#!/usr/bin/env python3
"""
linkedin_scraper — LinkedIn competitive scraper for synthetic offerings in market research.

Collects public LinkedIn content via search-engine indexes (never by logging
in to or crawling linkedin.com), plus news coverage and items you save
manually, then tags each item by competitor, signal type, and capability and
renders an HTML report with a 7/14/30/60/90-day period switcher.

Sources
  news     Google News RSS (no key needed)
  brave    Brave Search API     -> env BRAVE_API_KEY
  serpapi  SerpAPI Google search -> env SERPAPI_KEY
  tavily   Tavily search API     -> env TAVILY_API_KEY (free tier: 1,000 searches/month)
  arxiv    arXiv API, academic papers (no key needed)
  inbox    .txt/.md files in ./inbox (posts you copied from LinkedIn by hand)

Usage
  python3 linkedin_scraper.py collect [--sources news,brave,inbox] [--days 180]
  python3 linkedin_scraper.py report  [--summarize]
  python3 linkedin_scraper.py run     # collect + report

Standard library only. --summarize calls the Claude API (env ANTHROPIC_API_KEY).
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import html
import json
import math
import os
import re
import sqlite3
import ssl
import subprocess
import sys
import time
import tomllib
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from datetime import date, datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent
USER_AGENT = "linkedin-scraper/1.0 (competitive research; contact via repo owner)"
CLAUDE_MODEL = "claude-opus-5-5"
NEWS_CAP = 100  # Google News RSS returns at most ~100 items per query


# --------------------------------------------------------------------------
# Config & storage
# --------------------------------------------------------------------------

def load_config(path: Path) -> dict:
    with open(path, "rb") as f:
        cfg = tomllib.load(f)
    for c in cfg["competitors"]:
        c["_patterns"] = [_alias_pattern(a) for a in c["aliases"]]
        c.setdefault("exclude", [])
    cfg.setdefault("voices", [])
    for v in cfg["voices"]:
        v["_patterns"] = [_alias_pattern(a) for a in v.get("aliases", [v["name"]])]
    a = cfg.setdefault("academic", {})
    a.setdefault("terms", [])
    a.setdefault("arxiv_queries", [])
    a.setdefault("discovery_queries", [])
    # word-boundary match so e.g. "nber" doesn't fire inside "Canberra"
    a["_patterns"] = [re.compile(r"(?<![a-z])" + re.escape(t.lower()) + r"(?![a-z])") for t in a["terms"]]
    t = cfg["topics"]
    t.setdefault("specific", [])
    t.setdefault("generic", t.get("terms", []))  # older configs used a single "terms" list
    t.setdefault("qualifier", '("market research" OR insights OR survey)')
    s = cfg["settings"]
    s.setdefault("lookback_days", 180)
    s.setdefault("max_pages", 3)
    s.setdefault("report_periods", [7, 14, 30, 60, 90])
    s.setdefault("default_period", 30)
    return cfg


def _alias_pattern(alias: str) -> re.Pattern:
    # All-caps short aliases (NIQ, BASES) match case-sensitively to avoid
    # hitting ordinary words; everything else is case-insensitive.
    flags = 0 if alias.isupper() and len(alias) <= 5 else re.IGNORECASE
    return re.compile(r"(?<![\w-])" + re.escape(alias) + r"(?![\w-])", flags)


def open_db(path: Path) -> sqlite3.Connection:
    path.parent.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(path)
    db.row_factory = sqlite3.Row
    db.executescript("""
        CREATE TABLE IF NOT EXISTS items (
            id TEXT PRIMARY KEY,
            url TEXT, title TEXT, snippet TEXT,
            source TEXT, channel TEXT, url_type TEXT,
            published TEXT, first_seen TEXT, last_seen TEXT, query TEXT,
            competitors TEXT, signals TEXT, capabilities TEXT
        );
        CREATE TABLE IF NOT EXISTS runs (
            started TEXT PRIMARY KEY, sources TEXT, fetched INTEGER, new INTEGER
        );
        CREATE TABLE IF NOT EXISTS briefs (
            competitor TEXT PRIMARY KEY, created TEXT, body TEXT
        );
        CREATE TABLE IF NOT EXISTS observations (
            item_id TEXT, run TEXT, source TEXT, query TEXT, rank INTEGER,
            reactions INTEGER, comments INTEGER, reposts INTEGER
        );
        CREATE INDEX IF NOT EXISTS obs_item ON observations(item_id);
        CREATE TABLE IF NOT EXISTS query_stats (
            run TEXT, source TEXT, query TEXT, results INTEGER, kept INTEGER,
            capped INTEGER, error TEXT
        );
    """)
    cols = {r[1] for r in db.execute("PRAGMA table_info(runs)")}
    if "lookback" not in cols:
        db.execute("ALTER TABLE runs ADD COLUMN lookback INTEGER")
    if "author" not in {r[1] for r in db.execute("PRAGMA table_info(items)")}:
        db.execute("ALTER TABLE items ADD COLUMN author TEXT DEFAULT ''")
    return db


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def today() -> date:
    return datetime.now(timezone.utc).date()


def norm_date(s: str) -> str:
    """Best-effort conversion of the many date formats sources return to YYYY-MM-DD."""
    s = (s or "").strip()
    if not s:
        return ""
    if re.match(r"^\d{4}-\d{2}-\d{2}", s):
        return s[:10]
    m = re.match(r"(\d+)\s+(minute|hour|day|week|month|year)s?\s+ago", s, re.IGNORECASE)
    if m:
        n, unit = int(m.group(1)), m.group(2).lower()
        days = {"minute": 0, "hour": 0, "day": 1, "week": 7, "month": 30, "year": 365}[unit] * n
        return (today() - timedelta(days=days)).isoformat()
    for fmt in ("%b %d, %Y", "%B %d, %Y", "%d %b %Y", "%d %B %Y", "%m/%d/%Y"):
        try:
            return datetime.strptime(s, fmt).date().isoformat()
        except ValueError:
            pass
    try:
        return parsedate_to_datetime(s).date().isoformat()
    except (TypeError, ValueError):
        return ""


def linkedin_date(url: str) -> str:
    """LinkedIn post ids (activity/ugcPost/share) carry their creation time in the top 41 bits
    (milliseconds since the Unix epoch), so a post URL dates the post even when the search
    result doesn't."""
    m = re.search(r"(?:activity|ugcPost|share)[-:%3A]+(\d{18,20})", url or "")
    if not m:
        return ""
    try:
        d = datetime.fromtimestamp((int(m.group(1)) >> 22) / 1000, timezone.utc).date()
    except (OverflowError, OSError, ValueError):
        return ""
    return d.isoformat() if date(2015, 1, 1) <= d <= today() else ""


def item_date(it: dict) -> str:
    return norm_date(it.get("published", "")) or linkedin_date(it.get("url", "")) or it["first_seen"][:10]


# --------------------------------------------------------------------------
# HTTP helpers
# --------------------------------------------------------------------------

_USE_CURL = False  # flips on after the first cert failure; curl uses the OS trust store


def _is_cert_error(e: Exception) -> bool:
    return isinstance(getattr(e, "reason", e), ssl.SSLCertVerificationError)


def _curl(url: str, headers: dict, timeout: int, data: bytes | None = None) -> bytes:
    cmd = ["curl", "-sSfL", "--max-time", str(timeout)]
    for k, v in headers.items():
        cmd += ["-H", f"{k}: {v}"]
    if data is not None:
        cmd += ["-X", "POST", "--data-binary", "@-"]
    r = subprocess.run(cmd + [url], input=data, capture_output=True)
    if r.returncode:
        raise RuntimeError(f"curl exit {r.returncode}: {r.stderr.decode().strip()}")
    return r.stdout


def _request(url: str, headers: dict, timeout: int, data: bytes | None = None) -> bytes:
    global _USE_CURL
    headers = {"User-Agent": USER_AGENT, **headers}
    if not _USE_CURL:
        req = urllib.request.Request(url, data=data, headers=headers,
                                     method="POST" if data is not None else "GET")
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read()
        except Exception as e:
            if not _is_cert_error(e):
                raise
            _USE_CURL = True
    return _curl(url, headers, timeout, data)


def http_get(url: str, headers: dict | None = None, timeout: int = 20) -> bytes:
    return _request(url, headers or {}, timeout)


def http_post_json(url: str, payload: dict, headers: dict, timeout: int = 120) -> dict:
    body = _request(url, {"Content-Type": "application/json", **headers}, timeout,
                    json.dumps(payload).encode())
    return json.loads(body)


# --------------------------------------------------------------------------
# Engagement parsing
# --------------------------------------------------------------------------

_ENG = re.compile(r"(\d[\d,.]*\s*[KkMm]?)\+?\s*(reactions?|likes?|comments?|reposts?|shares?)\b", re.IGNORECASE)


def _num(s: str) -> int:
    s = s.strip().replace(",", "").replace(" ", "")
    mult = 1000 if s[-1:] in "Kk" else 1_000_000 if s[-1:] in "Mm" else 1
    try:
        return int(float(s.rstrip("KkMm")) * mult)
    except ValueError:
        return 0


def parse_engagement(*texts: str, max_from_text: int | None = None) -> dict:
    """Reaction / comment / repost counts as search engines show them for
    LinkedIn posts, e.g. "412 reactions · 58 comments" or "1.2K+ likes"."""
    out = {"reactions": 0, "comments": 0, "reposts": 0}
    for i, t in enumerate(texts):
        for n, kind in _ENG.findall(t or ""):
            k = kind.lower()
            key = "comments" if k.startswith("comment") else "reposts" if k.startswith(("repost", "share")) else "reactions"
            v = _num(n)
            # Text after the first argument (the title) is scraped page text, where adjacent
            # numbers run together; ignore implausibly large values from it.
            if max_from_text and i > 0 and v > max_from_text:
                continue
            out[key] = max(out[key], v)
    return out


# --------------------------------------------------------------------------
# Query building
# --------------------------------------------------------------------------

SYNTH_OR = ('(synthetic OR "digital twin" OR "digital twins" OR persona OR personas OR simulated '
            'OR simulation OR "AI respondents" OR "agentic twin")')
# Pure-play vendors do nothing but synthetic research, so requiring synthetic terms
# only loses coverage; a light AI/research qualifier keeps out unrelated uses of the name.
PUREPLAY_OR = "(AI OR research OR insights OR startup OR raises OR launches OR synthetic OR twin OR persona OR simulated)"
# Search engines return noticeably different results for differently worded but
# equivalent queries, so incumbents get a second, narrower wording too.
SYNTH_ALT = '(synthetic OR "digital twin" OR simulated) (respondents OR data OR personas OR audience OR consumers)'


def _alias_terms(cfg: dict) -> list[tuple[str, str]]:
    # Every alias is searched, so product names (PersonaBot, HarmonAIze, …)
    # surface items that never mention the parent company.
    seen, out = set(), []
    for c in cfg["competitors"]:
        for a in [c["name"], *c["aliases"]]:
            if a.lower() not in seen:
                seen.add(a.lower())
                out.append((a, c.get("segment", "")))
    return out


def topic_queries(cfg: dict) -> list[str]:
    t = cfg["topics"]
    return [f'"{s}"' for s in t["specific"]] + [f'"{g}" {t["qualifier"]}' for g in t["generic"]]


def competitor_queries(cfg: dict) -> list[str]:
    qs = []
    for a, seg in _alias_terms(cfg):
        qs.append(f'"{a}" {PUREPLAY_OR if seg == "pure-play" else SYNTH_OR}')
        qs.append(f'"{a}" {SYNTH_ALT}')
    return qs


def voice_queries(cfg: dict) -> list[str]:
    return [f'"{v["name"]}" {SYNTH_OR}' for v in cfg["voices"]]


def linkedin_queries(cfg: dict) -> list[str]:
    qs = [f"site:linkedin.com {q}" for q in competitor_queries(cfg) + voice_queries(cfg)]
    for q in topic_queries(cfg):
        qs.append(f"site:linkedin.com/posts {q}")
        qs.append(f"site:linkedin.com/pulse {q}")
    return qs


def news_queries(cfg: dict) -> list[str]:
    return (competitor_queries(cfg) + topic_queries(cfg) + voice_queries(cfg)
            + cfg["academic"]["discovery_queries"])


# --------------------------------------------------------------------------
# Collectors — each yields dicts: url, title, snippet, published, query, source
# and appends one {source, query, results, capped, error} record per query to `stats`.
# --------------------------------------------------------------------------

def _news_fetch(q: str, start: date, end: date, delay: float, depth: int = 0):
    """Fetch with Google's own lookback; split into date windows only if the result cap is hit.
    (Windowed queries return fewer items than a single lookback query when under the cap.)"""
    if depth == 0:
        full = f"{q} when:{(end - start).days}d"
    else:
        full = f"{q} after:{(start - timedelta(days=1)).isoformat()} before:{(end + timedelta(days=1)).isoformat()}"
    url = "https://news.google.com/rss/search?" + urllib.parse.urlencode(
        {"q": full, "hl": "en-US", "gl": "US", "ceid": "US:en"})
    root = ET.fromstring(http_get(url))
    time.sleep(delay)
    items = list(root.iter("item"))
    if len(items) >= NEWS_CAP and (end - start).days > 7 and depth < 4:
        mid = start + (end - start) / 2
        a, cap_a = _news_fetch(q, start, mid, delay, depth + 1)
        b, cap_b = _news_fetch(q, mid + timedelta(days=1), end, delay, depth + 1)
        return a + b, cap_a or cap_b
    return items, len(items) >= NEWS_CAP


def collect_news(cfg: dict, days: int, stats: list):
    end, start = today(), today() - timedelta(days=days)
    for q in news_queries(cfg):
        try:
            entries, capped = _news_fetch(q, start, end, cfg["settings"]["request_delay_seconds"])
        except Exception as e:
            print(f"  ! news query failed ({e}): {q}", file=sys.stderr)
            stats.append({"source": "news", "query": q, "results": 0, "capped": False, "error": str(e)[:200]})
            continue
        stats.append({"source": "news", "query": q, "results": len(entries), "capped": capped, "error": ""})
        for rank, it in enumerate(entries, 1):
            pub = it.findtext("pubDate")
            try:
                pub = parsedate_to_datetime(pub).date().isoformat() if pub else ""
            except (TypeError, ValueError):
                pass
            desc = re.sub(r"<[^>]+>", " ", it.findtext("description") or "")
            yield {
                "url": it.findtext("link") or "",
                "title": it.findtext("title") or "",
                "snippet": html.unescape(re.sub(r"\s+", " ", desc)).strip(),
                "published": pub or "",
                "rank": rank,
                "query": q, "source": "news",
            }


def collect_brave(cfg: dict, days: int, stats: list):
    key = os.environ.get("BRAVE_API_KEY")
    if not key:
        print("  - skipping brave: BRAVE_API_KEY not set", file=sys.stderr)
        return
    s = cfg["settings"]
    freshness = f"{(today() - timedelta(days=days)).isoformat()}to{today().isoformat()}"
    count = min(s["max_results_per_query"], 20)
    for q in linkedin_queries(cfg):
        n, capped, err = 0, False, ""
        for page in range(s["max_pages"]):
            params = {"q": q, "count": count, "offset": page, "freshness": freshness}
            url = "https://api.search.brave.com/res/v1/web/search?" + urllib.parse.urlencode(params)
            try:
                data = json.loads(http_get(url, {"X-Subscription-Token": key, "Accept": "application/json"}))
            except Exception as e:
                print(f"  ! brave query failed ({e}): {q}", file=sys.stderr)
                err = str(e)[:200]
                break
            results = data.get("web", {}).get("results", [])
            n += len(results)
            for idx, r in enumerate(results, 1):
                desc = re.sub(r"<[^>]+>", "", r.get("description", ""))
                extra = " ".join(r.get("extra_snippets") or [])
                yield {
                    "url": r.get("url", ""),
                    "title": r.get("title", ""),
                    "snippet": desc,
                    "published": r.get("page_age") or r.get("age") or "",
                    "rank": page * count + idx,
                    "engagement": parse_engagement(r.get("title", ""), desc, extra),
                    "query": q, "source": "brave",
                }
            time.sleep(s["request_delay_seconds"])
            more = data.get("query", {}).get("more_results_available", False)
            if not more:
                break
            capped = page == s["max_pages"] - 1
        stats.append({"source": "brave", "query": q, "results": n, "capped": capped, "error": err})


def collect_serpapi(cfg: dict, days: int, stats: list):
    key = os.environ.get("SERPAPI_KEY")
    if not key:
        print("  - skipping serpapi: SERPAPI_KEY not set", file=sys.stderr)
        return
    s = cfg["settings"]
    fmt = lambda d: f"{d.month}/{d.day}/{d.year}"
    tbs = f"cdr:1,cd_min:{fmt(today() - timedelta(days=days))},cd_max:{fmt(today())}"
    for q in linkedin_queries(cfg):
        n, capped, err = 0, False, ""
        for page in range(s["max_pages"]):
            params = {"engine": "google", "q": q, "api_key": key, "tbs": tbs, "start": page * 10}
            try:
                data = json.loads(http_get("https://serpapi.com/search.json?" + urllib.parse.urlencode(params)))
            except Exception as e:
                print(f"  ! serpapi query failed ({e}): {q}", file=sys.stderr)
                err = str(e)[:200]
                break
            results = data.get("organic_results", [])
            n += len(results)
            for idx, r in enumerate(results, 1):
                yield {
                    "url": r.get("link", ""),
                    "title": r.get("title", ""),
                    "snippet": r.get("snippet", ""),
                    "published": r.get("date", ""),
                    "rank": r.get("position") or page * 10 + idx,
                    # Google puts LinkedIn reaction/comment counts in rich snippets / extensions
                    "engagement": parse_engagement(r.get("title", ""), r.get("snippet", ""),
                                                   json.dumps(r.get("rich_snippet", {})),
                                                   " ".join(map(str, r.get("extensions", [])))),
                    "query": q, "source": "serpapi",
                }
            time.sleep(s["request_delay_seconds"])
            if not data.get("serpapi_pagination", {}).get("next"):
                break
            capped = page == s["max_pages"] - 1
        stats.append({"source": "serpapi", "query": q, "results": n, "capped": capped, "error": err})


def tavily_queries(cfg: dict) -> list[str]:
    # Tavily is a relevance-ranked search (OR/site: operators aren't needed; the domain is
    # filtered with include_domains). One query per competitor, product name, topic and voice
    # keeps a weekly run around 60-90 searches, inside the free 1,000 a month.
    qs = [f'"{c["name"]}" synthetic respondents digital twins AI personas' for c in cfg["competitors"]]
    names = {c["name"].lower() for c in cfg["competitors"]}
    for c in cfg["competitors"]:
        for a in c["aliases"]:
            # product names (PersonaBot, HarmonAIze, ...): long enough to be specific, not the company itself
            squash = lambda x: re.sub(r"[^a-z0-9]", "", x.lower())   # "Brox.ai" == "Brox AI"
            if (a.lower() not in names and len(a) > 5 and not a.isupper()
                    and squash(c["name"]) not in squash(a) and squash(a) not in squash(c["name"])):
                qs.append(f'"{a}" {c["name"]} synthetic')
    qs += [f'"{t}" market research' for t in cfg["topics"]["specific"] + cfg["topics"]["generic"]]
    qs += [f'"{v["name"]}" synthetic research' for v in cfg["voices"]]
    return list(dict.fromkeys(qs))


def _tavily_search(q: str, base: dict, key: str, delay: float) -> tuple[list, str]:
    """One search, retried once when it comes back empty or fails (Tavily occasionally returns
    nothing for a query that has results moments later)."""
    err = ""
    for attempt in range(2):
        try:
            data = http_post_json("https://api.tavily.com/search", {"query": q, **base},
                                  {"Authorization": f"Bearer {key}"}, timeout=40)
            results = data.get("results", [])
            if results:
                return results, ""
            err = ""
        except Exception as e:
            err = str(e)[:200]
        time.sleep(delay * 2)
    return [], err


def collect_tavily(cfg: dict, days: int, stats: list):
    key = os.environ.get("TAVILY_API_KEY")
    if not key:
        print("  - skipping tavily: TAVILY_API_KEY not set", file=sys.stderr)
        return
    t = cfg.get("tavily", {})
    delay = cfg["settings"]["request_delay_seconds"]
    base = {"search_depth": t.get("search_depth", "basic"), "max_results": min(int(t.get("max_results", 20)), 20),
            "include_domains": t.get("include_domains", ["linkedin.com"]), "include_raw_content": False}
    # No date filter: Tavily rarely knows when a LinkedIn page was published, so date filters
    # silently drop most LinkedIn results. Posts are dated from their URL instead (linkedin_date).
    variants = t.get("capped_variants", [])
    queue = [(q, q) for q in tavily_queries(cfg)]
    while queue:
        q, parent = queue.pop(0)
        results, err = _tavily_search(q, base, key, delay)
        if err:
            print(f"  ! tavily query failed ({err}): {q}", file=sys.stderr)
        for rank, r in enumerate(results, 1):
            content = re.sub(r"\s+", " ", r.get("content") or "").strip()
            yield {
                "url": r.get("url", ""),
                "title": r.get("title", ""),
                "snippet": content[:1200],
                "published": r.get("published_date") or "",
                "rank": rank,
                "engagement": parse_engagement(r.get("title", ""), content, max_from_text=2000),
                "query": q, "source": "tavily",
            }
        capped = len(results) >= base["max_results"]
        stats.append({"source": "tavily", "query": q, "results": len(results), "capped": capped, "error": err})
        # Tavily has no next page: a query that fills the limit is widened with variant phrasings.
        if capped and q == parent:
            queue[0:0] = [(f"{q} {v}", parent) for v in variants]
        time.sleep(delay)


ATOM = {"a": "http://www.w3.org/2005/Atom"}


def collect_arxiv(cfg: dict, days: int, stats: list):
    cutoff = (today() - timedelta(days=days)).isoformat()
    for q in cfg["academic"]["arxiv_queries"]:
        params = {"search_query": q, "sortBy": "submittedDate", "sortOrder": "descending", "max_results": 100}
        try:
            root = ET.fromstring(http_get("https://export.arxiv.org/api/query?" + urllib.parse.urlencode(params), timeout=40))
        except Exception as e:
            print(f"  ! arxiv query failed ({e}): {q}", file=sys.stderr)
            stats.append({"source": "arxiv", "query": q, "results": 0, "capped": False, "error": str(e)[:200]})
            continue
        n = 0
        entries = root.findall("a:entry", ATOM)
        for rank, e in enumerate(entries, 1):
            pub = (e.findtext("a:published", namespaces=ATOM) or "")[:10]
            if pub < cutoff:
                break  # sorted newest first
            n += 1
            authors = [a.findtext("a:name", namespaces=ATOM) for a in e.findall("a:author", ATOM)]
            yield {
                "url": (e.findtext("a:id", namespaces=ATOM) or "").replace("http://", "https://"),
                "title": re.sub(r"\s+", " ", e.findtext("a:title", namespaces=ATOM) or "").strip(),
                "snippet": re.sub(r"\s+", " ", e.findtext("a:summary", namespaces=ATOM) or "").strip()[:1200],
                "published": pub,
                "author": ", ".join(authors[:3]) + (" et al." if len(authors) > 3 else ""),
                "rank": rank,
                "query": q, "source": "arxiv",
            }
        stats.append({"source": "arxiv", "query": q, "results": n, "capped": n == len(entries) == 100, "error": ""})
        time.sleep(3)  # arXiv asks for >= 3 s between API calls


def collect_inbox(cfg: dict, days: int, stats: list):
    """Posts saved by hand. Optional header lines, then a blank line, then text:
        url: https://www.linkedin.com/posts/...
        author: Jane Doe, Evidenza
        date: 2026-10-01
        reactions: 412        (optional: counts you saw on the post)
        comments: 58
        reposts: 12
    Files starting with "_" are ignored (see inbox/_TEMPLATE.txt).
    """
    inbox = ROOT / "inbox"
    inbox.mkdir(exist_ok=True)
    n = 0
    for f in sorted(p for p in inbox.iterdir() if p.suffix in (".txt", ".md") and not p.name.startswith("_")):
        text = f.read_text(errors="replace")
        meta, body = {}, text
        head, sep, rest = text.partition("\n\n")
        if sep and all(re.match(r"^\w+:\s", ln) for ln in head.strip().splitlines()):
            meta = dict(ln.split(":", 1) for ln in head.strip().splitlines())
            meta = {k.strip().lower(): v.strip() for k, v in meta.items()}
            body = rest
        body = re.sub(r"\s+", " ", body).strip()
        title = meta.get("author") or f.stem
        n += 1
        yield {
            "url": meta.get("url") or f"file://{f.name}",
            "title": title,
            "snippet": body[:2000],
            "published": meta.get("date", ""),
            "author": (meta.get("author") or "").split(",")[0].strip(),
            "engagement": {k: _num(meta.get(k, "0") or "0") for k in ("reactions", "comments", "reposts")}
                          | ({"reactions": _num(meta["likes"])} if meta.get("likes") else {}),
            "query": "manual", "source": "inbox",
        }
    stats.append({"source": "inbox", "query": "manual", "results": n, "capped": False, "error": ""})


COLLECTORS = {"news": collect_news, "brave": collect_brave, "serpapi": collect_serpapi, "tavily": collect_tavily,
              "arxiv": collect_arxiv, "inbox": collect_inbox}


# --------------------------------------------------------------------------
# Classification
# --------------------------------------------------------------------------

def url_type(url: str) -> tuple[str, str]:
    u = url.lower()
    if "arxiv.org" in u:
        return "academic", "paper"
    if "linkedin.com" not in u:
        return ("news" if u.startswith("http") else "manual"), "other"
    for frag, kind in (("/posts/", "post"), ("/feed/update", "post"), ("/pulse/", "article"),
                       ("/company/", "company page"), ("/jobs/", "job"), ("/events/", "event"),
                       ("/in/", "profile")):
        if frag in u:
            return "linkedin", kind
    return "linkedin", "other"


def classify(item: dict, cfg: dict) -> dict:
    text = f'{item["title"]} {item["snippet"]}'
    low = text.lower()
    comps = [c["name"] for c in cfg["competitors"] if any(p.search(text) for p in c["_patterns"])
             and not any(x in low for x in c["exclude"])]
    sigs = [k for k, kws in cfg["signals"].items() if any(kw in low for kw in kws)]
    if item.get("source") == "arxiv":
        sigs = [x for x in sigs if x in ("Validation claim", "Skepticism / risk")]
    if "Leadership change" in sigs and "Product launch" in sigs and not re.search(r"launch|unveil|introduc", low):
        sigs.remove("Product launch")
    caps = [k for k, kws in cfg["capabilities"].items() if any(kw in low for kw in kws)]
    voices = [v["name"] for v in cfg["voices"] if any(p.search(text) for p in v["_patterns"])]
    channel, kind = url_type(item["url"])
    if item["source"] == "inbox":
        channel = "linkedin" if "linkedin.com" in item["url"] else "manual"
    author = item.get("author") or extract_author(item, channel)
    if author and item["source"] != "arxiv" and not _is_person(author, cfg):
        author = ""
    url = item["url"].lower()
    academic = (item["source"] == "arxiv" or any(p.search(low) or p.search(url) for p in cfg["academic"]["_patterns"])
                or (not comps and any(v["kind"] == "academic" for v in cfg["voices"] if v["name"] in voices)))
    if academic:
        source_kind = "Academic"
    elif voices or (channel == "linkedin" and author and not comps):
        source_kind = "Industry voice"
    elif comps:
        source_kind = "Vendor"
    else:
        source_kind = "Other"
    return {**item, "published": norm_date(item["published"]) or item["published"],
            "competitors": comps, "signals": sigs, "capabilities": caps,
            "voices": voices, "author": author, "kind": source_kind,
            "channel": channel, "url_type": kind}


_PERSON = r"[A-Z][a-zA-Z'\-]+(?:\s+[A-Z]\.)?(?:\s+[A-Z][a-zA-Z'\-]+){1,2}"
_PERSON_INITIAL = r"[A-Z][a-zA-Z'\-]+\s+[A-Z]\."      # "Netali J." (LinkedIn's shortened names)
# Headline words that look like names in "X Y: headline" patterns but aren't.
_NOT_PERSON = set("""the a an artificial intelligence synthetic users data research insights market markets
digital modern milestones early scale explained ai new report study survey guide why how what top best
future state trends weekly daily news update inside exclusive opinion podcast webinar interview analysis
review case week year big small smart human humans consumer consumers brand brands customer customers
agents agent twin twins persona personas panel panels global industry tech technology innovation
breaking watch live first last part chapter episode season""".split())


def _is_person(name: str, cfg: dict) -> bool:
    words = name.lower().replace(".", "").split()
    if any(w in _NOT_PERSON for w in words):
        return False
    aliases = {a.lower() for c in cfg["competitors"] for a in [c["name"], *c["aliases"]]}
    return name.lower() not in aliases


def extract_author(item: dict, channel: str) -> str:
    """Who is speaking: LinkedIn post/article author from the result title, or a
    professor/researcher named in a news headline or snippet."""
    title = item.get("title", "")
    if channel == "linkedin":
        for pat in (rf"^({_PERSON}) on LinkedIn:", rf"^({_PERSON})'s Post",
                    rf"\|\s*({_PERSON}) posted on the topic",                       # "... | Olivia Wang posted on the topic | LinkedIn"
                    rf"\|\s*({_PERSON})\s*(?:\.\.\.|…)?\s*(?:\|\s*[\d,.]+[KkMm]?\+?\s*comments?\s*)?$",  # "... | Peter Weinberg ..." / "| Mark Ritson | 393 comments"
                    rf"^({_PERSON})\s*\|\s*[\d,.]+\s*comments?",                # "Byron Sharp | 34 comments"
                    rf"^({_PERSON}|{_PERSON_INITIAL})\s+[-–]\s+"):              # "Netali J. - Market research today"
            m = re.search(pat, title)
            if m:
                return m.group(1)
        # The post URL starts with the poster's profile name: /posts/netali-jakubovitz_...
        m = re.search(r"linkedin\.com/posts/([a-z][a-z\-]+?)(?:-[a-z0-9]*\d[a-z0-9]*)?_", item.get("url", ""))
        if m and "-" in m.group(1):
            words = [w for w in m.group(1).split("-") if w and w not in ("com", "inc", "llc", "ltd", "official", "hq")]
            if 2 <= len(words) <= 4:
                return " ".join(w.capitalize() for w in words)
    # Columns and webinar write-ups: "Mark Ritson: …", "…: Vijay Raj at MRSI webinar"
    m = re.match(rf"({_PERSON}):\s", title) or re.search(rf"[:,]\s+({_PERSON})\s+at\s+[A-Z]", title)
    if m:
        return m.group(1)
    text = f"{title} {item.get('snippet', '')}"
    m = re.search(rf"(?:Professor|Prof\.|Dr\.)\s+({_PERSON})", text) or \
        re.search(rf"({_PERSON}),\s+(?:an?\s+)?(?:associate |assistant )?(?:professor|researcher|lecturer|economist)", text)
    return m.group(1) if m else ""


_SYNTH_TOPIC = re.compile(
    r"synthetic|digital twin|silicon sampl|silicon subject|homo silicus|persona|simulat|virtual audience"
    r"|ai respondent|llm respondent|ai[- ]generated respond|replace (?:human|real) (?:survey )?respond"
    r"|without (?:people|humans|respondents)|ai (?:survey|panel)s?\b|llms? (?:as|replace|simulate)", re.I)


def _about_synthetic(item: dict) -> bool:
    """LinkedIn page text often includes comments and sidebars, so one passing mention of
    "synthetic" (e.g. in a comment) isn't enough: the topic must be in the post's title, or come up
    at least twice in its text."""
    return bool(_SYNTH_TOPIC.search(item["title"])) or len(_SYNTH_TOPIC.findall(item.get("snippet", ""))) >= 2


def is_relevant(item: dict, cfg: dict) -> bool:
    # Keep anything naming a tracked competitor; otherwise require a synthetic
    # capability *and* a market-research context term.
    low = f'{item["title"]} {item["snippet"]}'.lower()
    rel = cfg.get("relevance", {})
    if any(t in low for t in rel.get("exclude_terms", [])):
        return False
    if item.get("channel") == "linkedin" and (item.get("url_type") == "profile" or "/top-content/" in item["url"]):
        # Personal profile pages and LinkedIn's SEO "top content" pages aren't posts; skip them.
        return False
    if item["source"] == "arxiv":
        # arXiv queries are broad ("survey" also means literature review there)
        return any(t in low for t in cfg["academic"].get("relevance_terms", [])) or bool(item["competitors"])
    if item["competitors"]:
        return True
    if item["source"] == "tavily" and not _about_synthetic(item):
        return False
    synthetic = bool(item["capabilities"]) or bool(
        re.search(r"synthetic|digital twin|silicon sampl|silicon subject|homo silicus|persona|simulat", low))
    if item.get("voices") and synthetic:
        return True
    ctx = rel.get("context_terms", [])
    return bool(item["capabilities"]) and (not ctx or any(t in low for t in ctx))


def item_id(url: str, title: str) -> str:
    # LinkedIn URLs carry tracking params; strip the query for de-duplication.
    base = url.split("?")[0].rstrip("/") if "linkedin.com" in url else url
    return hashlib.sha1((base or title).encode()).hexdigest()[:16]


# --------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------

def cmd_collect(cfg: dict, db: sqlite3.Connection, sources: list[str], days: int) -> None:
    started = now_iso()
    fetched = new = 0
    stats: list[dict] = []
    kept = Counter()
    for name in sources:
        print(f"Collecting from {name}…")
        for raw in COLLECTORS[name](cfg, days, stats):
            if not raw["url"] and not raw["title"]:
                continue
            it = classify(raw, cfg)
            if not is_relevant(it, cfg):
                continue
            fetched += 1
            kept[(it["source"], it["query"])] += 1
            iid = item_id(it["url"], it["title"])
            eng = raw.get("engagement") or {}
            db.execute("INSERT INTO observations VALUES (?,?,?,?,?,?,?,?)",
                       (iid, started, it["source"], it["query"], raw.get("rank"),
                        eng.get("reactions", 0), eng.get("comments", 0), eng.get("reposts", 0)))
            exists = db.execute("SELECT 1 FROM items WHERE id=?", (iid,)).fetchone()
            if exists:
                db.execute("UPDATE items SET last_seen=? WHERE id=?", (started, iid))
                continue
            new += 1
            db.execute(
                "INSERT INTO items (id, url, title, snippet, source, channel, url_type, published, first_seen,"
                " last_seen, query, competitors, signals, capabilities, author) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (iid, it["url"], it["title"], it["snippet"], it["source"], it["channel"],
                 it["url_type"], it["published"], started, started, it["query"],
                 json.dumps(it["competitors"]), json.dumps(it["signals"]),
                 json.dumps(it["capabilities"]), it["author"]))
        db.commit()
    db.executemany("INSERT INTO query_stats VALUES (?,?,?,?,?,?,?)", [
        (started, st["source"], st["query"], st["results"], kept[(st["source"], st["query"])],
         int(st["capped"]), st["error"]) for st in stats])
    db.execute("INSERT OR REPLACE INTO runs (started, sources, fetched, new, lookback) VALUES (?,?,?,?,?)",
               (started, ",".join(sources), fetched, new, days))
    db.commit()
    capped = sum(1 for st in stats if st["capped"])
    print(f"Done: {fetched} relevant results, {new} new, {len(stats)} queries"
          + (f", {capped} hit the result cap" if capped else "") + ".")


def load_items(db: sqlite3.Connection, days: int, cfg: dict | None = None) -> list[dict]:
    """Items dated within `days`. With cfg, tags are recomputed so edits to
    config.toml apply to everything already collected."""
    cutoff = (today() - timedelta(days=days)).isoformat()
    out = []
    for r in db.execute("SELECT * FROM items"):
        d = dict(r)
        for k in ("competitors", "signals", "capabilities"):
            d[k] = json.loads(d[k])
        d["author"] = d.get("author") or ""
        if cfg:
            d = {**d, **{k: v for k, v in classify(d, cfg).items()
                         if k in ("competitors", "signals", "capabilities", "voices", "author", "kind", "channel", "url_type")}}
            if not is_relevant(d, cfg):
                continue
        d["date"] = item_date(d)
        d["dated"] = bool(norm_date(d.get("published", "")) or linkedin_date(d.get("url", "")))
        if d["date"] >= cutoff:
            out.append(d)
    out.sort(key=lambda d: (d["date"], d["first_seen"]), reverse=True)
    return out


def _claude(prompt: str, key: str) -> str:
    resp = http_post_json(
        "https://api.anthropic.com/v1/messages",
        {"model": CLAUDE_MODEL, "max_tokens": 1024,
         "messages": [{"role": "user", "content": prompt}]},
        {"x-api-key": key, "anthropic-version": "2023-06-01"})
    return "".join(b.get("text", "") for b in resp.get("content", []))


def summarize(cfg: dict, db: sqlite3.Connection, items: list[dict]) -> None:
    key = os.environ.get("ANTHROPIC_API_KEY")
    if not key:
        print("  - skipping summaries: ANTHROPIC_API_KEY not set", file=sys.stderr)
        return
    by_comp = defaultdict(list)
    for it in items:
        for c in it["competitors"]:
            by_comp[c].append(it)
    for comp, its in sorted(by_comp.items(), key=lambda kv: -len(kv[1])):
        if len(its) < 2:
            continue
        evidence = "\n".join(
            f'- [{i["published"] or "undated"}] ({i["channel"]}/{i["url_type"]}) {i["title"]} — {i["snippet"][:400]}'
            for i in its[:40])
        prompt = (
            f"You are a competitive-intelligence analyst covering synthetic data, synthetic "
            f"respondents, and digital-twin offerings in the market research industry.\n\n"
            f"Below are public LinkedIn and news snippets mentioning {comp}. Write a brief "
            f"(max 180 words) with these headed sections: Offering, Positioning & claims, "
            f"Recent moves, Watch-outs. Only state what the evidence supports; flag "
            f"uncertainty explicitly and never invent metrics, customers, or quotes.\n\n"
            f"Evidence:\n{evidence}")
        print(f"  summarizing {comp} ({len(its)} items)…")
        try:
            body = _claude(prompt, key)
        except Exception as e:
            print(f"  ! summary failed for {comp}: {e}", file=sys.stderr)
            continue
        db.execute("INSERT OR REPLACE INTO briefs VALUES (?,?,?)", (comp, now_iso(), body))
        db.commit()


def summarize_trends(cfg: dict, db: sqlite3.Connection, all_items: list[dict]) -> None:
    """One market-wide 'recent trends' narrative per report period."""
    key = os.environ.get("ANTHROPIC_API_KEY")
    if not key:
        return
    for p in cfg["settings"]["report_periods"]:
        cur, prev = split_periods(all_items, p)
        if len(cur) < 3:
            continue
        t = trend_stats(cur, prev)
        counts = (f"This period: {len(cur)} items; prior {p} days: {len(prev)} items.\n"
                  f"Competitor mentions (this vs prior): "
                  + ", ".join(f"{c} {n} vs {t['comp_prev'].get(c, 0)}" for c, n in t["comp_cur"].most_common(12))
                  + "\nSignals: " + ", ".join(f"{k} {v}" for k, v in t["sig_cur"].most_common())
                  + "\nCapabilities: " + ", ".join(f"{k} {v}" for k, v in t["cap_cur"].most_common()))
        evidence = "\n".join(
            f'- [{i["date"]}] {i.get("kind", "")} | {", ".join(i["competitors"] + i.get("voices", [])) or "—"} | {", ".join(i["signals"]) or "—"} | {i["title"]}'
            for i in cur[:80])
        prompt = (
            f"You are a competitive-intelligence analyst at Qualtrics covering synthetic "
            f"respondents, synthetic data and digital twins in market research.\n\n"
            f"Summarize recent trends for the last {p} days from the evidence below. Format: "
            f"3–5 short bullets on what changed or stood out (name competitors, industry voices and "
            f"notable academic work; compare with the "
            f"prior period where the counts support it), then one line starting 'Implication:' "
            f"on what it means for Qualtrics. Max 150 words. Only state what the evidence "
            f"supports; never invent metrics, customers or quotes. Note when evidence is thin.\n\n"
            f"{counts}\n\nHeadlines:\n{evidence}")
        print(f"  summarizing trends for last {p} days…")
        try:
            body = _claude(prompt, key)
        except Exception as e:
            print(f"  ! trend summary failed ({p}d): {e}", file=sys.stderr)
            continue
        db.execute("INSERT OR REPLACE INTO briefs VALUES (?,?,?)", (f"_trends:{p}", now_iso(), body))
        db.commit()


def write_csv(path: Path, items: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    cols = ["date", "first_seen", "published", "channel", "url_type", "kind", "competitors", "voices",
            "author", "signals", "capabilities", "title", "snippet", "url", "source", "query",
            "score", "reactions", "comments", "reposts", "best_rank", "searches", "runs"]
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(cols)
        for it in items:
            a = it.get("att", {})
            it = {**it, "reactions": a.get("reactions", 0), "comments": a.get("comments", 0),
                  "reposts": a.get("reposts", 0), "best_rank": a.get("best_rank") or "",
                  "searches": a.get("queries", ""), "runs": a.get("runs", "")}
            w.writerow(["; ".join(it.get(c, [])) if isinstance(it.get(c), list) else it.get(c, "") for c in cols])


def cmd_report(cfg: dict, db: sqlite3.Connection, do_summary: bool) -> None:
    s = cfg["settings"]
    periods = s["report_periods"]
    longest = max(periods)
    all_items = load_items(db, 2 * longest, cfg)  # includes the prior window for comparisons
    load_attention(db, all_items)
    shown = [i for i in all_items if i["date"] >= (today() - timedelta(days=longest)).isoformat()]
    if do_summary:
        summarize(cfg, db, shown)
        summarize_trends(cfg, db, all_items)
    briefs = {r["competitor"]: r for r in db.execute("SELECT * FROM briefs")}
    last = db.execute("SELECT * FROM runs ORDER BY started DESC LIMIT 1").fetchone()
    stats = [dict(r) for r in db.execute("SELECT * FROM query_stats WHERE run=?", (last["started"],))] if last else []
    earliest = db.execute("SELECT MIN(COALESCE(NULLIF(published,''), substr(first_seen,1,10))) FROM items").fetchone()[0]
    first_run = db.execute("SELECT MIN(started) FROM runs").fetchone()[0]
    write_csv(ROOT / s["csv_path"], shown)
    out = ROOT / s["report_path"]
    out.parent.mkdir(parents=True, exist_ok=True)
    page = render_html(cfg, all_items, briefs, dict(last) if last else None, stats, earliest, first_run)
    out.write_text(page)
    # Same report without the document skeleton, for publishing as a hosted page
    # (the host adds its own <!doctype>/<head>/<body>).
    hosted = ROOT / s.get("hosted_report_path", "reports/linkedin_synthetic_mr_hosted.html")
    hosted.write_text(hosted_fragment(page))
    print(f"Report: {out}\nHosted: {hosted}\nCSV:    {ROOT / s['csv_path']}  ({len(shown)} items, last {longest} days)")


def hosted_fragment(page: str) -> str:
    head = re.search(r"<head>(.*?)</head>", page, re.S).group(1)
    head = re.sub(r"<meta[^>]*>\s*", "", head)
    body = re.search(r"<body>(.*)</body>", page, re.S).group(1)
    return head.strip() + "\n" + body.strip() + "\n"


# --------------------------------------------------------------------------
# Attention: which items are rising to the top
# --------------------------------------------------------------------------

def load_attention(db: sqlite3.Connection, items: list[dict]) -> None:
    """Attach an `att` dict and `score` to each item from its search sightings."""
    obs = defaultdict(list)
    for r in db.execute("SELECT * FROM observations ORDER BY run"):
        obs[r["item_id"]].append(dict(r))
    for it in items:
        o = obs.get(it["id"], [])
        ranks = [x["rank"] for x in o if x["rank"]]
        by_run = defaultdict(lambda: {"reactions": 0, "comments": 0, "reposts": 0})
        for x in o:
            for k in ("reactions", "comments", "reposts"):
                by_run[x["run"]][k] = max(by_run[x["run"]][k], x[k] or 0)
        runs = sorted(by_run)
        latest = by_run[runs[-1]] if runs else {"reactions": 0, "comments": 0, "reposts": 0}
        # growth since the previous run that had any counts
        growth, since = 0, ""
        with_counts = [r for r in runs if sum(by_run[r].values())]
        if len(with_counts) >= 2:
            a, b = by_run[with_counts[-2]], by_run[with_counts[-1]]
            growth = (b["reactions"] + 3 * b["comments"] + 2 * b["reposts"]) - (a["reactions"] + 3 * a["comments"] + 2 * a["reposts"])
            since = with_counts[-2][:10]
        it["att"] = {
            **latest,
            "best_rank": min(ranks) if ranks else None,
            "queries": len({(x["source"], x["query"]) for x in o}) or 1,
            "runs": len(runs) or 1,
            "growth": growth, "since": since,
        }
        it["score"] = attention_score(it["att"])


def attention_score(a: dict, coverage: int = 1) -> float:
    # Comments count triple: they're discussion, which is what makes a post worth reading.
    eng = a["reactions"] + 3 * a["comments"] + 2 * a["reposts"]
    s = 12 * math.log10(1 + eng)
    if a["best_rank"]:
        s += max(0, 11 - a["best_rank"])          # top-10 placement in a search
    s += 2 * min(a["queries"], 5)                 # surfaced by many different searches
    s += 2 * min(a["runs"] - 1, 5)                # kept appearing run after run
    s += 5 * min(coverage - 1, 3)                 # same story covered by several sources
    if a["growth"] > 0:
        s += 6 * math.log10(1 + a["growth"])      # engagement climbing between runs
    return round(s, 1)


def _att_badges(a: dict, coverage: int = 1) -> str:
    b = []
    if a["comments"] or a["reactions"] or a["reposts"]:
        parts = [f"{a['comments']:,} comments" if a["comments"] else "",
                 f"{a['reactions']:,} reactions" if a["reactions"] else "",
                 f"{a['reposts']:,} reposts" if a["reposts"] else ""]
        b.append("<span class='badge eng'>" + " · ".join(x for x in parts if x) + "</span>")
    if a["growth"] > 0:
        b.append(f"<span class='badge up'>▲ rising since {html.escape(a['since'])}</span>")
    if a["best_rank"] and a["best_rank"] <= 3:
        b.append(f"<span class='badge'>#{a['best_rank']} in search</span>")
    if a["queries"] >= 3:
        b.append(f"<span class='badge'>{a['queries']} searches</span>")
    if a["runs"] >= 2:
        b.append(f"<span class='badge'>{a['runs']} runs</span>")
    if coverage > 1:
        b.append(f"<span class='badge'>{coverage} sources</span>")
    return "".join(b)


def _attention_section(cfg, p, cur, any_counts: bool = True) -> str:
    # Rank stories (merged coverage), led by their most-engaged item.
    stories = cluster_stories(cur)
    ranked = []
    for m in stories:
        lead = max(m, key=lambda i: i["score"])
        cov = len(m)
        ranked.append((attention_score(lead["att"], cov), lead, cov))
    ranked.sort(key=lambda x: -x[0])
    top_score = ranked[0][0] if ranked else 1

    def li(score, it, cov):
        who = f" · {html.escape(it['author'])}" if it.get("author") else ""
        bar = f"<span class='meter' style='--w:{max(4, round(100 * score / top_score))}%'></span>"
        return (f"<li><div class='vh'><div class='t'>{_link(it, _clean_title(it['title']))}</div>{bar}</div>"
                f"<div class='meta'>{_dlabel(it)} · {html.escape(it['channel'])}{who} "
                f"{_att_badges(it['att'], cov)}</div></li>")

    top_html = _more([li(*x) for x in ranked[:12]], 6, "moves rank", "<li class='mut'>No items this period.</li>")

    # Most discussed: comment counts, with a debate flag when comments are high relative to reactions.
    talk = sorted((i for i in cur if i["att"]["comments"]), key=lambda i: -i["att"]["comments"])[:10]
    def tli(it):
        a = it["att"]
        ratio = a["comments"] / a["reactions"] if a["reactions"] else 0
        debate = " <span class='badge hot'>debate</span>" if a["comments"] >= 10 and ratio >= 0.2 else ""
        return (f"<li><div class='t'>{_link(it, _clean_title(it['title']))}</div><div class='meta'>"
                f"{_dlabel(it)}{' · ' + html.escape(it['author']) if it.get('author') else ''} "
                f"{_att_badges(a)}{debate}</div></li>")
    has_counts = any(i["att"]["reactions"] or i["att"]["comments"] for i in cur)
    if talk:
        talk_html = _more([tli(i) for i in talk], 6, "moves")
    else:
        talk_html = ("<p class='mut'>No comment counts in this period. Counts come from LinkedIn search results "
                     "or from <code>comments:</code> / <code>reactions:</code> lines in inbox files.</p>")
    note = ("" if has_counts else
            "<p class='note'>No engagement counts yet, so this ranking uses search prominence, "
            "breadth, staying power and coverage only.</p>")
    explain = ("<p class='foot'>Score combines engagement shown in search results (comments weighted ×3), "
               "growth since the last run, top-3 search placement, how many searches return it, how many runs "
               "it's stayed in results, and how many sources cover the story.</p>")

    if not any_counts:
        # Nothing to rank by comments anywhere yet: one full-width panel instead of an empty second one.
        return f"""
{_h2("rising", "Rising to the top", p)}
<div class="panel"><div class="rank-head"><h3>Most worth reading</h3><span class="lbl">Attention score</span></div>{note}{top_html}
 {explain}
 <p class="foot"><b>Most discussed</b> (posts ranked by comment count, with debates flagged) appears here once
 reaction and comment counts come in. They come from LinkedIn search results, or from counts added to inbox files.</p></div>"""
    return f"""
{_h2("rising", "Rising to the top", p)}
<div class="cols cols-wide">
 <div class="panel"><div class="rank-head"><h3>Most worth reading</h3><span class="lbl">Attention score</span></div>{note}{top_html}</div>
 <div class="panel"><h3>Most discussed <small>· by comments</small></h3>{talk_html}</div>
</div>
{explain.replace("class='foot'", "class='foot foot-out'")}"""


# --------------------------------------------------------------------------
# Trend analysis
# --------------------------------------------------------------------------

KEY_SIGNALS = ["Product launch", "Partnership / M&A", "Funding", "Leadership change", "Validation claim"]
_STOP = set("the a an and or of for to in on with by at from as is are be its new how why what "
            "this that ai into over says say finds report research market".split())
_NOT_ORG = {"The", "New", "How", "Why", "What", "This", "AI", "It", "We", "Our", "Report", "Study",
            "Survey", "Research", "Exclusive", "Update", "Watch", "Breaking", "Today", "Week"}


def split_periods(items: list[dict], p: int) -> tuple[list[dict], list[dict]]:
    t0 = today()
    cur_start = (t0 - timedelta(days=p)).isoformat()
    prev_start = (t0 - timedelta(days=2 * p)).isoformat()
    cur = [i for i in items if i["date"] >= cur_start]
    prev = [i for i in items if prev_start <= i["date"] < cur_start]
    return cur, prev


NOT_ACTIVITY = ("company page", "job")   # pages that exist, not things a competitor did or said


def trend_stats(cur: list[dict], prev: list[dict]) -> dict:
    def cnt(items, key):
        return Counter(x for i in items if i.get("url_type") not in NOT_ACTIVITY for x in i[key])
    return {"comp_cur": cnt(cur, "competitors"), "comp_prev": cnt(prev, "competitors"),
            "sig_cur": cnt(cur, "signals"), "sig_prev": cnt(prev, "signals"),
            "cap_cur": cnt(cur, "capabilities"), "cap_prev": cnt(prev, "capabilities")}


def _clean_title(t: str) -> str:
    # Google News titles end with " - Publisher" (occasionally twice)
    t = re.sub(r"(\s+[-–|]\s+[^-–|]{2,60})\1$", r"\1", t.strip())
    return re.sub(r"\s+[-–|]\s+[^-–|]{2,60}$", "", t).strip()


def _tokens(t: str) -> set[str]:
    return {w for w in re.findall(r"[a-z0-9]+", _clean_title(t).lower()) if len(w) > 2 and w not in _STOP}


def _same_event(a: dict, b: dict) -> bool:
    # Differently worded headlines about one competitor's move a few days apart.
    if not a["competitors"] or set(a["competitors"]) != set(b["competitors"]):
        return False
    if not set(a["signals"]) & set(b["signals"]) & set(KEY_SIGNALS):
        return False
    da, db_ = date.fromisoformat(a["date"]), date.fromisoformat(b["date"])
    return abs((da - db_).days) <= 5


def cluster_stories(items: list[dict], threshold: float = 0.4) -> list[list[dict]]:
    """Group items that are the same story covered by several outlets / posts."""
    clusters: list[tuple[set[str], list[dict]]] = []
    for it in items:
        tk = _tokens(it["title"])
        for ctk, members in clusters:
            if (tk and ctk and len(tk & ctk) / len(tk | ctk) >= threshold) or _same_event(it, members[0]):
                members.append(it)
                ctk |= tk
                break
        else:
            clusters.append((set(tk), [it]))
    return [m for _, m in clusters]


def emerging_names(items: list[dict], cfg: dict, limit: int = 10) -> list[tuple[str, int, str]]:
    """Organisations doing things in the coverage that aren't on the watchlist."""
    known = {a.lower() for c in cfg["competitors"] for a in [c["name"], *c["aliases"]]}
    # Headlines are often Title Case, so the verb is matched case-insensitively.
    verbs = (r"(?i:launch(?:es)?|unveils?|announces?|introduces?|debuts?|raises?|secures?|acquires?|"
             r"partners?|teams up|rolls out|releases?|expands?|closes|bags|lands)")
    pat = re.compile(r"\b([A-Z][\w&.\-]*(?:\s+(?:[A-Z][\w&.\-]*|and|&)){0,4}?)\s+" + verbs + r"\b")
    found: dict[str, list[str]] = defaultdict(list)
    for it in items:
        title = _clean_title(it["title"])
        for m in pat.finditer(title):
            for part in re.split(r"\s+(?:and|&)\s+", m.group(1)):
                words = part.split()
                while words and words[0] in _NOT_ORG:
                    words = words[1:]
                name = " ".join(words)
                if len(name) < 3 or name.lower() in known or any(k in name.lower() for k in known):
                    continue
                if title not in found[name]:
                    found[name].append(title)
    ranked = sorted(found.items(), key=lambda kv: -len(kv[1]))[:limit]
    return [(n, len(t), t[0]) for n, t in ranked]


def _pct(cur: int, prev: int) -> str:
    if prev == 0:
        return "new" if cur else "—"
    d = round(100 * (cur - prev) / prev)
    return f"{'+' if d > 0 else ''}{d}%"


def _arrow(cur: int, prev: int) -> str:
    if cur > prev:
        return "<span class='up'>▲</span>"
    if cur < prev:
        return "<span class='dn'>▼</span>"
    return "<span class='mut'>·</span>"


# --------------------------------------------------------------------------
# HTML report
# --------------------------------------------------------------------------

def _heat(matrix: dict, rows: list[str], cols: list[str], row_label: str) -> str:
    peak = max([v for r in matrix.values() for v in r.values()] or [1])
    head = "".join(f"<th>{html.escape(c)}</th>" for c in cols)
    body = []
    for r in rows:
        cells = []
        for c in cols:
            v = matrix[r].get(c, 0)
            a = 0 if not v else 0.12 + 0.75 * v / peak
            cells.append(f'<td class="n" style="--a:{a:.2f}">{v or ""}</td>')
        body.append(f"<tr><th class='rh'>{html.escape(r)}</th>{''.join(cells)}</tr>")
    return (f"<div class='scroll'><table class='heat'><thead><tr><th>{row_label}</th>{head}</tr>"
            f"</thead><tbody>{''.join(body)}</tbody></table></div>")


def _tags(it: dict) -> str:
    tags = "".join(f"<span class='tag c'>{html.escape(x)}</span>" for x in it["competitors"])
    tags += "".join(f"<span class='tag s'>{html.escape(x)}</span>" for x in it["signals"])
    tags += "".join(f"<span class='tag k'>{html.escape(x)}</span>" for x in it["capabilities"])
    tags += "".join(f"<span class='tag v'>{html.escape(x)}</span>" for x in it.get("voices", []))
    if it.get("kind") == "Academic":
        tags += "<span class='tag a'>Academic</span>"
    return tags


def _link(it: dict, text: str) -> str:
    link = html.escape(it["url"]) if it["url"].startswith("http") else ""
    text = html.escape(text or "(untitled)")
    return f"<a href='{link}' target='_blank' rel='noopener'>{text}</a>" if link else text


def _more(rows: list[str], n: int, cls: str, empty: str = "") -> str:
    """A list showing its first n rows, with the rest behind a "Show more" toggle, so cards that
    sit side by side stay a similar height without dropping anything."""
    if not rows:
        return f"<ul class='{cls}'>{empty}</ul>" if empty else ""
    out = f"<ul class='{cls}'>{''.join(rows[:n])}</ul>"
    if len(rows) > n:
        out += (f"<details class='more'><summary>Show {len(rows) - n} more</summary>"
                f"<ul class='{cls}'>{''.join(rows[n:])}</ul></details>")
    return out


def _dlabel(it: dict) -> str:
    """Publish date, or when we first found it for pages LinkedIn doesn't date (articles, company pages)."""
    return html.escape(it["date"] if it.get("dated", True) else f"found {it['date']}")


def _plabel(p: int) -> str:
    return "Last week" if p == 7 else f"Last {p} days"


def _h2(sec: str, title: str, p: int | None = None) -> str:
    eyebrow = f"<span class='eyebrow'>{_plabel(p)}</span>" if p else ""
    return f"<h2 data-sec='{sec}'>{eyebrow}{title}</h2>"


LINKEDIN_SOURCES = ("tavily", "brave", "serpapi")


def _has_linkedin_source(last: dict | None, stats: list) -> bool:
    return any(st["source"] in LINKEDIN_SOURCES and st["results"] for st in stats)


def _trends_section(cfg, p, cur, prev, briefs, earliest, seg, first_run) -> str:
    t = trend_stats(cur, prev)
    prior_start = (today() - timedelta(days=2 * p)).isoformat()
    cur_start = (today() - timedelta(days=p)).isoformat()
    partial = bool(earliest) and earliest > prior_start
    vs = f"vs {len(prev)} in the prior {p} days" + (" (prior period only partly collected)" if partial else "")
    # Search engines favour recent results, so until runs have been accumulating
    # through the prior period, older items are under-represented.
    backfilled = not first_run or first_run[:10] > cur_start

    # --- At a glance -----------------------------------------------------
    glance = [f"<b>{len(cur)}</b> items in the last {p} days, {vs}"
              + (f" — <b>{_pct(len(cur), len(prev))}</b>" if prev else "") + "."]
    total_mentions = sum(t["comp_cur"].values()) or 1
    top = t["comp_cur"].most_common(3)
    if top:
        glance.append("Most visible: " + ", ".join(
            f"<b>{html.escape(c)}</b> ({round(100 * n / total_mentions)}% of mentions)" for c, n in top) + ".")
    rising = sorted(((c, n, t["comp_prev"].get(c, 0)) for c, n in t["comp_cur"].items()
                     if n >= 2 and n >= 1.5 * t["comp_prev"].get(c, 0) + 1), key=lambda x: x[2] - x[1])
    if rising:
        glance.append("Gaining attention: " + ", ".join(
            f"<b>{html.escape(c)}</b> ({pv}→{n})" for c, n, pv in rising[:4]) + ".")
    quiet = [c for c, n in t["comp_prev"].items() if n >= 2 and t["comp_cur"].get(c, 0) == 0]
    if quiet:
        glance.append("Gone quiet (active before, nothing this period): "
                      + ", ".join(html.escape(c) for c in quiet[:5]) + ".")
    moves = [(k, n) for k, n in t["sig_cur"].most_common() if k in KEY_SIGNALS][:3]
    if moves:
        glance.append("Most common moves: " + ", ".join(
            f"{html.escape(k).lower()} ({n})" for k, n in moves) + ".")
    if t["cap_cur"]:
        cap, n = t["cap_cur"].most_common(1)[0]
        line = f"Capability most discussed: <b>{html.escape(cap)}</b> ({n})"
        growth = sorted(((k, v - t["cap_prev"].get(k, 0)) for k, v in t["cap_cur"].items()),
                        key=lambda kv: -kv[1])
        if growth and growth[0][1] >= 2 and growth[0][0] != cap:
            line += f"; fastest growing: <b>{html.escape(growth[0][0])}</b> (+{growth[0][1]})"
        glance.append(line + ".")
    skept = sum(1 for i in cur if "Skepticism / risk" in i["signals"])
    if cur:
        glance.append(f"Skepticism / risk framing in <b>{round(100 * skept / len(cur))}%</b> of items"
                      + (f" (prior: {round(100 * sum(1 for i in prev if 'Skepticism / risk' in i['signals']) / len(prev))}%)"
                         if prev else "") + ".")
    if cur and "score" in cur[0]:
        best = max(cur, key=lambda i: i["score"])
        glance.append(f"Most worth reading: {_link(best, _clean_title(best['title']))} "
                      "(see <i>Rising to the top</i>).")
    outside = [i for i in cur if not i["competitors"]]
    if cur:
        acad = sum(1 for i in cur if i.get("kind") == "Academic")
        active_voices = {v for i in cur for v in i.get("voices", [])}
        glance.append(f"Outside the watchlist: <b>{len(outside)}</b> items ({round(100 * len(outside) / len(cur))}%); "
                      f"academic / research: <b>{acad}</b>; tracked voices active: <b>{len(active_voices)}</b>"
                      " (see <i>Beyond the watchlist</i>).")
    glance_html = "".join(f"<li>{g}</li>" for g in glance)
    if backfilled and prev:
        glance_html += ("<li class='mut'>Changes vs the prior period are likely overstated: the prior period was "
                        "back-filled in one search, and search engines under-return older items. Comparisons "
                        "firm up once regular runs have covered both periods.</li>")

    # --- AI narrative (optional) ----------------------------------------
    ai = briefs.get(f"_trends:{p}")
    ai_html = (f"<div class='panel ai'><h3>AI trend summary <small>· {html.escape(ai['created'][:10])}</small></h3>"
               f"<pre>{html.escape(ai['body'])}</pre></div>") if ai else ""

    # --- Key moves -------------------------------------------------------
    key_items = [i for i in cur if any(s in KEY_SIGNALS for s in i["signals"])]
    stories = cluster_stories(key_items)
    stories.sort(key=lambda m: (len(m), bool(m[0]["competitors"]), max(i["date"] for i in m)), reverse=True)
    move_rows = []
    for m in stories[:10]:
        lead = max(m, key=lambda i: len(i["snippet"]))
        comps = sorted({c for i in m for c in i["competitors"]})
        sigs = sorted({s for i in m for s in i["signals"] if s in KEY_SIGNALS})
        cov = f"{len(m)} sources" if len(m) > 1 else "1 source"
        move_rows.append(
            f"<li><div class='t'>{_link(lead, _clean_title(lead['title']))}</div>"
            f"<div class='meta'>{html.escape(max(i['date'] for i in m))} · {cov} "
            + "".join(f"<span class='tag c'>{html.escape(c)}</span>" for c in comps)
            + "".join(f"<span class='tag s'>{html.escape(s)}</span>" for s in sigs) + "</div></li>")
    moves_html = _more(move_rows, 5, "moves", "<li class='mut'>No launches, deals, funding, leadership or validation news this period.</li>")

    # --- Momentum table ---------------------------------------------------
    sig_by, cap_by = defaultdict(Counter), defaultdict(Counter)
    for i in cur:
        for c in i["competitors"]:
            sig_by[c].update(i["signals"])
            cap_by[c].update(i["capabilities"])
    names = sorted(set(t["comp_cur"]) | set(t["comp_prev"]),
                   key=lambda c: (-t["comp_cur"].get(c, 0), -t["comp_prev"].get(c, 0)))
    mom_rows = "".join(
        f"<tr><th class='rh'>{html.escape(c)} <small>{html.escape(seg.get(c, ''))}</small></th>"
        f"<td class='num'>{t['comp_cur'].get(c, 0)}</td><td class='num'>{t['comp_prev'].get(c, 0)}</td>"
        f"<td class='num'>{_arrow(t['comp_cur'].get(c, 0), t['comp_prev'].get(c, 0))} "
        f"{_pct(t['comp_cur'].get(c, 0), t['comp_prev'].get(c, 0))}</td>"
        f"<td>{html.escape(sig_by[c].most_common(1)[0][0]) if sig_by[c] else '—'}</td>"
        f"<td>{html.escape(cap_by[c].most_common(1)[0][0]) if cap_by[c] else '—'}</td></tr>"
        for c in names)
    mom_html = (f"<div class='scroll'><table class='mom'><thead><tr><th>Competitor</th><th>Items · last {p}d</th>"
                f"<th>Items · prior {p}d</th><th>Change</th><th>Main signal</th><th>Main capability</th></tr></thead>"
                f"<tbody>{mom_rows or '<tr><td colspan=6>No competitor mentions.</td></tr>'}</tbody></table></div>"
                "<p class='foot foot-out'>Items = LinkedIn posts and articles, news stories and papers that name the "
                "competitor (or one of its products) in the period. An item naming several competitors counts for each. "
                "Company pages and job listings aren't counted. Undated items count from the date they were found.</p>")

    # --- Names not on the watchlist ----------------------------------------
    emerging = emerging_names(cur, cfg)
    em_html = _more([f"<li><span><b>{html.escape(n)}</b> <small>{html.escape(ex[:110])}</small></span><b>{k}</b></li>"
                     for n, k, ex in emerging], 5, "lb", "<li class='mut'>None detected.</li>")

    return f"""
{_h2("summary", "Summary &amp; recent trends", p)}
<div class="cols">
 <div class="panel"><h3>At a glance</h3><ul class="glance">{glance_html}</ul></div>
 {ai_html or '<div class="panel"><h3>Key moves</h3>' + moves_html + '</div>'}
</div>
{'<div class="panel" style="margin-top:12px"><h3>Key moves</h3>' + moves_html + '</div>' if ai_html else ''}
<h3 class="sub">Momentum vs prior {p} days</h3>{mom_html}
<div class="panel" style="margin-top:12px"><h3>Organizations not on the watchlist <small>· launching, raising or partnering in this period's coverage</small></h3>
{em_html}</div>"""


def _beyond_section(cfg, p, cur) -> str:
    vmeta = {v["name"]: v for v in cfg["voices"]}

    # --- news from companies / people not on the watchlist ---------------
    outside = [i for i in cur if not i["competitors"] and i.get("kind") != "Academic"]
    stories = cluster_stories(outside)
    stories.sort(key=lambda m: (len(m), max(i["date"] for i in m)), reverse=True)
    rows = []
    for m in stories[:16]:
        lead = max(m, key=lambda i: len(i["snippet"]))
        tags = "".join(f"<span class='tag s'>{html.escape(x)}</span>" for x in sorted({x for i in m for x in i["signals"]}))
        tags += "".join(f"<span class='tag k'>{html.escape(x)}</span>" for x in sorted({x for i in m for x in i["capabilities"]}))
        tags += "".join(f"<span class='tag v'>{html.escape(x)}</span>" for x in sorted({x for i in m for x in i.get("voices", [])}))
        who = f" · {html.escape(lead['author'])}" if lead.get("author") else ""
        rows.append(f"<li><div class='t'>{_link(lead, _clean_title(lead['title']))}</div>"
                    f"<div class='meta'>{html.escape(max(i['date'] for i in m))} · {html.escape(lead['channel'])}{who} · "
                    f"{len(m)} source{'s' if len(m) > 1 else ''} {tags}</div></li>")
    news_html = _more(rows, 6, "moves", "<li class='mut'>Nothing outside the watchlist this period.</li>")

    # --- tracked voices ----------------------------------------------------
    by_voice = defaultdict(list)
    for i in cur:
        for v in i.get("voices", []):
            by_voice[v].append(i)
    vrows = [
        f"<li><div class='vh'><span><b>{html.escape(v)}</b> <small>{html.escape(vmeta[v]['kind'])} · "
        f"{html.escape(vmeta[v].get('affiliation', ''))}</small></span><b>{len(its)}</b></div>"
        f"<div class='meta'>Latest: {_link(its[0], _clean_title(its[0]['title']))} · {html.escape(its[0]['date'])}</div></li>"
        for v, its in sorted(by_voice.items(), key=lambda kv: -len(kv[1]))]
    quiet = len(vmeta) - len(by_voice)
    voices_html = (_more(vrows, 4, "moves", "<li class='mut'>No tracked voices mentioned this period.</li>")
                   + f"<p class='mut' style='margin:6px 0 0'>{quiet} of {len(vmeta)} tracked voices not seen this period. "
                   f"Edit the list under <code>[[voices]]</code> in config.toml.</p>")

    # --- academic & research ------------------------------------------------
    acad = [i for i in cur if i.get("kind") == "Academic"]
    acad.sort(key=lambda i: (i["source"] != "arxiv", i["date"]), reverse=True)
    # strongest matches first: papers naming more synthetic-research capabilities
    papers = sorted((i for i in acad if i["source"] == "arxiv"),
                    key=lambda i: (len(i["capabilities"]), i["date"]), reverse=True)
    studies = [i for i in acad if i["source"] != "arxiv"]
    def arow(i):
        who = f"<small>{html.escape(i['author'])}</small> · " if i.get("author") else ""
        cap = "".join(f"<span class='tag k'>{html.escape(x)}</span>" for x in i["capabilities"])
        return (f"<li><div class='t'>{_link(i, _clean_title(i['title']))}</div>"
                f"<div class='meta'>{who}{html.escape(i['date'])} · {html.escape(i['url_type'] if i['source'] == 'arxiv' else i['channel'])} {cap}</div></li>")
    acad_html = ""
    if studies:
        acad_html += "<h4>Studies in the news &amp; on LinkedIn</h4>" + _more([arow(i) for i in studies[:10]], 3, "moves")
    if papers:
        acad_html += (f"<h4>New papers <small>· arXiv, {len(papers)} this period</small></h4>"
                      + _more([arow(i) for i in papers], 4, "moves"))
    acad_html = acad_html or "<p class='mut'>No academic items this period.</p>"

    # --- people to watch (not on the voices list) -----------------------------
    known = {a.lower() for v in cfg["voices"] for a in v.get("aliases", [v["name"]])}
    people = defaultdict(list)
    for i in cur:
        a = i.get("author", "")
        if not a or i["source"] == "arxiv":
            continue  # paper authors are listed with their papers
        if a.lower() not in known:
            people[a].append(i)
    prow = [f"<li><span><b>{html.escape(n)}</b> <small>{html.escape(_clean_title(its[0]['title'])[:100])}</small></span><b>{len(its)}</b></li>"
            for n, its in sorted(people.items(), key=lambda kv: -len(kv[1]))[:20]]
    people_html = _more(prow, 5, "lb", "<li class='mut'>None detected. People are found when they author an indexed LinkedIn "
                                       "post or article, or are quoted as a professor / researcher.</li>")

    return f"""
{_h2("beyond", "Beyond the watchlist", p)}
<div class="panel"><h3>News from others <small>· items that name no tracked competitor, same story merged</small></h3>
{news_html}</div>
<div class="cols" style="margin-top:12px">
 <div class="panel"><h3>Industry voices</h3>{voices_html}
  <h4>People to watch <small>· speaking about synthetic, not on the voices list</small></h4>{people_html}</div>
 <div class="panel"><h3>Academic &amp; research</h3>{acad_html}</div>
</div>"""


def _period_panel(cfg, p, all_items, briefs, last_run, earliest, first_run, any_counts=True) -> str:
    cur, prev = split_periods(all_items, p)
    items = cur
    seg = {c["name"]: c.get("segment", "") for c in cfg["competitors"]}
    comp_count = Counter(c for it in items if it.get("url_type") not in NOT_ACTIVITY for c in it["competitors"])
    comps = [c for c, _ in comp_count.most_common()]
    sig_cols, cap_cols = list(cfg["signals"]), list(cfg["capabilities"])
    sig_m, cap_m = defaultdict(Counter), defaultdict(Counter)
    for it in items:
        for c in it["competitors"]:
            sig_m[c].update(it["signals"])
            cap_m[c].update(it["capabilities"])
    channel_count = Counter(it["channel"] for it in items)
    new_items = [it for it in items if last_run and it["first_seen"] == last_run]
    market_caps = Counter(c for it in items for c in it["capabilities"])

    def row(it):
        return (f"<tr><td class='d'>{_dlabel(it)}</td>"
                f"<td class='d'><span class='ch ch-{html.escape(it['channel'])}'>{html.escape(it['channel'])}</span><br><small>{html.escape(it['url_type'])}</small></td>"
                f"<td><div class='t'>{_link(it, it['title'])}</div><div class='sn'>{html.escape(it['snippet'][:320])}</div>"
                f"<div>{_tags(it)}{_att_badges(it['att']) if 'att' in it else ''}</div></td></tr>")

    brief_html = "".join(
        f"<article class='brief'><h3>{html.escape(c)} <small>{html.escape(seg.get(c, ''))} · "
        f"{html.escape(b['created'][:10])}</small></h3><pre>{html.escape(b['body'])}</pre></article>"
        for c, b in sorted(briefs.items(), key=lambda kv: -comp_count.get(kv[0], 0)) if not c.startswith("_"))
    lb = _more([f"<li><span>{html.escape(c)} <small>{html.escape(seg.get(c, ''))}</small></span><b>{n}</b></li>"
                for c, n in comp_count.most_common()], 7, "lb")
    caps = _more([f"<li><span>{html.escape(c)}</span><b>{n}</b></li>" for c, n in market_caps.most_common()], 7, "lb")
    hidden = "" if p == cfg["settings"]["default_period"] else " hidden"

    return f"""<section class="period" data-period="{p}"{hidden}>
{_trends_section(cfg, p, cur, prev, briefs, earliest, seg, first_run)}
{_attention_section(cfg, p, cur, any_counts)}
{_beyond_section(cfg, p, cur)}
{_h2("overview", "Overview", p)}
<div class="kpis">
 <div class="kpi"><b>{len(items)}</b>items tracked</div>
 <div class="kpi"><b>{len(new_items)}</b>new this run</div>
 <div class="kpi"><b>{channel_count.get("linkedin", 0)}</b>LinkedIn items</div>
 <div class="kpi"><b>{channel_count.get("news", 0)}</b>news items</div>
 <div class="kpi"><b>{len(comps)}</b>competitors active</div>
</div>
<div class="cols">
 <div class="panel"><h3>Share of voice</h3>{lb or "<ul class='lb'><li>No data yet</li></ul>"}</div>
 <div class="panel"><h3>Capabilities discussed (market-wide)</h3>{caps or "<ul class='lb'><li>No data yet</li></ul>"}</div>
</div>
<h3 class="sub">Competitor × signal type</h3>{_heat(sig_m, comps, sig_cols, "Competitor")}
<h3 class="sub">Competitor × capability</h3>{_heat(cap_m, comps, cap_cols, "Competitor")}
{"<h3 class='sub'>AI briefs</h3><div class='briefs'>" + brief_html + "</div>" if brief_html else ""}
<h3 class="sub">New this run</h3>
<div class="scroll"><table class="feed"><tbody>{"".join(row(i) for i in new_items[:50]) or "<tr><td>Nothing new.</td></tr>"}</tbody></table></div>
{_h2("items", "All items", p)}
<input class="q" placeholder="Filter by competitor, signal, keyword…">
<div class="scroll"><table class="feed all"><tbody>{"".join(row(i) for i in items) or "<tr><td>No items in this period.</td></tr>"}</tbody></table></div>
</section>"""


def _coverage_section(cfg, stats, last, earliest) -> str:
    if not last:
        return ""
    by_src = defaultdict(list)
    for st in stats:
        by_src[st["source"]].append(st)
    rows = ""
    for src, sts in by_src.items():
        rows += (f"<tr><th class='rh'>{html.escape(src)}</th><td class='num'>{len(sts)}</td>"
                 f"<td class='num'>{sum(s['results'] for s in sts)}</td><td class='num'>{sum(s['kept'] for s in sts)}</td>"
                 f"<td class='num'>{sum(1 for s in sts if s['results'] == 0)}</td>"
                 f"<td class='num'>{sum(1 for s in sts if s['capped'])}</td>"
                 f"<td class='num'>{sum(1 for s in sts if s['error'])}</td></tr>")
    ran = set(by_src)
    missing = [s for s in LINKEDIN_SOURCES if s not in ran or all(x["results"] == 0 for x in by_src.get(s, []))]
    linkedin_ran = len(missing) < len(LINKEDIN_SOURCES)
    capped = [s for s in stats if s["capped"]]
    zero = [s for s in stats if s["results"] == 0 and s["source"] != "inbox"]
    details = ""
    if capped:
        details += "<p><b>Hit the result cap</b> (raise <code>max_pages</code> or narrow these):</p><ul class='ql'>" + "".join(
            f"<li><code>{html.escape(s['source'])}</code> {html.escape(s['query'])}</li>" for s in capped[:25]) + "</ul>"
    if zero:
        details += (f"<details><summary>{len(zero)} queries returned nothing</summary><ul class='ql'>"
                    + "".join(f"<li><code>{html.escape(s['source'])}</code> {html.escape(s['query'])}</li>" for s in zero)
                    + "</ul></details>")
    lb = last.get("lookback")
    gaps = [
        "Search engines index only part of LinkedIn. Many personal-profile posts, all comments, and anything behind login never appear in results.",
        "News items are tagged from the headline only (Google News doesn't return article text), so signal and capability tags undercount.",
        "Posts by a competitor's employees that don't name the company or a tracked product are missed. Add product names and exec names as aliases to catch more.",
        "Competitors not in config.toml are only caught when they show up next to topic terms. The 'Organizations not on the watchlist' list helps find them.",
        "People are caught three ways: by name (the voices list), as the author of an indexed LinkedIn post or article, or when quoted as a professor or researcher. Commentators quoted any other way are missed.",
        "Engagement counts (reactions, comments) are only known when a search engine shows them in its result, or you add them in an inbox file. LinkedIn offers no approved way to read engagement on other people's posts, so many posts get ranked on search prominence alone.",
        "Academic coverage is arXiv plus press coverage of studies. Journals, SSRN and conference papers that aren't on arXiv are not searched.",
    ]
    if not linkedin_ran:
        gaps.insert(0, "<span class='warn'>LinkedIn search didn't run this time</span> (no Tavily, Brave Search or SerpAPI key). "
                       "LinkedIn coverage is limited to posts added to the inbox, and engagement counts can't be collected.")
    return f"""<section class="coverage">
<h2 data-sec="coverage" id="coverage"><span class="eyebrow">Last run</span>Coverage &amp; blind spots</h2>
<p class="mut">Last run {html.escape(last['started'][:16].replace('T', ' '))} UTC · sources: {html.escape(last['sources'])}
 · lookback {lb or '?'} days · data back to {html.escape(earliest or '—')}</p>
<div class="scroll"><table class="mom"><thead><tr><th>Source</th><th>Queries</th><th>Results</th><th>Kept</th>
<th>Empty</th><th>Capped</th><th>Errors</th></tr></thead><tbody>{rows or '<tr><td colspan=7>No query stats for this run.</td></tr>'}</tbody></table></div>
{details}
<div class="panel" style="margin-top:12px"><h3>Known blind spots</h3><ul class="glance">{''.join(f'<li>{g}</li>' for g in gaps)}</ul></div>
</section>"""


SUBSCRIBE_HTML = r'''
<section class="panel sub" id="sub" aria-labelledby="sub-h">
 <div class="sub-text">
  <h3 id="sub-h">Get this report every Monday</h3>
  <p class="mut">A short digest by email, with a link back to this page.</p>
 </div>
 <div class="sub-body">
  <p class="mut" data-state="loading">Checking your subscription…</p>
  <p class="mut" data-state="offline" hidden>Sign up on the hosted report: <a href="__HOSTED__" target="_blank" rel="noopener">open the report page</a>.</p>
  <p class="mut" data-state="signin" hidden>Sign-up isn't available in this view. Open the report on claude.ai while signed in to subscribe.</p>
  <p class="mut" data-state="noaccess" hidden>You can read this report but not subscribe yet. Ask the report's owner to give you Contributor access in the Share menu.</p>
  <p data-state="owner" hidden>You get this email as the report's owner. Approve or remove subscribers below.</p>
  <form data-state="form" id="sub-form" hidden novalidate>
   <label for="sub-email">Work email</label>
   <div class="sub-row"><input id="sub-email" type="email" autocomplete="email" placeholder="you@__DOMAIN0__" required><button type="submit" id="sub-btn">Subscribe</button></div>
   <p class="sub-err" id="sub-err" role="alert" hidden></p>
  </form>
  <div data-state="on" hidden>
   <p>Subscribed as <b id="sub-addr"></b> <span class="pill" id="sub-status"></span></p>
   <p class="mut" id="sub-wait" hidden>The report's owner approves new subscribers before the first email.</p>
   <button type="button" class="ghost" id="sub-off">Unsubscribe</button>
  </div>
 </div>
 <div class="sub-admin" id="sub-admin" hidden>
  <h4>Subscribers</h4>
  <ul class="lb" id="sub-list"></ul>
 </div>
</section>
<script>
(function(){
 var box=document.getElementById('sub'); if(!box) return;
 var DOMAINS=__DOMAINS__;
 function q(s){return box.querySelector(s)}
 function show(state){box.querySelectorAll('[data-state]').forEach(function(e){e.hidden=e.dataset.state!==state})}
 function okEmail(e){return /^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(e)&&(!DOMAINS.length||DOMAINS.some(function(d){return e.toLowerCase().slice(-(d.length+1))==='@'+d}))}
 if(!window.claude||typeof window.claude.use!=='function'){show('offline');return}
 (async function(){
  var caps=await Promise.all([claude.use('db'),claude.use('user')]), db=caps[0], user=caps[1];
  if(!db||!user){show('signin');return}
  var me=await user.me();
  if(!me.id){show('signin');return}
  var owner=me.isOwner, write=await user.can('data.write');
  var mine=null, approved=new Set(), subs=[], err=q('#sub-err');
  if(me.email&&!q('#sub-email').value) q('#sub-email').value=me.email;
  function renderMine(){
   if(owner){show('owner');return}
   if(mine){
    var a=approved.has(me.id), st=q('#sub-status');
    q('#sub-addr').textContent=String(mine.email||'');
    st.textContent=a?'Active':'Pending approval'; st.className='pill '+(a?'ok':'wait');
    q('#sub-wait').hidden=a; show('on');
   } else if(write===false){show('noaccess')} else {show('form')}
  }
  function btn(label,cls,fn){var b=document.createElement('button');b.type='button';b.textContent=label;if(cls)b.className=cls;
   b.addEventListener('click',async function(){b.disabled=true;try{await fn()}catch(e){b.disabled=false}});return b}
  function renderAdmin(){
   if(!owner) return;
   var ul=q('#sub-list'); ul.textContent='';
   if(!subs.length){var li0=document.createElement('li');li0.className='mut';li0.textContent='No subscribers yet. Share this page, and people with Contributor access can sign up here.';ul.append(li0)}
   subs.forEach(function(d){
    var b=d.data()||{}, a=approved.has(d.id), li=document.createElement('li'), who=document.createElement('span'),
        em=document.createElement('b'), st=document.createElement('small'), acts=document.createElement('span');
    em.textContent=String(b.email||'(no email)'); st.textContent=' '+(a?'Active':'Pending approval');
    who.append(em,st); acts.className='acts';
    if(!a) acts.append(btn('Approve','',function(){return db.doc('approvals/'+d.id).set({approved:true,at:new Date().toISOString()})}));
    acts.append(btn('Remove','ghost',async function(){await db.doc('subscribers/'+d.id).delete();await db.doc('approvals/'+d.id).delete()}));
    li.append(who,acts); ul.append(li);
   });
   q('#sub-admin').hidden=false;
  }
  db.collection('approvals').onSnapshot(function(s){
   approved=new Set(s.docs.filter(function(d){return (d.data()||{}).approved===true}).map(function(d){return d.id}));
   renderMine(); renderAdmin();
  },function(){});
  if(owner){db.collection('subscribers').onSnapshot(function(s){subs=s.docs;renderAdmin()},function(){})}
  else {db.doc('subscribers/'+me.id).onSnapshot(function(d){mine=d.exists?d.data():null;renderMine()},function(){})}
  renderMine();
  q('#sub-form').addEventListener('submit',async function(e){
   e.preventDefault(); err.hidden=true;
   var v=q('#sub-email').value.trim();
   if(!okEmail(v)){err.textContent='Enter your work address ('+DOMAINS.map(function(d){return '@'+d}).join(' or ')+').';err.hidden=false;return}
   var b=q('#sub-btn'); b.disabled=true;
   try{await db.doc('subscribers/'+me.id).set({email:v,subscribedAt:new Date().toISOString()})}
   catch(x){if(x&&x.code==='invalid_argument'){show('noaccess')}else{err.textContent="Couldn't save your subscription. Try again in a moment.";err.hidden=false}}
   finally{b.disabled=false}
  });
  q('#sub-off').addEventListener('click',async function(){var b=q('#sub-off');b.disabled=true;
   try{await db.doc('subscribers/'+me.id).delete()}catch(x){}finally{b.disabled=false}});
 })();
})();
</script>
'''


def _subscribe_html(cfg: dict) -> str:
    e = cfg.get("email", {})
    if not e.get("signup_enabled", False):
        # Sign-up storage is off (it stopped the hosted page loading); people are added by the owner instead.
        url = e.get("signup_url", "")
        action = (f"<a class='btn' href='{html.escape(url)}' target='_blank' rel='noopener'>Sign up for the email</a>"
                  if url else "<p class='mut'>To be added, ask the report's owner.</p>")
        return ("<section class='panel sub sub-static' id='sub'><div><h3>Get this report every Monday</h3>"
                "<p class='mut'>A short digest by email, with a link back to this page.</p></div>"
                f"{action}</section>")
    domains = e.get("allowed_domains", [])
    return (SUBSCRIBE_HTML.replace("__HOSTED__", html.escape(e.get("hosted_url", "")))
            .replace("__DOMAINS__", json.dumps(domains))
            .replace("__DOMAIN0__", html.escape(domains[0] if domains else "example.com")))


def render_html(cfg, all_items, briefs, last, stats, earliest, first_run) -> str:
    periods = cfg["settings"]["report_periods"]
    default = cfg["settings"]["default_period"]
    last_run = last["started"] if last else None
    any_counts = any(i.get("att", {}).get("reactions") or i.get("att", {}).get("comments") for i in all_items)
    buttons = "".join(
        f"<button type='button' data-p='{p}' aria-pressed='{str(p == default).lower()}'>"
        f"{'Last week' if p == 7 else f'{p} days'}</button>" for p in periods)
    jumps = "".join(f"<button type='button' data-jump='{k}'>{v}</button>" for k, v in (
        ("summary", "Summary"), ("rising", "Rising"), ("beyond", "Beyond the watchlist"),
        ("overview", "Overview"), ("items", "All items"), ("coverage", "Coverage")))
    panels = "".join(_period_panel(cfg, p, all_items, briefs, last_run, earliest, first_run, any_counts) for p in periods)
    linkedin_on = _has_linkedin_source(last, stats)
    used = [x for x in dict.fromkeys(st["source"] for st in stats if st["results"])]
    sources = html.escape(" · ".join(used) or "—")
    setup = "" if linkedin_on else (
        "<aside class='setup' role='note'><span class='pill wait'>Setup</span><p><b>LinkedIn search is off.</b> "
        "This report currently draws on news coverage and arXiv only, so LinkedIn posts, and the reaction and "
        "comment counts used to rank what's most discussed, aren't collected yet. Adding a Tavily "
        "(free), Brave Search or SerpAPI key to the weekly run turns them on.</p></aside>")
    stamp = now_iso()[:16].replace("T", " ")
    return f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>LinkedIn Synthetic MR Scraper</title>
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:opsz,wght@12..96,600;12..96,700&family=IBM+Plex+Mono:wght@400;500&family=IBM+Plex+Sans:ital,wght@0,400;0,500;0,600;1,400&display=swap">
<style>
/* Layout: one 1200px reading column; masthead, then a sticky toolbar (period + jump links),
   then titled sections whose cards sit on a cool grey ground. Mono carries dates and counts. */
:root{{--bg:#f1f4f6;--card:#ffffff;--fg:#14202a;--mut:#5a6875;--line:#d9e0e5;--soft:#e8edf0;
--acc:#0c727e;--acc-fg:#ffffff;--acc-soft:#dcefef;
--c:#e3ebf8;--c-fg:#23477c;--s:#faeed6;--k:#dff1e6;--k-fg:#1d633e;--v:#ede5f9;--v-fg:#54378c;--a2:#ddeff3;--a2-fg:#1a5869;
--s-fg:#7a5000;--up:#1f7d45;--dn:#bb3527;--warn:#9f5600;--warn-soft:#fbf0de;
--f-display:"Bricolage Grotesque","IBM Plex Sans",system-ui,sans-serif;
--f-body:"IBM Plex Sans",-apple-system,"Segoe UI",system-ui,sans-serif;
--f-mono:"IBM Plex Mono",ui-monospace,SFMono-Regular,Menlo,monospace}}
@media (prefers-color-scheme:dark){{:root:not([data-theme="light"]){{--bg:#0e1418;--card:#151d23;--fg:#e5ebef;--mut:#93a1ac;--line:#25313a;--soft:#1b252c;
--acc:#4fc0c8;--acc-fg:#06262a;--acc-soft:#173236;
--c:#1d2c45;--c-fg:#a9c4ef;--s:#3a2c12;--k:#16301f;--k-fg:#93d6ac;--v:#2a2140;--v-fg:#c9b4f1;--a2:#14303a;--a2-fg:#94d0de;
--s-fg:#f0c77a;--up:#66d08f;--dn:#ff8a7d;--warn:#f2ac55;--warn-soft:#33260f;color-scheme:dark}}}}
:root[data-theme="dark"]{{--bg:#0e1418;--card:#151d23;--fg:#e5ebef;--mut:#93a1ac;--line:#25313a;--soft:#1b252c;
--acc:#4fc0c8;--acc-fg:#06262a;--acc-soft:#173236;
--c:#1d2c45;--c-fg:#a9c4ef;--s:#3a2c12;--k:#16301f;--k-fg:#93d6ac;--v:#2a2140;--v-fg:#c9b4f1;--a2:#14303a;--a2-fg:#94d0de;
--s-fg:#f0c77a;--up:#66d08f;--dn:#ff8a7d;--warn:#f2ac55;--warn-soft:#33260f;color-scheme:dark}}
*{{box-sizing:border-box}}
body{{margin:0;background:var(--bg);color:var(--fg);font:15px/1.55 var(--f-body);-webkit-font-smoothing:antialiased}}
@media (prefers-reduced-motion:no-preference){{html{{scroll-behavior:smooth}}}}
main{{max-width:1200px;margin:0 auto;padding:32px clamp(16px,3vw,32px) 72px}}
a{{color:var(--acc)}}a:hover{{text-decoration:underline}}
:focus-visible{{outline:2px solid var(--acc);outline-offset:2px;border-radius:4px}}
.mut,small{{color:var(--mut)}}small{{font-size:.86em}}
code{{font:12px var(--f-mono);background:var(--soft);padding:1px 5px;border-radius:4px}}
[hidden]{{display:none!important}}

/* masthead */
.mast{{display:grid;gap:6px}}
.kicker{{font:500 12px var(--f-mono);letter-spacing:.08em;text-transform:uppercase;color:var(--acc)}}
h1{{font:700 clamp(26px,4vw,36px)/1.1 var(--f-display);letter-spacing:-.01em;margin:0;text-wrap:balance}}
.stamp{{display:flex;flex-wrap:wrap;gap:6px 16px;font:13px var(--f-mono);color:var(--mut)}}
.setup{{display:flex;gap:12px;align-items:flex-start;background:var(--warn-soft);border:1px solid color-mix(in srgb,var(--warn) 35%,transparent);
border-radius:12px;padding:12px 16px;margin-top:18px}}.setup p{{margin:0;max-width:80ch}}

/* toolbar */
.bar{{position:sticky;top:env(safe-area-inset-top,0px);z-index:5;margin:20px calc(-1 * clamp(16px,3vw,32px)) 0;
padding:10px clamp(16px,3vw,32px);background:color-mix(in srgb,var(--bg) 92%,transparent);backdrop-filter:blur(8px);
border-bottom:1px solid var(--line);display:flex;gap:10px 18px;flex-wrap:wrap;align-items:center}}
.seg{{display:inline-flex;background:var(--card);border:1px solid var(--line);border-radius:10px;padding:3px;gap:2px;
max-width:100%;overflow-x:auto;scrollbar-width:none}}.seg button{{white-space:nowrap}}
@media (max-width:600px){{.bar .lbl{{display:none}}.bar{{gap:8px}}}}
.seg button{{font:500 13px var(--f-body);padding:6px 12px;border:0;border-radius:7px;background:transparent;color:var(--fg);cursor:pointer}}
.seg button:hover{{background:var(--soft)}}
.seg button[aria-pressed=true]{{background:var(--acc);color:var(--acc-fg)}}
.jump{{display:flex;gap:4px;overflow-x:auto;min-width:0;flex:1 1 320px;scrollbar-width:none}}
.jump button{{font:13px var(--f-body);white-space:nowrap;padding:6px 10px;border:0;border-radius:7px;background:transparent;color:var(--mut);cursor:pointer}}
.jump button:hover{{color:var(--fg);background:var(--soft)}}
.lbl{{font:500 11px var(--f-mono);letter-spacing:.08em;text-transform:uppercase;color:var(--mut)}}

/* sections */
h2{{font:600 22px/1.2 var(--f-display);margin:48px 0 14px;scroll-margin-top:84px;text-wrap:balance}}
h2 .eyebrow{{display:block;font:500 11px var(--f-mono);letter-spacing:.08em;text-transform:uppercase;color:var(--mut);margin-bottom:4px}}
h3{{font:600 15px/1.3 var(--f-body);margin:0 0 10px}}
h3.sub{{font-size:14px;margin:26px 0 10px;color:var(--fg)}}
h4{{font:500 11px var(--f-mono);margin:18px 0 8px;color:var(--mut);text-transform:uppercase;letter-spacing:.08em}}
.panel,.kpi,.brief{{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:16px 18px;min-width:0}}
.cols{{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,340px),1fr));gap:14px;align-items:start}}
.rank-head{{display:flex;justify-content:space-between;align-items:baseline;gap:12px;margin-bottom:10px}}
.rank-head h3{{margin:0}}.rank-head .lbl{{flex:0 0 72px;text-align:right;white-space:nowrap}}
.cols-wide{{grid-template-columns:minmax(0,1.7fr) minmax(0,1fr)}}
@media (max-width:820px){{.cols-wide{{grid-template-columns:minmax(0,1fr)}}}}
.foot-out{{border-top:0;padding-top:0;margin-top:8px}}
details.more{{margin-top:2px}}
details.more>summary{{list-style:none;cursor:pointer;display:inline-block;font:500 12.5px var(--f-body);color:var(--acc);
padding:6px 0 2px}}details.more>summary::-webkit-details-marker{{display:none}}
details.more>summary::before{{content:"+ "}}details.more[open]>summary::before{{content:"− "}}
details.more[open]>summary{{margin-bottom:4px}}
.cols>*{{min-width:0}}
.note{{margin:0 0 10px;font-size:13px;color:var(--mut)}}
.foot{{margin:12px 0 0;padding-top:10px;border-top:1px dashed var(--line);font-size:12.5px;color:var(--mut)}}
.foot+.foot{{border-top:0;padding-top:0;margin-top:6px}}

/* lists */
ul.lb{{list-style:none;margin:0;padding:0}}
ul.lb li{{display:flex;justify-content:space-between;gap:12px;padding:7px 0;border-bottom:1px solid var(--soft)}}
ul.lb li:last-child{{border-bottom:0}}ul.lb li>b{{font:500 13px var(--f-mono)}}
ul.glance{{margin:0;padding-left:18px}}ul.glance li{{margin:6px 0}}ul.glance li::marker{{color:var(--acc)}}
ul.moves{{list-style:none;margin:0;padding:0}}
ul.moves li{{padding:10px 0;border-bottom:1px solid var(--soft)}}ul.moves li:first-child{{padding-top:2px}}ul.moves li:last-child{{border-bottom:0}}
ul.moves .meta{{font-size:12px;color:var(--mut);margin-top:4px;display:flex;flex-wrap:wrap;gap:4px 6px;align-items:center}}
ul.moves .meta a{{text-decoration:none}}
.vh{{display:flex;justify-content:space-between;gap:14px;align-items:flex-start}}.vh>*{{min-width:0}}
.t{{font-weight:600;line-height:1.35}}.t a{{color:var(--fg);text-decoration:none}}.t a:hover{{color:var(--acc);text-decoration:underline}}
ol,ul{{overflow-wrap:anywhere}}

/* rank meter */
.meter{{flex:0 0 72px;height:6px;margin-top:8px;border-radius:3px;background:var(--soft);position:relative;overflow:hidden}}
.meter::after{{content:"";position:absolute;inset:0;width:var(--w);background:var(--acc);border-radius:3px}}

/* tags & badges */
.tag{{display:inline-block;font-size:11.5px;line-height:1.5;padding:1px 8px;border-radius:99px;margin:0 4px 3px 0;white-space:nowrap}}
.tag.c{{background:var(--c);color:var(--c-fg)}}.tag.s{{background:var(--s);color:var(--s-fg)}}.tag.k{{background:var(--k);color:var(--k-fg)}}
.tag.v{{background:var(--v);color:var(--v-fg)}}.tag.a{{background:var(--a2);color:var(--a2-fg)}}
.badge{{display:inline-block;font:11px/1.6 var(--f-mono);padding:0 6px;border-radius:5px;margin:0 4px 3px 0;border:1px solid var(--line);color:var(--mut);white-space:nowrap}}
.badge.eng{{color:var(--fg);font-weight:500}}.badge.up{{color:var(--up);border-color:currentColor}}.badge.hot{{color:var(--warn);border-color:currentColor}}
.pill{{display:inline-block;font:500 11px/1.6 var(--f-mono);letter-spacing:.04em;text-transform:uppercase;padding:0 8px;border-radius:99px;border:1px solid var(--line);white-space:nowrap}}
.pill.ok{{color:var(--up);border-color:currentColor}}.pill.wait{{color:var(--warn);border-color:currentColor}}
.up{{color:var(--up)}}.dn{{color:var(--dn)}}.warn{{color:var(--warn);font-weight:600}}

/* KPIs */
.kpis{{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;margin:0 0 14px}}
.kpi{{color:var(--mut);font-size:13px}}.kpi b{{display:block;font:500 30px/1.1 var(--f-mono);color:var(--fg);margin-bottom:4px}}

/* tables */
.scroll{{overflow-x:auto;background:var(--card);border:1px solid var(--line);border-radius:12px}}
table{{border-collapse:collapse;width:100%}}th,td{{padding:9px 12px;text-align:left;vertical-align:top}}
.heat thead th,.mom thead th{{font:500 11px var(--f-mono);letter-spacing:.04em;text-transform:uppercase;color:var(--mut);white-space:nowrap;border-bottom:1px solid var(--line)}}
.heat td.n{{text-align:center;font:500 13px var(--f-mono);background:color-mix(in srgb,var(--acc) calc(var(--a)*100%),transparent);
border:1px solid var(--soft);min-width:58px}}
.heat .rh,.mom .rh{{color:var(--fg);white-space:nowrap;font-weight:500}}
.mom tbody tr+tr{{border-top:1px solid var(--soft)}}.mom td.num{{font:13px var(--f-mono);white-space:nowrap}}
.feed tr+tr{{border-top:1px solid var(--soft)}}.feed tr:hover{{background:color-mix(in srgb,var(--soft) 55%,transparent)}}
.feed .d{{white-space:nowrap;font:12px var(--f-mono);color:var(--mut);width:1%}}
.ch{{display:inline-block;font:500 11px var(--f-mono);text-transform:uppercase;letter-spacing:.04em;color:var(--acc)}}
.ch-academic{{color:var(--a2-fg)}}.ch-linkedin{{color:var(--c-fg)}}
.sn{{color:var(--mut);font-size:13px;margin:4px 0 6px;max-width:90ch}}
input.q{{width:100%;padding:10px 14px;border-radius:10px;border:1px solid var(--line);background:var(--card);color:var(--fg);font:inherit;margin:0 0 10px}}
input.q::placeholder{{color:var(--mut)}}

/* briefs */
.briefs{{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,340px),1fr));gap:12px}}
.brief pre,.ai pre{{white-space:pre-wrap;font:inherit;margin:0}}.brief h3{{font-size:16px}}

/* coverage */
ul.ql{{font-size:13px;margin:4px 0 0}}details{{margin-top:10px}}summary{{cursor:pointer;color:var(--mut)}}
.coverage>p{{font:13px var(--f-mono)}}
.disclaimer{{margin-top:32px;font-size:13px;color:var(--mut)}}

/* email sign-up */
.sub{{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1.2fr);gap:8px 24px;margin-top:18px}}
.sub.sub-static{{display:flex;justify-content:space-between;align-items:center;gap:12px 24px;flex-wrap:wrap}}.sub.sub-static p{{margin:0}}
.btn{{display:inline-block;font:500 14px var(--f-body);padding:9px 16px;border-radius:8px;background:var(--acc);color:var(--acc-fg);text-decoration:none;white-space:nowrap}}
.btn:hover{{text-decoration:none;filter:brightness(1.08)}}
@media (max-width:720px){{.sub{{grid-template-columns:minmax(0,1fr)}}}}
.sub h3{{margin:0 0 2px}}.sub p{{margin:0 0 6px}}.sub label{{display:block;font-size:12px;color:var(--mut);margin-bottom:4px}}
.sub-row{{display:flex;gap:8px;flex-wrap:wrap}}.sub-row input{{flex:1 1 220px;min-width:0;margin:0;padding:9px 12px;border-radius:8px;border:1px solid var(--line);background:var(--card);color:var(--fg);font:inherit}}
.sub button{{font:inherit;font-size:14px;padding:8px 14px;border-radius:8px;border:1px solid var(--acc);background:var(--acc);color:var(--acc-fg);cursor:pointer}}
.sub button.ghost{{background:transparent;color:var(--acc)}}.sub button:disabled{{opacity:.6;cursor:default}}
.sub-err{{color:var(--dn);font-size:13px;margin-top:6px}}
.sub-admin{{grid-column:1/-1;border-top:1px solid var(--line);padding-top:8px}}.sub-admin h4{{margin-top:4px}}
.sub-admin li{{align-items:center}}.sub-admin .acts{{display:flex;gap:6px;flex-shrink:0}}
.sub-admin .acts button{{padding:4px 10px;font-size:13px}}
</style></head><body><main>
<header class="mast">
 <span class="kicker">Competitive intel · synthetic research</span>
 <h1>LinkedIn Scraper: Synthetic Offerings in Market Research</h1>
 <div class="stamp"><span>Generated {stamp} UTC</span><span>Sources: {sources}</span><span>{len(all_items)} items collected</span></div>
</header>
{setup}
{_subscribe_html(cfg) if cfg.get("email", {}).get("hosted_url") else ""}
<nav class="bar" aria-label="Report controls">
 <span class="lbl">Period</span><div class="seg" role="group" aria-label="Period">{buttons}</div>
 <div class="jump" aria-label="Jump to section">{jumps}</div>
</nav>
{panels}
{_coverage_section(cfg, stats, last, earliest)}
<p class="disclaimer">Tags are keyword-based and approximate. Verify before citing.</p>
</main><script>
const btns=document.querySelectorAll('.seg button');
function show(p){{document.querySelectorAll('section.period').forEach(s=>s.hidden=s.dataset.period!==p);
btns.forEach(b=>b.setAttribute('aria-pressed',b.dataset.p===p));
try{{localStorage.setItem('period',p)}}catch(e){{}}}}
btns.forEach(b=>b.addEventListener('click',()=>show(b.dataset.p)));
try{{const p=localStorage.getItem('period');if(p&&document.querySelector(`section[data-period="${{p}}"]`))show(p)}}catch(e){{}}
document.querySelectorAll('.jump button').forEach(b=>b.addEventListener('click',()=>{{
const k=b.dataset.jump, vis=document.querySelector('section.period:not([hidden])');
const t=(vis&&vis.querySelector(`[data-sec="${{k}}"]`))||document.querySelector(`[data-sec="${{k}}"]`);
if(t)t.scrollIntoView({{block:'start'}})}}));
// Balance side-by-side cards: while a card is shorter than its neighbour, move rows from its
// "Show more" list into the visible list, so pairs end level without empty space or stretching.
function balance(root){{(root||document).querySelectorAll('.cols').forEach(row=>{{
 const cards=[...row.children]; if(cards.length<2) return;
 const tops=new Set(cards.map(c=>Math.round(c.getBoundingClientRect().top))); if(tops.size>1) return; // stacked on narrow screens
 for(let guard=0;guard<40;guard++){{
  const hs=cards.map(c=>c.getBoundingClientRect().height), tall=Math.max(...hs);
  const i=hs.indexOf(Math.min(...hs)), card=cards[i], d=card.querySelector('details.more:not([open])'); if(!d) break;
  const src=d.querySelector('ul'), li=src&&src.firstElementChild, dst=d.previousElementSibling; if(!li||!dst) break;
  dst.appendChild(li); const h=card.getBoundingClientRect().height;
  if(h>tall+8){{src.prepend(li);break}}
  const left=src.children.length, sum=d.querySelector('summary');
  if(!left){{d.remove();continue}} sum.textContent='Show '+left+' more';
 }}
 // If the shorter card had nothing left to reveal, trim the taller one instead (keep at least 3 rows).
 for(let guard=0;guard<20;guard++){{
  const hs=cards.map(c=>c.getBoundingClientRect().height), i=hs.indexOf(Math.max(...hs)), card=cards[i];
  const other=Math.max(...hs.filter((_,j)=>j!==i)), d=card.querySelector('details.more:not([open])');
  const vis=d&&d.previousElementSibling; if(!vis||vis.children.length<=3||hs[i]-other<40) break;
  const li=vis.lastElementChild; d.querySelector('ul').prepend(li);
  if(card.getBoundingClientRect().height<other-8){{vis.appendChild(li);break}}
  d.querySelector('summary').textContent='Show '+d.querySelector('ul').children.length+' more';
 }}
}})}}
const _show=show; show=function(p){{_show(p);balance(document.querySelector(`section[data-period="${{p}}"]`))}};
window.addEventListener('load',()=>balance(document.querySelector('section.period:not([hidden])')));
document.querySelectorAll('section.period').forEach(sec=>{{const q=sec.querySelector('input.q');
q.addEventListener('input',e=>{{const v=e.target.value.toLowerCase();
sec.querySelectorAll('table.all tr').forEach(r=>r.hidden=!r.textContent.toLowerCase().includes(v))}})}});
</script></body></html>"""


# --------------------------------------------------------------------------

KEY_FILES = (ROOT / "keys.env", Path.home() / ".config" / "synth-intel" / "keys.env")


def load_keys() -> list[str]:
    """Read API keys (TAVILY_API_KEY, BRAVE_API_KEY, SERPAPI_KEY, ANTHROPIC_API_KEY) from keys.env so scheduled
    runs, which don't see keys exported in a terminal, can use them. Real environment
    variables win. Returns the names loaded (never the values)."""
    loaded = []
    for f in KEY_FILES:
        if not f.is_file():
            continue
        for line in f.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            k, v = (x.strip() for x in line.removeprefix("export ").split("=", 1))
            v = v.strip('"').strip("'")
            if k and v and k not in os.environ:
                os.environ[k] = v
                loaded.append(k)
    return loaded


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("command", choices=["collect", "report", "run"])
    ap.add_argument("--config", default=str(ROOT / "config.toml"))
    ap.add_argument("--sources", default="news,tavily,brave,serpapi,arxiv,inbox",
                    help="comma-separated: " + ",".join(COLLECTORS))
    ap.add_argument("--days", type=int, default=None,
                    help="collection lookback in days (default: lookback_days in config)")
    ap.add_argument("--summarize", action="store_true",
                    help="generate per-competitor briefs and per-period trend summaries with Claude")
    a = ap.parse_args()

    keys = load_keys()
    if keys:
        print("Keys loaded from keys.env: " + ", ".join(keys))
    cfg = load_config(Path(a.config))
    db = open_db(ROOT / cfg["settings"]["db_path"])
    sources = [s.strip() for s in a.sources.split(",") if s.strip()]
    bad = [s for s in sources if s not in COLLECTORS]
    if bad:
        ap.error(f"unknown source(s): {', '.join(bad)}")
    if a.command in ("collect", "run"):
        cmd_collect(cfg, db, sources, a.days or cfg["settings"]["lookback_days"])
    if a.command in ("report", "run"):
        cmd_report(cfg, db, a.summarize)


if __name__ == "__main__":
    main()
