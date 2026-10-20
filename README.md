# LinkedIn scraper: synthetic offerings in market research

Tracks how competitors talk about **synthetic respondents, synthetic data, digital twins
and AI personas** on LinkedIn and in industry news. Each item is tagged by competitor,
signal type (launch, partnership, funding, validation claim, leadership change…) and
capability, then rolled into an HTML report and a CSV.

## How it gets LinkedIn data (and why not by scraping linkedin.com)

Logging in to linkedin.com and crawling it breaks LinkedIn's User Agreement and gets
accounts restricted. LinkedIn also litigates against scrapers (it sued Proxycurl in 2025).
This tool never touches linkedin.com directly. Instead it uses:

| Source   | What it gets                                                        | Setup                    |
|----------|---------------------------------------------------------------------|--------------------------|
| `tavily` | Public LinkedIn posts, articles and company pages, via Tavily search filtered to linkedin.com (~50 searches/run, free tier 1,000/month) | `TAVILY_API_KEY` |
| `brave`  | Public LinkedIn posts, Pulse articles, company pages, via `site:linkedin.com` search | `export BRAVE_API_KEY=…` (free tier available) |
| `serpapi`| Same, via Google results                                             | `export SERPAPI_KEY=…`   |
| `news`   | Google News coverage (press releases, Research Live, Quirks, etc.)   | none                     |
| `arxiv`  | Academic papers on synthetic respondents, silicon sampling, LLM personas (official arXiv API) | none |
| `inbox`  | Posts you read on LinkedIn and paste into `inbox/*.txt`              | see `inbox/_TEMPLATE.txt`|

You only need one of `tavily` / `brave` / `serpapi` for LinkedIn coverage; Tavily's free tier covers a weekly run.
Sources with no key are skipped.

### Keys

Copy `keys.env.example` to `keys.env`, paste your keys, and `chmod 600 keys.env`. The script reads it on every
run, including the Monday scheduled task (which can't see keys exported in a terminal). `keys.env` is in
`.gitignore` and must never be committed.

## Run it

```bash
python3 linkedin_scraper.py run                 # collect from all sources + build report
python3 linkedin_scraper.py collect --sources news,tavily
python3 linkedin_scraper.py collect --days 60   # override the lookback (default: lookback_days in config)
python3 linkedin_scraper.py report --summarize  # adds Claude-written competitor briefs + per-period trend summaries (ANTHROPIC_API_KEY)
```

Output: `reports/linkedin_synthetic_mr.html`, `reports/linkedin_synthetic_mr.csv`, and history in
`data/linkedin_scraper.db` (SQLite). Re-runs de-duplicate, and the report shows "new this run".

## The report

A period switcher at the top (last week, 14, 30, 60, 90 days) changes every section. Each period opens with
**Summary & recent trends**:

- **At a glance**: volume vs the prior period, most visible competitors, who's gaining attention or has
  gone quiet, the most common moves, which capabilities are being discussed, and how much coverage is skeptical.
- **Key moves**: launches, partnerships, funding, leadership changes and validation claims, with
  duplicate coverage of one story merged and counted ("3 sources").
- **Momentum**: each competitor's mentions vs the prior period, with its main signal and capability.
- **Names not on your watchlist**: organisations launching, raising or partnering in the coverage that
  aren't in `config.toml`.
- **AI trend summary** (with `--summarize`): a short written read on the period, plus implications.

Then **Rising to the top**, for deciding what to read first:

- **Most worth reading** ranks stories by an attention score built from engagement counts shown in
  search results (comments weighted ×3, since they mean discussion), growth since the last run, top-3
  search placement, how many searches return it, how many runs it has stayed in results, and how many
  sources cover it.
- **Most discussed** sorts by comment count and flags a **debate** when comments are high relative
  to reactions.

LinkedIn offers no approved way to read engagement on other people's posts, so counts are only known when
a search engine shows them (Google often does for LinkedIn posts; needs `SERPAPI_KEY` or `BRAVE_API_KEY`),
or when you add `reactions:` / `comments:` / `reposts:` lines to an inbox file. Without them, the ranking
uses the other signals. "Rising" needs at least two runs that saw the counts.

Then **Beyond the watchlist**, for what company names alone would miss:

- **News from others**: items that name no tracked competitor (new entrants, partnerships between
  non-tracked firms, commentary), with duplicate coverage merged.
- **Industry voices**: tracked people (the `[[voices]]` list in `config.toml`: academics like Olivier
  Toubia and Lisa Argyle, commentators like Ray Poynter and Mark Ritson) and what they were last seen saying.
  **People to watch** lists people who aren't on the list but are speaking about synthetic research:
  LinkedIn post authors, columnists, and quoted professors and researchers.
- **Academic & research**: studies covered in the news or on LinkedIn, plus new arXiv papers, ranked
  by how closely they match synthetic research.

The voices list is a starting point. Check the affiliations and add the people your team follows.

Under that are the overview, heatmaps, AI briefs, new items and the filterable item list. At the bottom,
**Coverage & blind spots** shows how many queries ran, how many returned nothing or hit a result cap, and
what this approach can't see.

## How complete is it?

It isn't complete, and nothing that works through search engines can be. Things to know:

- Search engines index only part of LinkedIn: many personal-profile posts, all comments, and anything
  behind login never show up.
- Results shift with query wording, so each competitor is searched with two wordings and every product
  alias is searched too. Even so, some stories surface in one run and not the next. The database keeps
  everything it has ever found, so **running it regularly (weekly) is the biggest single improvement**.
- News items are tagged from headlines only, so tags undercount.
- People are found only by name (voices list), as LinkedIn authors, or when quoted as a professor or
  researcher. Academic coverage is arXiv plus press; journals and SSRN aren't searched.
- Period-over-period changes are overstated until regular runs have covered both periods (the report
  says so when this applies).

Check the Coverage section after each run for empty or capped queries.

## Tuning

Everything lives in `config.toml`: competitors and aliases, topic terms, signal and
capability keyword rules, relevance include/exclude terms, report periods and lookback.
Tags are recomputed every time the report is built, so config edits apply to data already collected. The tags come from keyword
rules, so they're approximate. Check the source before citing anything.

To run on a schedule, use cron or launchd, e.g. weekly:
`0 7 * * 1 cd /path/to/synth-intel && python3 linkedin_scraper.py run`.

No dependencies: Python 3.11+ standard library only. If Python can't verify TLS certificates
(common behind corporate proxies), it falls back to the system `curl`.

## Hosted report, sharing and the weekly email

The report is also published as a private page: https://claude.ai/artifact/52dwftZ1hBaynPM3grou6C
(`reports/linkedin_synthetic_mr_hosted.html` is the copy that gets published). A scheduled task in the
Claude app runs the scraper every Monday at 8:00, republishes that page, and emails a digest with a link
to it.

- **Sharing:** use the page's Share menu. Give teammates **Contributor** access so they can sign up for
  the email; Viewers can read the report but can't subscribe.
- **Sign-ups:** teammates enter their @qualtrics.com address in the box at the top of the page. The owner
  sees the subscriber list there (no one else can) and approves or removes people. Only approved
  @qualtrics.com addresses are emailed, in Bcc. Change the allowed domains under `[email]` in `config.toml`.
