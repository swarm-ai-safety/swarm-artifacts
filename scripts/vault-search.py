#!/usr/bin/env python3
"""Search the vault by keywords, tags, type, and confidence."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).parent.parent
VAULT_DIR = ROOT / "vault"

SKIP_DIRS = {"templates"}


# ── index builder ────────────────────────────────────────────────────

def extract_frontmatter(text: str) -> tuple[dict, str]:
    """Return (frontmatter_dict, body) from a markdown file."""
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            try:
                fm = yaml.safe_load(text[3:end]) or {}
            except yaml.YAMLError:
                fm = {}
            body = text[end + 3:].strip()
            return fm, body
    return {}, text


def extract_topics(text: str) -> list[str]:
    """Extract tags from <!-- topics: tag1, tag2 --> footer."""
    m = re.search(r"<!--\s*topics:\s*(.+?)\s*-->", text)
    if m:
        return [t.strip() for t in m.group(1).split(",") if t.strip()]
    return []


def extract_h1(body: str) -> str | None:
    """Return the first H1 line content, if present."""
    for line in body.splitlines():
        line = line.strip()
        if line.startswith("# ") and not line.startswith("## "):
            return line[2:].strip()
    return None


def build_index() -> list[dict]:
    """Scan vault/ and return a list of note records."""
    records: list[dict] = []
    for md in sorted(VAULT_DIR.rglob("*.md")):
        # skip templates directory
        rel = md.relative_to(VAULT_DIR)
        if rel.parts[0] in SKIP_DIRS:
            continue

        text = md.read_text(errors="replace")
        fm, body = extract_frontmatter(text)

        fm_tags = fm.get("tags", []) or []
        if isinstance(fm_tags, str):
            fm_tags = [fm_tags]
        topic_tags = extract_topics(text)
        all_tags = sorted(set(fm_tags + topic_tags))

        records.append({
            "path": str(rel),
            "stem": md.stem,
            "type": fm.get("type", ""),
            "description": fm.get("description", ""),
            "tags": all_tags,
            "title": extract_h1(body),
            "confidence": fm.get("confidence", ""),
            "status": fm.get("status", ""),
            "body": body,
        })
    return records


# ── scoring ──────────────────────────────────────────────────────────

CONFIDENCE_SCORE = {"high": 3, "medium": 2, "low": 1}


def score_record(rec: dict, query: str | None) -> int:
    """Compute relevance score for a record against a keyword query."""
    if not query:
        return 0
    q = query.lower()
    score = 0

    # tag match
    for tag in rec["tags"]:
        if q in tag.lower():
            score += 10

    # title / H1 match
    title = rec.get("title") or ""
    if q in title.lower():
        score += 8

    # description match
    desc = rec.get("description") or ""
    if q in desc.lower():
        score += 5

    # body occurrences (capped at 5)
    body_lower = rec["body"].lower()
    count = body_lower.count(q)
    score += min(count, 5)

    # confidence boost
    conf = rec.get("confidence", "")
    if conf:
        score += CONFIDENCE_SCORE.get(conf, 0)

    return score


# ── filtering & searching ───────────────────────────────────────────

def search(
    records: list[dict],
    query: str | None = None,
    tag: str | None = None,
    note_type: str | None = None,
    confidence: str | None = None,
    limit: int = 10,
) -> list[dict]:
    """Filter and rank records. Returns list of (record, score) dicts."""
    results = []
    for rec in records:
        # type filter
        if note_type and rec["type"] != note_type:
            continue
        # tag filter
        if tag:
            tag_l = tag.lower()
            if not any(tag_l in t.lower() for t in rec["tags"]):
                continue
        # confidence filter
        if confidence and rec.get("confidence", "") != confidence:
            continue

        s = score_record(rec, query) if query else 0
        # if keyword query, skip zero-score records
        if query and s == 0:
            continue

        results.append({**rec, "_score": s})

    results.sort(key=lambda r: r["_score"], reverse=True)
    return results[:limit]


# ── output formatting ───────────────────────────────────────────────

def snippet_around(text: str, query: str, context: int = 50) -> str | None:
    """Return a body snippet with ~context chars around the first match."""
    idx = text.lower().find(query.lower())
    if idx == -1:
        return None
    start = max(0, idx - context)
    end = min(len(text), idx + len(query) + context)
    prefix = "..." if start > 0 else ""
    suffix = "..." if end < len(text) else ""
    return prefix + text[start:end].replace("\n", " ") + suffix


def highlight_tags(tags: list[str], query: str | None, tag_filter: str | None) -> str:
    """Return tags string with matches marked."""
    highlighted = []
    for t in tags:
        mark = False
        if query and query.lower() in t.lower():
            mark = True
        if tag_filter and tag_filter.lower() in t.lower():
            mark = True
        highlighted.append(f"*{t}*" if mark else t)
    return ", ".join(highlighted)


def print_results(
    results: list[dict],
    query: str | None,
    tag_filter: str | None,
    as_json: bool = False,
    verbose: bool = False,
) -> None:
    """Print search results to stdout."""
    if not results:
        print("No results found.")
        return

    if as_json:
        out = []
        for r in results:
            entry = {
                "path": r["path"],
                "type": r["type"],
                "description": r["description"],
                "tags": r["tags"],
                "score": r["_score"],
            }
            if r.get("confidence"):
                entry["confidence"] = r["confidence"]
            if r.get("title"):
                entry["title"] = r["title"]
            if verbose and query:
                snip = snippet_around(r["body"], query)
                if snip:
                    entry["snippet"] = snip
            out.append(entry)
        print(json.dumps(out, indent=2))
        return

    for i, r in enumerate(results, 1):
        type_str = r["type"] or "unknown"
        if r.get("confidence"):
            type_str += f" (confidence: {r['confidence']})"

        tag_str = highlight_tags(r["tags"], query, tag_filter)

        print(f"  {i}. {r['path']}")
        print(f"     Type: {type_str}    Score: {r['_score']}")
        if r.get("description"):
            print(f"     {r['description']}")
        if tag_str:
            print(f"     Tags: {tag_str}")
        if verbose and query:
            snip = snippet_around(r["body"], query)
            if snip:
                print(f"     ...{snip}")
        print()


# ── CLI ──────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Search the vault by keywords, tags, and type.",
        epilog="Examples:\n"
               "  vault-search.py 'transaction tax'\n"
               "  vault-search.py --tag governance\n"
               "  vault-search.py --type claim --confidence high\n"
               "  vault-search.py 'welfare' --type claim --limit 5 --verbose\n",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("query", nargs="?", default=None,
                        help="Keyword query (searches title, description, tags, body)")
    parser.add_argument("--tag", default=None, help="Filter by tag")
    parser.add_argument("--type", dest="note_type", default=None,
                        help="Filter by note type (claim, method, failure-pattern, ...)")
    parser.add_argument("--confidence", default=None,
                        choices=["high", "medium", "low", "contested"],
                        help="Filter claims by confidence level")
    parser.add_argument("--limit", type=int, default=10,
                        help="Max results to show (default: 10)")
    parser.add_argument("--json", dest="as_json", action="store_true",
                        help="Output results as JSON")
    parser.add_argument("--verbose", action="store_true",
                        help="Show body snippet with match context")

    args = parser.parse_args()

    if not args.query and not args.tag and not args.note_type and not args.confidence:
        parser.print_help()
        sys.exit(1)

    records = build_index()
    results = search(
        records,
        query=args.query,
        tag=args.tag,
        note_type=args.note_type,
        confidence=args.confidence,
        limit=args.limit,
    )

    if not args.as_json:
        parts = []
        if args.query:
            parts.append(f'query="{args.query}"')
        if args.tag:
            parts.append(f"tag={args.tag}")
        if args.note_type:
            parts.append(f"type={args.note_type}")
        if args.confidence:
            parts.append(f"confidence={args.confidence}")
        header = ", ".join(parts)
        print(f"\n  Vault search: {header}  ({len(results)} results)\n")

    print_results(results, args.query, args.tag, args.as_json, args.verbose)


if __name__ == "__main__":
    main()
