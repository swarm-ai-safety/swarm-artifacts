#!/usr/bin/env python3
"""
Generate a human-readable changelog of vault changes between two git commits.

Usage:
    python scripts/vault-digest.py HEAD~1..HEAD
    python scripts/vault-digest.py --since "1 week ago"
    python scripts/vault-digest.py --since "2026-02-18"
    python scripts/vault-digest.py HEAD~5..HEAD --output vault/digests/digest.md
    python scripts/vault-digest.py HEAD~5..HEAD --json
"""

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path

import yaml

ROOT = Path(__file__).parent.parent
VAULT_PREFIX = "vault/"

CATEGORY_LABELS = {
    "claims": "Claims",
    "experiments": "Experiments",
    "sweeps": "Sweeps",
    "governance": "Governance",
    "topologies": "Topologies",
    "failures": "Failures",
    "methods": "Methods",
}

CONFIDENCE_ORDER = ["low", "medium", "high"]


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------

def git(*args: str) -> str:
    """Run a git command and return stdout. Raises on failure."""
    result = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {result.stderr.strip()}")
    return result.stdout


def resolve_refs(range_str: str | None, since: str | None) -> tuple[str, str]:
    """Return (start_ref, end_ref) from either a range or --since flag."""
    if range_str:
        if ".." not in range_str:
            raise ValueError(f"Range must contain '..': got '{range_str}'")
        start, end = range_str.split("..", 1)
        # Validate refs
        git("rev-parse", "--verify", start)
        git("rev-parse", "--verify", end or "HEAD")
        return start, end or "HEAD"

    if since:
        # Find the earliest commit since the given date
        log = git("log", "--format=%H", "--reverse", f"--since={since}", "--", "vault/")
        commits = log.strip().splitlines()
        if not commits:
            raise RuntimeError(f"No vault commits found since '{since}'")
        first_commit = commits[0]
        start = f"{first_commit}~1"
        # Validate that parent exists; if it's the root commit, use empty tree
        try:
            git("rev-parse", "--verify", start)
        except RuntimeError:
            start = git("hash-object", "-t", "tree", "/dev/null").strip()
        return start, "HEAD"

    raise ValueError("Provide either a range (A..B) or --since")


def get_diff(start: str, end: str) -> list[tuple[str, str]]:
    """Return list of (status, path) for vault/ files changed between refs."""
    raw = git("diff", "--name-status", start, end, "--", "vault/")
    entries = []
    for line in raw.strip().splitlines():
        if not line:
            continue
        parts = line.split("\t", 1)
        if len(parts) != 2:
            continue
        status, path = parts[0][0], parts[1]  # first char handles R100 etc.
        entries.append((status, path))
    return entries


def get_file_at_ref(ref: str, path: str) -> str | None:
    """Return file content at a given git ref, or None if not found."""
    try:
        return git("show", f"{ref}:{path}")
    except RuntimeError:
        return None


def ref_date(ref: str) -> str:
    """Return the ISO date of a commit ref."""
    try:
        return git("log", "-1", "--format=%ci", ref).strip()[:10]
    except RuntimeError:
        return "unknown"


# ---------------------------------------------------------------------------
# Frontmatter parsing
# ---------------------------------------------------------------------------

def parse_frontmatter(text: str) -> dict | None:
    """Extract YAML frontmatter from markdown text."""
    match = re.match(r"^---\n(.+?)\n---", text, re.DOTALL)
    if not match:
        return None
    try:
        return yaml.safe_load(match.group(1)) or {}
    except yaml.YAMLError:
        return None


# ---------------------------------------------------------------------------
# Change categorisation
# ---------------------------------------------------------------------------

def categorise(path: str) -> str | None:
    """Return the vault sub-category for a path, or None."""
    rel = path.removeprefix(VAULT_PREFIX)
    for cat in CATEGORY_LABELS:
        if rel.startswith(cat + "/"):
            return cat
    if rel in ("_index.md", "categories.yaml", "vocabulary.yaml"):
        return "_index"
    return "_other"


def analyse_claim_change(start: str, end: str, path: str) -> dict:
    """Compare old and new versions of a claim file, return change details."""
    old_text = get_file_at_ref(start, path)
    new_text = get_file_at_ref(end, path)
    changes: dict = {"path": path, "details": []}

    old_fm = parse_frontmatter(old_text) if old_text else {}
    new_fm = parse_frontmatter(new_text) if new_text else {}
    if not old_fm:
        old_fm = {}
    if not new_fm:
        new_fm = {}

    changes["description"] = new_fm.get("description", Path(path).stem)
    changes["confidence_old"] = old_fm.get("confidence")
    changes["confidence_new"] = new_fm.get("confidence")
    changes["status_old"] = old_fm.get("status")
    changes["status_new"] = new_fm.get("status")

    # Confidence change
    c_old, c_new = changes["confidence_old"], changes["confidence_new"]
    if c_old and c_new and c_old != c_new:
        old_idx = CONFIDENCE_ORDER.index(c_old) if c_old in CONFIDENCE_ORDER else -1
        new_idx = CONFIDENCE_ORDER.index(c_new) if c_new in CONFIDENCE_ORDER else -1
        if new_idx > old_idx and old_idx >= 0:
            changes["confidence_direction"] = "upgraded"
        elif new_idx < old_idx and new_idx >= 0:
            changes["confidence_direction"] = "downgraded"
        else:
            changes["confidence_direction"] = "changed"
        changes["details"].append(
            f"confidence {c_old} -> {c_new}"
        )

    # Status change
    s_old, s_new = changes["status_old"], changes["status_new"]
    if s_old and s_new and s_old != s_new:
        changes["details"].append(f"status {s_old} -> {s_new}")

    # New evidence entries
    old_ev = old_fm.get("evidence", {}) or {}
    new_ev = new_fm.get("evidence", {}) or {}
    for key in ("supporting", "weakening"):
        old_list = old_ev.get(key, []) or []
        new_list = new_ev.get(key, []) or []
        added = len(new_list) - len(old_list)
        if added > 0:
            changes["details"].append(f"+{added} {key} evidence")

    # New related_claims
    old_rel = set(old_fm.get("related_claims", []) or [])
    new_rel = set(new_fm.get("related_claims", []) or [])
    added_rel = new_rel - old_rel
    if added_rel:
        changes["details"].append(f"+{len(added_rel)} related claims")

    return changes


# ---------------------------------------------------------------------------
# Digest builder
# ---------------------------------------------------------------------------

def build_digest(start: str, end: str) -> dict:
    """Build the full digest data structure."""
    entries = get_diff(start, end)

    digest: dict = {
        "start_ref": start,
        "end_ref": end,
        "start_date": ref_date(start),
        "end_date": ref_date(end),
        "added": {},
        "modified": {},
        "deleted": {},
        "claim_changes": [],
    }

    for status, path in entries:
        cat = categorise(path)
        if cat is None:
            continue

        if status == "A":
            digest["added"].setdefault(cat, []).append(path)
        elif status == "M":
            digest["modified"].setdefault(cat, []).append(path)
        elif status == "D":
            digest["deleted"].setdefault(cat, []).append(path)

    # Deep-analyse modified claims
    for path in digest["modified"].get("claims", []):
        change = analyse_claim_change(start, end, path)
        digest["claim_changes"].append(change)

    # Also capture new claim metadata
    digest["new_claims"] = []
    for path in digest["added"].get("claims", []):
        text = get_file_at_ref(end, path)
        fm = parse_frontmatter(text) if text else None
        digest["new_claims"].append({
            "path": path,
            "description": fm.get("description", Path(path).stem) if fm else Path(path).stem,
            "confidence": fm.get("confidence", "unknown") if fm else "unknown",
            "status": fm.get("status", "unknown") if fm else "unknown",
        })

    return digest


def format_markdown(digest: dict) -> str:
    """Render the digest as markdown."""
    lines: list[str] = []
    start, end = digest["start_ref"], digest["end_ref"]
    lines.append(f"# Vault Digest: {start}..{end}")
    lines.append(f"Period: {digest['start_date']} to {digest['end_date']}")
    lines.append("")

    # Summary counts
    n_new_claims = len(digest["added"].get("claims", []))
    n_mod_claims = len(digest["modified"].get("claims", []))
    n_del_claims = len(digest["deleted"].get("claims", []))
    n_new_exp = len(digest["added"].get("experiments", []))
    n_new_sweeps = len(digest["added"].get("sweeps", []))

    total_added = sum(len(v) for v in digest["added"].values())
    total_modified = sum(len(v) for v in digest["modified"].values())
    total_deleted = sum(len(v) for v in digest["deleted"].values())

    lines.append("## Summary")
    lines.append(f"- {total_added} files added, {total_modified} modified, {total_deleted} deleted")
    if n_new_claims or n_mod_claims:
        parts = []
        if n_new_claims:
            parts.append(f"{n_new_claims} new")
        if n_mod_claims:
            parts.append(f"{n_mod_claims} modified")
        if n_del_claims:
            parts.append(f"{n_del_claims} deleted")
        lines.append(f"- Claims: {', '.join(parts)}")
    if n_new_exp:
        lines.append(f"- {n_new_exp} experiment notes added")
    if n_new_sweeps:
        lines.append(f"- {n_new_sweeps} sweep summaries added")

    # Other categories
    for cat in ("governance", "topologies", "failures", "methods"):
        n_a = len(digest["added"].get(cat, []))
        n_m = len(digest["modified"].get(cat, []))
        if n_a or n_m:
            label = CATEGORY_LABELS.get(cat, cat)
            parts = []
            if n_a:
                parts.append(f"{n_a} new")
            if n_m:
                parts.append(f"{n_m} modified")
            lines.append(f"- {label}: {', '.join(parts)}")

    if digest["added"].get("_index") or digest["modified"].get("_index"):
        lines.append("- Index/metadata files updated")
    lines.append("")

    # Claims section
    if digest["new_claims"] or digest["claim_changes"]:
        lines.append("## Claims")

    if digest["new_claims"]:
        lines.append("### New")
        for c in digest["new_claims"]:
            name = Path(c["path"]).stem
            lines.append(f"- **{name}** -- {c['description']} ({c['confidence']} confidence)")
        lines.append("")

    # Partition modified claims
    strengthened = [c for c in digest["claim_changes"] if c.get("confidence_direction") == "upgraded"]
    weakened = [c for c in digest["claim_changes"]
                if c.get("confidence_direction") == "downgraded"
                or (c.get("status_new") in ("weakened", "superseded", "retracted")
                    and c.get("status_old") != c.get("status_new"))]
    other_modified = [c for c in digest["claim_changes"]
                      if c not in strengthened and c not in weakened]

    if strengthened:
        lines.append("### Strengthened")
        for c in strengthened:
            name = Path(c["path"]).stem
            detail = f"confidence upgraded {c['confidence_old']} -> {c['confidence_new']}"
            lines.append(f"- **{name}** -- {detail}")
        lines.append("")

    if weakened:
        lines.append("### Weakened")
        for c in weakened:
            name = Path(c["path"]).stem
            detail = "; ".join(c["details"]) if c["details"] else "modified"
            lines.append(f"- **{name}** -- {detail}")
        lines.append("")

    if other_modified:
        lines.append("### Modified")
        for c in other_modified:
            name = Path(c["path"]).stem
            detail = "; ".join(c["details"]) if c["details"] else "content updated"
            lines.append(f"- **{name}** -- {detail}")
        lines.append("")

    # Deleted claims
    if digest["deleted"].get("claims"):
        lines.append("### Deleted")
        for p in digest["deleted"]["claims"]:
            lines.append(f"- ~~{Path(p).stem}~~")
        lines.append("")

    # Experiments
    if digest["added"].get("experiments") or digest["modified"].get("experiments"):
        lines.append("## Experiments")
        n_a = len(digest["added"].get("experiments", []))
        n_m = len(digest["modified"].get("experiments", []))
        if n_a:
            lines.append(f"- {n_a} new experiment notes added")
        if n_m:
            lines.append(f"- {n_m} experiment notes modified")
        lines.append("")

    # Sweeps
    if digest["added"].get("sweeps") or digest["modified"].get("sweeps"):
        lines.append("## Sweeps")
        for p in digest["added"].get("sweeps", []):
            lines.append(f"- **NEW** {Path(p).stem}")
        for p in digest["modified"].get("sweeps", []):
            lines.append(f"- modified {Path(p).stem}")
        lines.append("")

    # Other categories
    for cat in ("governance", "topologies", "failures", "methods"):
        added = digest["added"].get(cat, [])
        modified = digest["modified"].get(cat, [])
        deleted = digest["deleted"].get(cat, [])
        if not (added or modified or deleted):
            continue
        lines.append(f"## {CATEGORY_LABELS[cat]}")
        for p in added:
            lines.append(f"- **NEW** {Path(p).stem}")
        for p in modified:
            lines.append(f"- modified {Path(p).stem}")
        for p in deleted:
            lines.append(f"- ~~{Path(p).stem}~~ (deleted)")
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def format_json(digest: dict) -> str:
    """Render the digest as JSON."""
    return json.dumps(digest, indent=2, default=str) + "\n"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Generate a vault changelog between two git commits.",
        epilog="Examples:\n"
               "  vault-digest.py HEAD~5..HEAD\n"
               "  vault-digest.py --since '1 week ago'\n"
               "  vault-digest.py HEAD~1..HEAD --output vault/digests/digest.md\n",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "range", nargs="?", default=None,
        help="Git range, e.g. HEAD~5..HEAD or abc123..def456",
    )
    parser.add_argument(
        "--since", default=None,
        help="Show changes since date/time, e.g. '1 week ago' or '2026-02-18'",
    )
    parser.add_argument(
        "--output", "-o", default=None,
        help="Write digest to file instead of stdout",
    )
    parser.add_argument(
        "--json", action="store_true", dest="json_output",
        help="Output as JSON instead of markdown",
    )
    args = parser.parse_args()

    if not args.range and not args.since:
        parser.error("Provide a git range (A..B) or --since")

    # Verify we are in a git repo
    try:
        git("rev-parse", "--git-dir")
    except RuntimeError:
        print("Error: not a git repository", file=sys.stderr)
        sys.exit(1)

    try:
        start, end = resolve_refs(args.range, args.since)
    except (ValueError, RuntimeError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        sys.exit(1)

    try:
        digest = build_digest(start, end)
    except RuntimeError as exc:
        print(f"Error building digest: {exc}", file=sys.stderr)
        sys.exit(1)

    if args.json_output:
        output = format_json(digest)
    else:
        output = format_markdown(digest)

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(output, encoding="utf-8")
        print(f"Digest written to {out_path}")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
