#!/usr/bin/env python3
"""
Vault health audit — comprehensive integrity check for the research vault.

Checks:
- Claim card schema compliance and confidence consistency
- Evidence provenance (run references exist)
- Wiki-link integrity (targets exist)
- Index consistency (orphaned notes, missing entries)
- Staleness (notes not updated in >30 days)

Usage:
    python scripts/vault-health.py              # human-readable output
    python scripts/vault-health.py --json       # JSON output for CI
"""

import argparse
import json
import re
import sys
from datetime import datetime, timedelta
from pathlib import Path

import yaml

ROOT = Path(__file__).parent.parent
VAULT_DIR = ROOT / "vault"
RUNS_DIR = ROOT / "runs"

STALE_THRESHOLD_DAYS = 30


def parse_frontmatter(path: Path) -> dict | None:
    text = path.read_text(encoding="utf-8")
    match = re.match(r"^---\n(.+?)\n---", text, re.DOTALL)
    if not match:
        return None
    data = yaml.safe_load(match.group(1))
    if data is None:
        return None
    # YAML parses bare dates as datetime.date — normalize to strings
    from datetime import date as date_type
    for key in ("created", "updated"):
        if key in data and isinstance(data[key], (date_type, datetime)):
            data[key] = data[key].isoformat()
    return data


def find_wiki_links(text: str) -> list[str]:
    """Extract [[wiki-link]] targets from markdown text."""
    return re.findall(r"\[\[([^\]]+)\]\]", text)


def audit_claims() -> dict:
    """Audit all claim cards."""
    claims_dir = VAULT_DIR / "claims"
    result = {
        "total": 0,
        "active": 0,
        "weakened": 0,
        "superseded": 0,
        "retracted": 0,
        "high_confidence": 0,
        "medium_confidence": 0,
        "low_confidence": 0,
        "contested": 0,
        "stale": 0,
        "stale_claims": [],
    }

    if not claims_dir.exists():
        return result

    today = datetime.now().date()

    for path in sorted(claims_dir.glob("*.md")):
        fm = parse_frontmatter(path)
        if fm is None:
            continue

        result["total"] += 1

        # Status counts
        status = fm.get("status", "unknown")
        if status in result:
            result[status] += 1

        # Confidence counts
        conf = fm.get("confidence", "unknown")
        conf_key = f"{conf}_confidence" if conf != "contested" else "contested"
        if conf_key in result:
            result[conf_key] += 1

        # Staleness
        updated = fm.get("updated") or fm.get("created")
        if updated:
            if isinstance(updated, str):
                try:
                    updated = datetime.strptime(updated, "%Y-%m-%d").date()
                except ValueError:
                    continue
            if (today - updated).days > STALE_THRESHOLD_DAYS:
                result["stale"] += 1
                result["stale_claims"].append(path.name)

    return result


def audit_evidence() -> dict:
    """Check that all evidence run references exist."""
    broken = []
    claims_dir = VAULT_DIR / "claims"

    if not claims_dir.exists():
        return {"broken_run_refs": broken}

    for path in sorted(claims_dir.glob("*.md")):
        fm = parse_frontmatter(path)
        if fm is None:
            continue

        evidence = fm.get("evidence", {})
        for kind in ["supporting", "weakening"]:
            for entry in evidence.get(kind, []):
                run_id = entry.get("run")
                if run_id and not (RUNS_DIR / run_id).exists():
                    broken.append({
                        "claim": path.name,
                        "run_id": run_id,
                        "evidence_type": kind,
                    })

    return {"broken_run_refs": broken}


def audit_wiki_links() -> dict:
    """Check that all wiki-links resolve to existing notes."""
    broken = []
    # Build a set of all note stems across vault subdirs
    note_stems = set()
    for md in VAULT_DIR.rglob("*.md"):
        note_stems.add(md.stem)

    # Also accept stems without prefix for claim references
    claims_dir = VAULT_DIR / "claims"
    if claims_dir.exists():
        for md in claims_dir.glob("*.md"):
            # "claim-circuit-breakers-dominate" is the stem
            note_stems.add(md.stem)

    # Skip templates directory — those contain placeholder links
    templates_dir = VAULT_DIR / "templates"

    for md in VAULT_DIR.rglob("*.md"):
        # Skip templates — they contain placeholder wiki-links like [[claim-id]]
        if templates_dir.exists() and md.is_relative_to(templates_dir):
            continue

        text = md.read_text(encoding="utf-8")
        for target in find_wiki_links(text):
            # Normalize: strip any path, just use the link text
            target_clean = target.split("|")[0].strip()
            # Check if target exists as a note stem or as a run folder
            if (
                target_clean not in note_stems
                and target_clean.replace(" ", "-") not in note_stems
                and not (RUNS_DIR / target_clean).exists()
            ):
                broken.append({
                    "file": str(md.relative_to(ROOT)),
                    "target": target_clean,
                })

    return {"broken": broken}


def audit_index() -> dict:
    """Check index consistency — orphaned notes not in _index.md."""
    orphaned = []
    index_path = VAULT_DIR / "_index.md"

    if not index_path.exists():
        return {"orphaned_notes": [], "missing_index": True}

    index_text = index_path.read_text(encoding="utf-8")

    for subdir in ["claims", "experiments", "governance", "topologies", "failures", "methods", "sweeps"]:
        dir_path = VAULT_DIR / subdir
        if not dir_path.exists():
            continue
        for md in sorted(dir_path.glob("*.md")):
            if md.stem not in index_text:
                orphaned.append(str(md.relative_to(ROOT)))

    return {"orphaned_notes": orphaned, "missing_index": False}


def main():
    parser = argparse.ArgumentParser(description="Vault health audit")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    report = {
        "claims": audit_claims(),
        "evidence": audit_evidence(),
        "wiki_links": audit_wiki_links(),
        "index": audit_index(),
        "generated_utc": datetime.now().astimezone().isoformat(),
    }

    if args.json:
        print(json.dumps(report, indent=2, default=str))
    else:
        c = report["claims"]
        print("## Vault Health Report\n")
        print(f"### Claims ({c['total']} total)")
        print(f"  Active: {c['active']}  |  Weakened: {c['weakened']}  |  Superseded: {c['superseded']}  |  Retracted: {c['retracted']}")
        print(f"  High: {c['high_confidence']}  |  Medium: {c['medium_confidence']}  |  Low: {c['low_confidence']}  |  Contested: {c['contested']}")
        print(f"  Stale (>{STALE_THRESHOLD_DAYS}d): {c['stale']}")

        broken_refs = report["evidence"]["broken_run_refs"]
        print(f"\n### Evidence integrity")
        print(f"  Broken run references: {len(broken_refs)}")
        for ref in broken_refs:
            print(f"    - {ref['claim']}: {ref['run_id']} ({ref['evidence_type']})")

        broken_links = report["wiki_links"]["broken"]
        print(f"\n### Wiki-links")
        print(f"  Broken links: {len(broken_links)}")
        for link in broken_links:
            print(f"    - {link['file']}: [[{link['target']}]]")

        orphaned = report["index"]["orphaned_notes"]
        print(f"\n### Index consistency")
        print(f"  Orphaned notes: {len(orphaned)}")
        for note in orphaned:
            print(f"    - {note}")

        # Exit code
        total_errors = len(broken_refs) + len(broken_links) + len(orphaned)
        if total_errors > 0:
            print(f"\n{total_errors} integrity error(s) found")
            sys.exit(1)
        else:
            print("\nAll checks passed")


if __name__ == "__main__":
    main()
