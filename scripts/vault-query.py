#!/usr/bin/env python3
"""
Query the SWARM vault frontmatter — replicates Obsidian Dataview queries.

Usage:
    python scripts/vault-query.py                  # Run all suggestion queries
    python scripts/vault-query.py --query claims   # Just claims dashboard
    python scripts/vault-query.py --query suggestions
    python scripts/vault-query.py --json           # JSON output
"""

import argparse
import json
import sys
from datetime import datetime, timedelta
from pathlib import Path

import yaml

VAULT_DIR = Path(__file__).parent.parent / "vault"
STALE_DAYS = 14


def load_notes(folder: str | None = None) -> list[dict]:
    """Load all markdown notes with YAML frontmatter from vault."""
    root = VAULT_DIR / folder if folder else VAULT_DIR
    notes = []
    for md in root.rglob("*.md"):
        if ".obsidian" in md.parts or "templates" in md.parts:
            continue
        text = md.read_text(encoding="utf-8", errors="replace")
        if not text.startswith("---"):
            continue
        end = text.find("---", 3)
        if end == -1:
            continue
        try:
            fm = yaml.safe_load(text[3:end])
        except yaml.YAMLError:
            continue
        if not isinstance(fm, dict):
            continue
        fm["_path"] = str(md.relative_to(VAULT_DIR.parent))
        fm["_name"] = md.stem
        fm["_folder"] = str(md.parent.relative_to(VAULT_DIR))
        # count inlinks (simple wikilink grep across vault)
        fm["_file"] = md
        notes.append(fm)
    return notes


def count_inlinks(notes: list[dict]) -> dict[str, int]:
    """Count how many notes link to each note via [[wikilinks]]."""
    counts: dict[str, int] = {n["_name"]: 0 for n in notes}
    for n in notes:
        text = n["_file"].read_text(encoding="utf-8", errors="replace")
        for target in counts:
            if f"[[{target}]]" in text and target != n["_name"]:
                counts[target] += 1
    return counts


def fmt_table(headers: list[str], rows: list[list], max_col: int = 50) -> str:
    """Format a simple ASCII table."""
    if not rows:
        return "  (empty)\n"

    def trunc(v, m):
        s = str(v) if v is not None else ""
        return s[:m] + "..." if len(s) > m else s

    widths = [len(h) for h in headers]
    str_rows = []
    for row in rows:
        sr = [trunc(v, max_col) for v in row]
        for i, v in enumerate(sr):
            widths[i] = max(widths[i], len(v))
        str_rows.append(sr)

    sep = "  ".join("-" * w for w in widths)
    hdr = "  ".join(h.ljust(w) for h, w in zip(headers, widths))
    lines = [hdr, sep]
    for sr in str_rows:
        lines.append("  ".join(v.ljust(w) for v, w in zip(sr, widths)))
    return "\n".join(lines) + "\n"


def query_claims(notes: list[dict]) -> dict:
    """Claims dashboard queries."""
    claims = [n for n in notes if n.get("type") == "claim"]
    active = [c for c in claims if c.get("status") == "active"]

    by_confidence = {}
    for c in active:
        conf = c.get("confidence", "unknown")
        by_confidence.setdefault(conf, []).append(c)

    by_domain = {}
    for c in claims:
        d = c.get("domain", "unknown")
        by_domain.setdefault(d, []).append(c)

    return {
        "total": len(claims),
        "active": len(active),
        "by_confidence": {k: len(v) for k, v in by_confidence.items()},
        "by_domain": {k: len(v) for k, v in by_domain.items()},
        "claims": [
            {
                "name": c["_name"],
                "confidence": c.get("confidence"),
                "domain": c.get("domain"),
                "status": c.get("status"),
                "supporting": len(c.get("evidence", {}).get("supporting", [])),
            }
            for c in active
        ],
    }


def query_suggestions(notes: list[dict]) -> dict:
    """Replicate the suggestions dashboard queries."""
    claims = [n for n in notes if n.get("type") == "claim" and n.get("status") == "active"]
    experiments = [n for n in notes if n.get("type") == "experiment"]
    sweeps = [n for n in notes if n.get("type") == "sweep-summary"]
    failures = [n for n in notes if n.get("type") == "failure-pattern"]

    inlinks = count_inlinks(notes)
    today = datetime.now().date()

    # 1. Needs replication (<2 supporting runs)
    needs_replication = []
    for c in claims:
        sup = c.get("evidence", {}).get("supporting", [])
        if len(sup) < 2:
            needs_replication.append({
                "name": c["_name"],
                "confidence": c.get("confidence"),
                "domain": c.get("domain"),
                "runs": len(sup),
            })

    # 2. Stale claims (>14 days since update)
    stale = []
    for c in claims:
        updated = c.get("updated")
        if updated:
            try:
                if isinstance(updated, str):
                    ud = datetime.strptime(updated, "%Y-%m-%d").date()
                else:
                    ud = updated
                if (today - ud).days > STALE_DAYS:
                    stale.append({
                        "name": c["_name"],
                        "confidence": c.get("confidence"),
                        "updated": str(ud),
                        "days_ago": (today - ud).days,
                    })
            except (ValueError, TypeError):
                pass

    # 3. Untested boundary conditions
    boundary = []
    for c in claims:
        bc = c.get("evidence", {}).get("boundary_conditions", [])
        if bc:
            boundary.append({
                "name": c["_name"],
                "conditions": bc,
            })

    # 4. Unlinked experiments (no inlinks)
    unlinked_exp = []
    for e in experiments:
        if inlinks.get(e["_name"], 0) == 0:
            unlinked_exp.append({
                "name": e["_name"],
                "type": e.get("experiment_type", "unknown"),
                "created": str(e.get("created", "")),
            })

    # 5. Low confidence
    low_conf = [
        {"name": c["_name"], "domain": c.get("domain")}
        for c in claims
        if c.get("confidence") == "low"
    ]

    # 6. Contradictions by domain
    contradictions: dict[str, list] = {}
    for c in claims:
        d = c.get("domain", "unknown")
        contradictions.setdefault(d, []).append({
            "name": c["_name"],
            "confidence": c.get("confidence"),
            "description": c.get("description", ""),
        })
    # only domains with 2+ claims can have contradictions
    contradictions = {k: v for k, v in contradictions.items() if len(v) >= 2}

    # 7. Orphan notes
    orphans = []
    for n in notes:
        if n.get("type") == "dashboard" or "templates" in n.get("_folder", ""):
            continue
        name = n["_name"]
        text = n["_file"].read_text(encoding="utf-8", errors="replace")
        has_outlinks = "[[" in text.split("---", 2)[-1] if text.count("---") >= 2 else "[[" in text
        if inlinks.get(name, 0) == 0 and not has_outlinks:
            orphans.append({
                "name": name,
                "type": n.get("type"),
                "folder": n.get("_folder"),
            })

    # 8. Sweeps without claims (no inlinks)
    sweeps_no_claims = [
        {"name": s["_name"], "parameter": s.get("parameter", "")}
        for s in sweeps
        if inlinks.get(s["_name"], 0) == 0
    ]

    # 9. Critical failures still active
    critical_failures = [
        {"name": f["_name"], "severity": f.get("severity"), "status": f.get("status")}
        for f in failures
        if f.get("status") == "active"
        and f.get("severity") in ("critical", "high")
    ]

    return {
        "needs_replication": needs_replication,
        "stale_claims": stale,
        "boundary_conditions": boundary,
        "unlinked_experiments": unlinked_exp[:20],
        "low_confidence": low_conf,
        "contradiction_domains": contradictions,
        "orphan_notes": orphans,
        "sweeps_without_claims": sweeps_no_claims,
        "critical_failures": critical_failures,
    }


def print_suggestions(results: dict) -> None:
    """Pretty-print suggestion results."""
    print("=" * 60)
    print("  SWARM Vault — Suggestions")
    print("=" * 60)

    # Needs replication
    nr = results["needs_replication"]
    print(f"\n## Needs Replication ({len(nr)} claims with <2 supporting runs)\n")
    if nr:
        print(fmt_table(
            ["Claim", "Confidence", "Domain", "Runs"],
            [[r["name"], r["confidence"], r["domain"], r["runs"]] for r in nr],
        ))

    # Stale
    st = results["stale_claims"]
    print(f"\n## Stale Claims ({len(st)} not updated in {STALE_DAYS}+ days)\n")
    if st:
        print(fmt_table(
            ["Claim", "Confidence", "Last Updated", "Days Ago"],
            [[r["name"], r["confidence"], r["updated"], r["days_ago"]] for r in st],
        ))

    # Boundary conditions
    bc = results["boundary_conditions"]
    print(f"\n## Untested Boundary Conditions ({len(bc)} claims with known limits)\n")
    if bc:
        for r in bc:
            print(f"  {r['name']}:")
            for cond in r["conditions"]:
                print(f"    - {cond}")
            print()

    # Unlinked experiments
    ue = results["unlinked_experiments"]
    print(f"\n## Unlinked Experiments ({len(ue)} with no inlinks, showing top 20)\n")
    if ue:
        print(fmt_table(
            ["Experiment", "Type", "Created"],
            [[r["name"], r["type"], r["created"]] for r in ue[:20]],
        ))

    # Low confidence
    lc = results["low_confidence"]
    print(f"\n## Low-Confidence Claims ({len(lc)})\n")
    if lc:
        print(fmt_table(
            ["Claim", "Domain"],
            [[r["name"], r["domain"]] for r in lc],
        ))

    # Contradictions
    cd = results["contradiction_domains"]
    print(f"\n## Potential Contradictions ({len(cd)} domains with 2+ claims)\n")
    for domain, claims in cd.items():
        print(f"  ### {domain} ({len(claims)} claims)")
        for c in claims:
            desc = c["description"][:80] + "..." if len(c.get("description", "")) > 80 else c.get("description", "")
            print(f"    [{c['confidence']}] {c['name']}: {desc}")
        print()

    # Orphans
    orph = results["orphan_notes"]
    print(f"\n## Orphan Notes ({len(orph)} disconnected)\n")
    if orph:
        print(fmt_table(
            ["Note", "Type", "Folder"],
            [[r["name"], r["type"], r["folder"]] for r in orph],
        ))

    # Sweeps without claims
    sw = results["sweeps_without_claims"]
    print(f"\n## Sweeps Without Claims ({len(sw)})\n")
    if sw:
        print(fmt_table(
            ["Sweep", "Parameter"],
            [[r["name"], r["parameter"]] for r in sw],
        ))

    # Critical failures
    cf = results["critical_failures"]
    print(f"\n## Critical/High Failures Still Active ({len(cf)})\n")
    if cf:
        print(fmt_table(
            ["Pattern", "Severity", "Status"],
            [[r["name"], r["severity"], r["status"]] for r in cf],
        ))


def print_claims(results: dict) -> None:
    """Pretty-print claims dashboard."""
    print("=" * 60)
    print("  SWARM Vault — Claims Dashboard")
    print("=" * 60)

    print(f"\n  Total: {results['total']}  Active: {results['active']}")
    print(f"  By confidence: {results['by_confidence']}")
    print(f"  By domain: {results['by_domain']}\n")

    print(fmt_table(
        ["Claim", "Confidence", "Domain", "Status", "Evidence"],
        [
            [c["name"], c["confidence"], c["domain"], c["status"], c["supporting"]]
            for c in results["claims"]
        ],
    ))


def main():
    parser = argparse.ArgumentParser(description="Query SWARM vault frontmatter")
    parser.add_argument(
        "--query", "-q",
        choices=["suggestions", "claims", "all"],
        default="suggestions",
        help="Which dashboard to query (default: suggestions)",
    )
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    notes = load_notes()
    print(f"Loaded {len(notes)} notes from vault\n", file=sys.stderr)

    results = {}
    if args.query in ("suggestions", "all"):
        results["suggestions"] = query_suggestions(notes)
    if args.query in ("claims", "all"):
        results["claims"] = query_claims(notes)

    if args.json:
        # Strip non-serializable fields
        print(json.dumps(results, indent=2, default=str))
    else:
        if "claims" in results:
            print_claims(results["claims"])
        if "suggestions" in results:
            print_suggestions(results["suggestions"])


if __name__ == "__main__":
    main()
