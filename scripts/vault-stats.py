#!/usr/bin/env python3
"""Vault statistics: count artifacts across all vault subdirectories.

Usage:
    python scripts/vault-stats.py          # human-readable table
    python scripts/vault-stats.py --json   # JSON output for CI
"""

import argparse
import json
import os
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    yaml = None

REPO_ROOT = Path(__file__).resolve().parent.parent
VAULT = REPO_ROOT / "vault"
RUNS = REPO_ROOT / "runs"

VAULT_DIRS = {
    "claims": VAULT / "claims",
    "experiments": VAULT / "experiments",
    "failures": VAULT / "failures",
    "governance": VAULT / "governance",
    "methods": VAULT / "methods",
    "sweeps": VAULT / "sweeps",
    "topologies": VAULT / "topologies",
}


def count_md(directory: Path) -> int:
    """Count markdown files in a directory (non-recursive)."""
    if not directory.is_dir():
        return 0
    return sum(1 for f in directory.iterdir() if f.suffix == ".md" and f.name != "_index.md")


def count_runs(directory: Path) -> int:
    """Count run directories (skip temp/hidden dirs)."""
    if not directory.is_dir():
        return 0
    return sum(
        1 for d in directory.iterdir()
        if d.is_dir() and not d.name.startswith("_") and not d.name.startswith(".")
    )


def parse_claim_confidences(claims_dir: Path) -> dict:
    """Parse confidence levels from claim frontmatter."""
    levels = {"high": 0, "medium": 0, "low": 0, "contested": 0, "unknown": 0}
    if not claims_dir.is_dir():
        return levels
    for f in claims_dir.glob("*.md"):
        if f.name == "_index.md":
            continue
        confidence = _extract_confidence(f)
        if confidence in levels:
            levels[confidence] += 1
        else:
            levels["unknown"] += 1
    return levels


def _extract_confidence(filepath: Path) -> str:
    """Extract confidence field from YAML frontmatter."""
    try:
        text = filepath.read_text(encoding="utf-8")
    except OSError:
        return "unknown"
    if not text.startswith("---"):
        return "unknown"
    parts = text.split("---", 2)
    if len(parts) < 3:
        return "unknown"
    front = parts[1]
    if yaml:
        try:
            meta = yaml.safe_load(front)
            return str(meta.get("confidence", "unknown")).lower()
        except Exception:
            pass
    # Fallback: regex-style line scan
    for line in front.splitlines():
        stripped = line.strip()
        if stripped.startswith("confidence:"):
            return stripped.split(":", 1)[1].strip().lower()
    return "unknown"


def gather_stats() -> dict:
    """Collect all vault statistics into a dict."""
    counts = {name: count_md(path) for name, path in VAULT_DIRS.items()}
    counts["runs"] = count_runs(RUNS)
    confidences = parse_claim_confidences(VAULT_DIRS["claims"])
    total_vault = sum(v for k, v in counts.items() if k != "runs")
    return {
        "counts": counts,
        "confidences": confidences,
        "total_vault_notes": total_vault,
    }


def print_human(stats: dict) -> None:
    """Print a human-readable summary."""
    c = stats["counts"]
    conf = stats["confidences"]
    print("=== Vault Statistics ===")
    print(f"  Claims:          {c['claims']:>4}  (high={conf['high']}, medium={conf['medium']}, low={conf['low']}, contested={conf['contested']})")
    print(f"  Experiments:     {c['experiments']:>4}")
    print(f"  Runs indexed:    {c['runs']:>4}")
    print(f"  Failure patterns:{c['failures']:>4}")
    print(f"  Governance:      {c['governance']:>4}")
    print(f"  Methods:         {c['methods']:>4}")
    print(f"  Sweeps:          {c['sweeps']:>4}")
    print(f"  Topologies:      {c.get('topologies', 0):>4}")
    print(f"  ────────────────────")
    print(f"  Total vault notes:{stats['total_vault_notes']:>3}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Vault statistics")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    stats = gather_stats()
    if args.json:
        json.dump(stats, sys.stdout, indent=2)
        print()
    else:
        print_human(stats)


if __name__ == "__main__":
    main()
