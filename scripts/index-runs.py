#!/usr/bin/env python3
"""
Generate run-index.yaml from all run.yaml files in runs/.

Produces a searchable catalog of all runs without traversing the filesystem.
Per RESEARCH_OS_SPEC.md §3.

Usage:
    python scripts/index-runs.py
    python scripts/index-runs.py --json    # output as JSON instead
"""

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

import yaml


RUNS_DIR = Path(__file__).parent.parent / "runs"
INDEX_PATH = Path(__file__).parent.parent / "run-index.yaml"


def build_entry(run_path: Path) -> dict:
    """Build an index entry from a run folder."""
    run_yaml_path = run_path / "run.yaml"
    if not run_yaml_path.exists():
        return {
            "id": run_path.name,
            "type": "unknown",
            "tags": ["unmigrated"],
            "date": "unknown",
            "status": "unknown",
        }

    with open(run_yaml_path) as f:
        ry = yaml.safe_load(f)

    exp = ry.get("experiment", {})
    entry = {
        "id": ry["run_id"],
        "slug": ry.get("slug", ""),
        "type": exp["type"],
        "tags": ry["tags"],
        "date": ry["created_utc"][:10] if isinstance(ry.get("created_utc"), str) else "unknown",
        "status": ry["results"]["status"],
    }

    # Sweep-specific fields
    total = exp.get("total_runs")
    if total:
        entry["total_runs"] = total
    swept = exp.get("swept_parameters", {})
    if swept:
        n_configs = 1
        for vals in swept.values():
            if isinstance(vals, list):
                n_configs *= len(vals)
        entry["total_configs"] = n_configs

    # Primary result summary
    primary = ry.get("results", {}).get("primary_result")
    if primary:
        entry["primary_result"] = primary

    # Claims
    claims = ry.get("links", {}).get("claims", [])
    if claims:
        entry["claims"] = claims

    return entry


def main():
    parser = argparse.ArgumentParser(description="Generate run-index.yaml")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    if not RUNS_DIR.exists():
        print(f"Error: {RUNS_DIR} does not exist")
        return

    entries = []
    type_counts: dict[str, int] = {}

    for run_path in sorted(RUNS_DIR.iterdir()):
        if not run_path.is_dir() or run_path.name.startswith("_"):
            continue
        entry = build_entry(run_path)
        entries.append(entry)
        t = entry.get("type", "unknown")
        type_counts[t] = type_counts.get(t, 0) + 1

    index = {
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "total_runs": len(entries),
        "by_type": dict(sorted(type_counts.items())),
        "runs": entries,
    }

    if args.json:
        out_path = INDEX_PATH.with_suffix(".json")
        with open(out_path, "w") as f:
            json.dump(index, f, indent=2)
        print(f"Wrote {out_path} with {len(entries)} runs")
    else:
        with open(INDEX_PATH, "w") as f:
            yaml.dump(index, f, default_flow_style=False, sort_keys=False)
        print(f"Wrote {INDEX_PATH} with {len(entries)} runs")

    # Summary
    for t, count in sorted(type_counts.items()):
        print(f"  {t}: {count}")


if __name__ == "__main__":
    main()
