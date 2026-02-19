#!/usr/bin/env python3
"""
Generate run-index.yaml from all run.yaml files in runs/.

Usage:
    python scripts/index-runs.py
"""

from datetime import datetime, timezone
from pathlib import Path

import yaml


RUNS_DIR = Path(__file__).parent.parent / "runs"
INDEX_PATH = Path(__file__).parent.parent / "run-index.yaml"


def main():
    entries = []

    for run_path in sorted(RUNS_DIR.iterdir()):
        if not run_path.is_dir():
            continue

        run_yaml_path = run_path / "run.yaml"
        if not run_yaml_path.exists():
            # Include un-migrated runs with minimal info
            entries.append({
                "id": run_path.name,
                "type": "unknown",
                "tags": ["unmigrated"],
                "date": "unknown",
                "status": "unknown",
            })
            continue

        with open(run_yaml_path) as f:
            ry = yaml.safe_load(f)

        entry = {
            "id": ry["run_id"],
            "type": ry["experiment"]["type"],
            "tags": ry["tags"],
            "date": ry["created_utc"][:10] if isinstance(ry["created_utc"], str) else "unknown",
            "status": ry["results"]["status"],
        }

        total = ry["experiment"].get("total_runs")
        if total:
            entry["total_runs"] = total

        claims = ry.get("links", {}).get("claims", [])
        if claims:
            entry["claims"] = claims

        entries.append(entry)

    index = {
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "total_runs": len(entries),
        "runs": entries,
    }

    with open(INDEX_PATH, "w") as f:
        yaml.dump(index, f, default_flow_style=False, sort_keys=False)

    print(f"Wrote {INDEX_PATH} with {len(entries)} runs")


if __name__ == "__main__":
    main()
