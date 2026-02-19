#!/usr/bin/env python3
"""
Validate a SWARM run folder against the Research OS schemas.

Usage:
    python scripts/validate-run.py runs/20260213-202050_baseline_governance_v2
    python scripts/validate-run.py --all
"""

import argparse
import json
import sys
from pathlib import Path

import yaml

try:
    import jsonschema
except ImportError:
    print("Install jsonschema: pip install jsonschema")
    sys.exit(1)


SCHEMAS_DIR = Path(__file__).parent.parent / "schemas"
RUNS_DIR = Path(__file__).parent.parent / "runs"


def load_schema(name: str) -> dict:
    """Load a YAML schema file."""
    path = SCHEMAS_DIR / name
    with open(path) as f:
        return yaml.safe_load(f)


def validate_run(run_path: Path) -> list[str]:
    """Validate a run folder. Returns list of error messages."""
    errors = []

    # Check run.yaml exists
    run_yaml_path = run_path / "run.yaml"
    if not run_yaml_path.exists():
        return [f"Missing run.yaml in {run_path.name}"]

    # Load and validate run.yaml
    with open(run_yaml_path) as f:
        run_data = yaml.safe_load(f)

    run_schema = load_schema("run.schema.yaml")
    try:
        jsonschema.validate(run_data, run_schema)
    except jsonschema.ValidationError as e:
        errors.append(f"run.yaml: {e.message} (at {list(e.absolute_path)})")

    # Validate summary.json against sweep schema if it's a sweep
    if run_data.get("experiment", {}).get("type") == "sweep":
        summary_path = run_path / "summary.json"
        if summary_path.exists():
            with open(summary_path) as f:
                try:
                    summary_data = json.load(f)
                    sweep_schema = load_schema("sweep.schema.yaml")
                    jsonschema.validate(summary_data, sweep_schema)
                except json.JSONDecodeError as e:
                    errors.append(f"summary.json: invalid JSON: {e}")
                except jsonschema.ValidationError as e:
                    errors.append(f"summary.json: {e.message} (at {list(e.absolute_path)})")

    # Check that listed artifacts actually exist
    artifacts = run_data.get("artifacts", {})
    for key in ["summary", "sweep_csv"]:
        val = artifacts.get(key)
        if val and not (run_path / val).exists():
            errors.append(f"artifacts.{key} references missing file: {val}")

    for csv_path in artifacts.get("epoch_csvs", []):
        if not (run_path / csv_path).exists():
            errors.append(f"artifacts.epoch_csvs references missing file: {csv_path}")

    return errors


def main():
    parser = argparse.ArgumentParser(description="Validate SWARM run folders")
    parser.add_argument("path", nargs="?", help="Path to a specific run folder")
    parser.add_argument("--all", action="store_true", help="Validate all runs")
    args = parser.parse_args()

    if not args.path and not args.all:
        parser.print_help()
        return

    targets = []
    if args.all:
        targets = sorted(p for p in RUNS_DIR.iterdir() if p.is_dir())
    else:
        targets = [Path(args.path)]

    total_errors = 0
    for run_path in targets:
        errors = validate_run(run_path)
        if errors:
            print(f"\n{run_path.name}: {len(errors)} error(s)")
            for e in errors:
                print(f"  - {e}")
            total_errors += len(errors)
        else:
            print(f"  {run_path.name}: OK")

    print(f"\n{'=' * 40}")
    print(f"Validated {len(targets)} runs, {total_errors} total errors")
    sys.exit(1 if total_errors > 0 else 0)


if __name__ == "__main__":
    main()
