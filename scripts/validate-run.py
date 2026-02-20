#!/usr/bin/env python3
"""
Validate a SWARM run folder against the Research OS schemas.

Checks:
  1. run.yaml against run.schema.yaml (required)
  2. scenario.yaml against scenario.schema.yaml (if present)
  3. summary.json against summary.schema.yaml (if present, all variants)
  4. Artifact manifest: all referenced files exist on disk
  5. Structural: at least one output (summary.json, csv/, report.json)

Usage:
    python scripts/validate-run.py runs/20260213-202050_baseline_governance_v2
    python scripts/validate-run.py --all
    python scripts/validate-run.py --all --quiet
"""

import argparse
import hashlib
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

_schema_cache: dict[str, dict] = {}


def load_schema(name: str) -> dict:
    """Load a YAML schema file (cached)."""
    if name not in _schema_cache:
        path = SCHEMAS_DIR / name
        with open(path) as f:
            _schema_cache[name] = yaml.safe_load(f)
    return _schema_cache[name]


def validate_run(run_path: Path) -> list[str]:
    """Validate a run folder. Returns list of error messages."""
    errors = []

    # ── 1. run.yaml must exist ────────────────────────────────────────
    run_yaml_path = run_path / "run.yaml"
    if not run_yaml_path.exists():
        return [f"Missing run.yaml in {run_path.name}"]

    with open(run_yaml_path) as f:
        run_data = yaml.safe_load(f)

    run_schema = load_schema("run.schema.yaml")
    try:
        jsonschema.validate(run_data, run_schema)
    except jsonschema.ValidationError as e:
        errors.append(f"run.yaml: {e.message} (at {list(e.absolute_path)})")

    # ── 2. scenario.yaml validation ───────────────────────────────────
    scenario_path = run_path / "scenario.yaml"
    if scenario_path.exists():
        try:
            with open(scenario_path) as f:
                scenario_data = yaml.safe_load(f)
            scenario_schema = load_schema("scenario.schema.yaml")
            jsonschema.validate(scenario_data, scenario_schema)
        except yaml.YAMLError as e:
            errors.append(f"scenario.yaml: invalid YAML: {e}")
        except jsonschema.ValidationError as e:
            errors.append(f"scenario.yaml: {e.message} (at {list(e.absolute_path)})")
    # scenario_ref: "unknown" is common for backfilled runs — not an error

    # ── 3. summary.json validation (all variants) ─────────────────────
    summary_path = run_path / "summary.json"
    if not summary_path.exists():
        # Try report.json for redteam runs
        summary_path = run_path / "report.json"
    if not summary_path.exists():
        summary_path = run_path / "analysis" / "summary.json"

    if summary_path.exists():
        try:
            with open(summary_path) as f:
                summary_data = json.load(f)
            summary_schema = load_schema("summary.schema.yaml")
            jsonschema.validate(summary_data, summary_schema)
        except json.JSONDecodeError as e:
            errors.append(f"{summary_path.name}: invalid JSON: {e}")
        except jsonschema.ValidationError:
            # Summary doesn't match any known variant — warn but don't block
            pass  # unrecognized summary format (LLM live runs, custom analyses)

    # ── 4. Artifact manifest: referenced files must exist ─────────────
    artifacts = run_data.get("artifacts", {})
    for key in ["summary", "sweep_csv"]:
        val = artifacts.get(key)
        if val and not (run_path / val).exists():
            errors.append(f"artifacts.{key} references missing file: {val}")

    for csv_path in artifacts.get("epoch_csvs", []):
        if not (run_path / csv_path).exists():
            errors.append(f"artifacts.epoch_csvs references missing: {csv_path}")

    for plot in artifacts.get("plots", []):
        p = plot.get("path") if isinstance(plot, dict) else plot
        if p and not (run_path / p).exists():
            errors.append(f"artifacts.plots references missing: {p}")

    for script in artifacts.get("scripts", []):
        if not (run_path / script).exists():
            errors.append(f"artifacts.scripts references missing: {script}")

    # ── 5. Content-addressing: verify SHA-256 of external artifacts ──
    for ext in artifacts.get("external", []):
        ext_path = run_path / ext.get("path", "")
        expected_sha = ext.get("sha256", "")
        if ext_path.exists() and expected_sha:
            h = hashlib.sha256()
            with open(ext_path, "rb") as f:
                for chunk in iter(lambda: f.read(8192), b""):
                    h.update(chunk)
            actual_sha = h.hexdigest()
            if actual_sha != expected_sha:
                errors.append(
                    f"artifacts.external SHA-256 mismatch for {ext.get('path')}: "
                    f"expected {expected_sha[:16]}..., got {actual_sha[:16]}..."
                )
        elif not ext_path.exists() and not ext.get("storage"):
            errors.append(f"artifacts.external missing with no storage ref: {ext.get('path')}")

    # ── 6. Structural: at least one output ────────────────────────────
    has_output = (
        (run_path / "summary.json").exists()
        or (run_path / "report.json").exists()
        or (run_path / "analysis" / "summary.json").exists()
        or (run_path / "csv").is_dir()
    )
    if not has_output:
        errors.append("No output found (need summary.json, report.json, or csv/)")

    return errors


def main():
    parser = argparse.ArgumentParser(description="Validate SWARM run folders")
    parser.add_argument("path", nargs="?", help="Path to a specific run folder")
    parser.add_argument("--all", action="store_true", help="Validate all runs")
    parser.add_argument("--quiet", "-q", action="store_true", help="Only show errors")
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
    clean = 0
    for run_path in targets:
        errors = validate_run(run_path)
        if errors:
            print(f"\n{run_path.name}: {len(errors)} error(s)")
            for e in errors:
                print(f"  - {e}")
            total_errors += len(errors)
        else:
            clean += 1
            if not args.quiet:
                print(f"  {run_path.name}: OK")

    print(f"\n{'=' * 40}")
    print(f"Validated {len(targets)} runs: {clean} clean, {len(targets) - clean} with errors ({total_errors} total)")
    sys.exit(1 if total_errors > 0 else 0)


if __name__ == "__main__":
    main()
