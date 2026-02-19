#!/usr/bin/env python3
"""
Backfill run.yaml metadata envelopes for existing SWARM runs.

Scans runs/ directory and generates a run.yaml for each run folder
that doesn't already have one, inferring metadata from folder name
and contents.

Usage:
    python scripts/backfill-run-yaml.py [--dry-run] [--run-id <specific-run>]
"""

import argparse
import hashlib
import json
import os
import re
from datetime import datetime, timezone
from pathlib import Path

import yaml


RUNS_DIR = Path(__file__).parent.parent / "runs"

# Patterns for inferring experiment type from folder contents
TYPE_SIGNALS = {
    "redteam": lambda files: any("report.json" in f for f in files),
    "calibration": lambda files: any("recommendation.json" in f for f in files),
    "study": lambda files: any("analysis" in f and os.path.isdir(f) for f in files)
                           or any("study" in os.path.basename(f).lower() for f in files if f.endswith("summary.json")),
    "sweep": lambda files: any("sweep_results.csv" in f or "sweep.csv" in f for f in files),
    "single": lambda files: any("history.json" in f for f in files),
}

# Tag extraction from folder name
TAG_KEYWORDS = [
    "baseline", "redteam", "adversarial", "sweep", "governance",
    "kernel", "market", "rlm", "collusion", "ldt", "cooperation",
    "acausality", "gastown", "pi", "bridge", "claude", "concordia",
    "delegation", "phylogeny", "tau", "calibration", "memori",
    "composition", "study", "reproduce", "analysis",
]


def parse_run_id(folder_name: str) -> dict:
    """Extract date, time, slug from folder name."""
    # Pattern: YYYYMMDD-HHMMSS_slug or YYYYMMDD_slug
    m = re.match(r"^(\d{8})-?(\d{6})?_?(.*)", folder_name)
    if not m:
        return {"date": None, "time": None, "slug": folder_name}

    date_str = m.group(1)
    time_str = m.group(2) or "000000"
    slug = m.group(3) or folder_name

    try:
        dt = datetime.strptime(f"{date_str}{time_str}", "%Y%m%d%H%M%S")
        dt = dt.replace(tzinfo=timezone.utc)
    except ValueError:
        dt = None

    return {"date": dt, "slug": slug}


def detect_type(run_path: Path) -> str:
    """Infer experiment type from folder contents and name."""
    # Name-based hint: folders ending in _study are studies
    if re.search(r"_study$", run_path.name):
        return "study"

    all_files = []
    for root, dirs, files in os.walk(run_path):
        for f in files:
            all_files.append(os.path.join(root, f))
        for d in dirs:
            all_files.append(os.path.join(root, d))

    for exp_type, detector in TYPE_SIGNALS.items():
        if detector(all_files):
            return exp_type
    return "single"


def extract_tags(slug: str) -> list[str]:
    """Extract tags from the slug."""
    slug_lower = slug.lower()
    tags = []
    for kw in TAG_KEYWORDS:
        if kw in slug_lower:
            tags.append(kw)

    # Extract seed if present
    seed_match = re.search(r"seed(\d+)", slug_lower)
    if seed_match:
        tags.append(f"seed-{seed_match.group(1)}")

    return tags or ["untagged"]


def sha256_file(path: Path) -> str:
    """Compute SHA-256 of a file."""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def inventory_artifacts(run_path: Path) -> dict:
    """Build the artifacts manifest for a run."""
    artifacts = {
        "summary": None,
        "sweep_csv": None,
        "epoch_csvs": [],
        "traces": [],
        "plots": [],
        "scripts": [],
        "external": [],
    }

    for item in sorted(run_path.rglob("*")):
        if not item.is_file():
            continue
        rel = str(item.relative_to(run_path))

        if item.name == "summary.json":
            artifacts["summary"] = rel
        elif item.name == "report.json":
            artifacts["summary"] = artifacts["summary"] or rel
        elif "sweep" in item.name and item.suffix == ".csv":
            artifacts["sweep_csv"] = rel
        elif item.suffix == ".csv":
            artifacts["epoch_csvs"].append(rel)
        elif item.suffix in (".png", ".html"):
            artifacts["plots"].append({"path": rel, "description": ""})
        elif item.suffix == ".py":
            artifacts["scripts"].append(rel)
        elif item.suffix in (".parquet", ".jsonl"):
            artifacts["traces"].append(rel)

    return {k: v for k, v in artifacts.items() if v}


def read_summary(run_path: Path) -> dict:
    """Try to read summary.json or report.json for results extraction."""
    for name in ["summary.json", "report.json"]:
        p = run_path / name
        if p.exists():
            try:
                with open(p) as f:
                    return json.load(f)
            except (json.JSONDecodeError, OSError):
                pass

    # Check analysis/summary.json
    p = run_path / "analysis" / "summary.json"
    if p.exists():
        try:
            with open(p) as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError):
            pass

    return {}


def build_run_yaml(run_path: Path) -> dict:
    """Build a run.yaml dict for the given run folder."""
    folder_name = run_path.name
    parsed = parse_run_id(folder_name)
    exp_type = detect_type(run_path)
    tags = extract_tags(parsed["slug"])
    artifacts = inventory_artifacts(run_path)
    summary = read_summary(run_path)

    created = parsed["date"]
    created_str = created.isoformat() if created else "unknown"

    # Extract seeds from summary if available
    seeds = summary.get("seeds", [])
    if not seeds:
        seed_match = re.search(r"seed(\d+)", folder_name)
        if seed_match:
            seeds = [int(seed_match.group(1))]

    # Extract swept parameters
    swept = summary.get("swept_parameters", {})

    # Build results
    results = {"status": "completed"}
    if "total_runs" in summary:
        results["total_hypotheses_tested"] = summary.get("total_hypotheses", 0)
        results["significant_findings"] = summary.get("n_bonferroni_significant", 0)
    if "robustness_score" in summary:
        results["primary_metric"] = "robustness_score"
        results["primary_result"] = f"Grade: {summary.get('grade', '?')}, score: {summary.get('robustness_score', '?')}"

    # Scenario ref
    scenario_ref = None
    scenario_sha = None
    if (run_path / "scenario.yaml").exists():
        scenario_ref = f"runs/{folder_name}/scenario.yaml"
        scenario_sha = sha256_file(run_path / "scenario.yaml")

    run_yaml = {
        "run_id": folder_name,
        "slug": parsed["slug"],
        "created_utc": created_str,
        "provenance": {
            "swarm_version": "unknown",
            "git_sha": "unknown",
            "git_dirty": False,
        },
        "experiment": {
            "type": exp_type,
            "scenario_ref": scenario_ref or "unknown",
            "seeds": seeds or [0],
        },
        "results": results,
        "artifacts": artifacts,
        "links": {
            "parent_runs": [],
            "child_runs": [],
            "claims": [],
        },
        "tags": tags,
    }

    if scenario_sha:
        run_yaml["experiment"]["scenario_sha256"] = scenario_sha
    if swept:
        run_yaml["experiment"]["swept_parameters"] = swept
    total = summary.get("total_runs")
    if total:
        run_yaml["experiment"]["total_runs"] = total

    return run_yaml


def main():
    parser = argparse.ArgumentParser(description="Backfill run.yaml for existing runs")
    parser.add_argument("--dry-run", action="store_true", help="Print but don't write")
    parser.add_argument("--run-id", type=str, help="Process only this specific run")
    parser.add_argument("--force", action="store_true", help="Overwrite existing run.yaml")
    args = parser.parse_args()

    if not RUNS_DIR.exists():
        print(f"Error: {RUNS_DIR} does not exist")
        return

    folders = sorted(RUNS_DIR.iterdir())
    if args.run_id:
        folders = [RUNS_DIR / args.run_id]

    created = 0
    skipped = 0
    errors = 0

    for run_path in folders:
        if not run_path.is_dir():
            continue

        target = run_path / "run.yaml"
        if target.exists() and not args.force:
            skipped += 1
            continue

        try:
            run_yaml = build_run_yaml(run_path)
        except Exception as e:
            print(f"  ERROR: {run_path.name}: {e}")
            errors += 1
            continue

        if args.dry_run:
            print(f"  WOULD CREATE: {target}")
            print(yaml.dump(run_yaml, default_flow_style=False, sort_keys=False)[:500])
            print("  ---")
        else:
            with open(target, "w") as f:
                yaml.dump(run_yaml, f, default_flow_style=False, sort_keys=False)
            print(f"  CREATED: {target}")

        created += 1

    print(f"\nDone: {created} created, {skipped} skipped, {errors} errors")


if __name__ == "__main__":
    main()
