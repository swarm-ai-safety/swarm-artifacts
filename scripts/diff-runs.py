#!/usr/bin/env python3
"""
Compare two SWARM runs side-by-side.

Shows parameter differences, metric deltas, effect sizes, and
claim overlap for two runs.

Usage:
    python scripts/diff-runs.py <run_id_1> <run_id_2>
    python scripts/diff-runs.py <run_id_1> <run_id_2> --json
    python scripts/diff-runs.py <run_id_1> <run_id_2> --metric welfare
"""

import argparse
import json
import re
import sys
from pathlib import Path

import yaml


ROOT = Path(__file__).parent.parent
RUNS_DIR = ROOT / "runs"
VAULT_DIR = ROOT / "vault"


# ── Helpers ──────────────────────────────────────────────────────────────


def read_yaml(path: Path) -> dict:
    with open(path) as f:
        return yaml.safe_load(f) or {}


def read_json(path: Path) -> dict | list:
    with open(path) as f:
        return json.load(f)


def load_run(run_id: str) -> dict:
    """Load run.yaml and available summary data for a run."""
    run_path = RUNS_DIR / run_id
    if not run_path.exists():
        print(f"Error: {run_path} does not exist", file=sys.stderr)
        sys.exit(1)

    run_yaml_path = run_path / "run.yaml"
    if not run_yaml_path.exists():
        print(f"Error: {run_id} has no run.yaml", file=sys.stderr)
        sys.exit(1)

    data = read_yaml(run_yaml_path)
    data["_path"] = run_path

    # Load summary data
    exp_type = data.get("experiment", {}).get("type", "single")
    summary = {}

    summary_rel = data.get("artifacts", {}).get("summary")
    if summary_rel:
        summary_path = run_path / summary_rel
        if summary_path.exists():
            raw = read_json(summary_path)
            if isinstance(raw, dict):
                summary = raw
            # Handle nested robustness key in redteam reports
            if "robustness" in summary:
                summary = {**summary, **summary.get("robustness", {})}

    # Also try analysis/summary.json for studies
    if not summary and exp_type == "study":
        analysis_path = run_path / "analysis" / "summary.json"
        if analysis_path.exists():
            summary = read_json(analysis_path)

    # Load history.json for single runs
    if exp_type == "single":
        history_path = run_path / "history.json"
        if history_path.exists():
            raw = read_json(history_path)
            if isinstance(raw, dict):
                snapshots = raw.get("epoch_snapshots", [])
                if snapshots:
                    final = snapshots[-1]
                    summary["welfare"] = final.get("total_welfare")
                    summary["toxicity_rate"] = final.get("toxicity_rate")
                    summary["quality_gap"] = final.get("quality_gap")
                    summary["n_agents"] = raw.get("n_agents")
                    summary["seed"] = raw.get("seed")

    data["_summary"] = summary
    return data


def extract_metrics(run: dict) -> dict[str, float]:
    """Extract all numeric metrics from a run's summary."""
    summary = run.get("_summary", {})
    metrics = {}

    # Direct numeric fields
    for key, val in summary.items():
        if isinstance(val, (int, float)) and not key.startswith("_"):
            metrics[key] = float(val)

    # Sweep: extract top-line stats
    if "total_runs" in summary:
        metrics["total_runs"] = summary["total_runs"]
    if "total_hypotheses" in summary:
        metrics["total_hypotheses"] = summary["total_hypotheses"]
    if "n_bonferroni_significant" in summary:
        metrics["bonferroni_significant"] = summary["n_bonferroni_significant"]

    # Redteam
    if "robustness_score" in summary:
        metrics["robustness_score"] = summary["robustness_score"]
    if "attacks_tested" in summary:
        metrics["attacks_tested"] = summary["attacks_tested"]
    if "attacks_successful" in summary:
        metrics["attacks_successful"] = summary["attacks_successful"]

    # Study descriptive
    descriptive = summary.get("descriptive") or summary.get("descriptive_stats")
    if isinstance(descriptive, dict):
        for condition, stats in descriptive.items():
            if isinstance(stats, dict):
                for stat_key, stat_val in stats.items():
                    if isinstance(stat_val, (int, float)):
                        metrics[f"{condition}.{stat_key}"] = float(stat_val)

    return metrics


def extract_params(run: dict) -> dict:
    """Extract experiment parameters for comparison."""
    exp = run.get("experiment", {})
    params = {}

    params["type"] = exp.get("type", "unknown")
    params["scenario_ref"] = exp.get("scenario_ref", "unknown")
    params["seeds"] = exp.get("seeds", [])
    params["total_runs"] = exp.get("total_runs")

    swept = exp.get("swept_parameters", {})
    for k, v in swept.items():
        params[f"swept.{k}"] = v

    return params


def diff_params(params_a: dict, params_b: dict) -> list[dict]:
    """Compare parameters between two runs."""
    all_keys = sorted(set(params_a.keys()) | set(params_b.keys()))
    diffs = []

    for key in all_keys:
        val_a = params_a.get(key)
        val_b = params_b.get(key)
        if val_a != val_b:
            diffs.append({
                "parameter": key,
                "run_a": val_a,
                "run_b": val_b,
            })

    return diffs


def diff_metrics(metrics_a: dict, metrics_b: dict, focus_metric: str | None = None) -> list[dict]:
    """Compare metrics between two runs."""
    if focus_metric:
        all_keys = sorted(k for k in set(metrics_a.keys()) | set(metrics_b.keys()) if focus_metric in k.lower())
    else:
        all_keys = sorted(set(metrics_a.keys()) | set(metrics_b.keys()))

    diffs = []
    for key in all_keys:
        val_a = metrics_a.get(key)
        val_b = metrics_b.get(key)

        if val_a is None and val_b is None:
            continue

        entry = {
            "metric": key,
            "run_a": val_a,
            "run_b": val_b,
        }

        # Compute delta and pct change if both are numeric
        if val_a is not None and val_b is not None:
            delta = val_b - val_a
            entry["delta"] = delta
            if val_a != 0:
                entry["pct_change"] = (delta / abs(val_a)) * 100
            else:
                entry["pct_change"] = None
        else:
            entry["delta"] = None
            entry["pct_change"] = None

        diffs.append(entry)

    return diffs


def find_shared_claims(run_a: dict, run_b: dict) -> dict:
    """Find claims linked to either run."""
    claims_a = set(run_a.get("links", {}).get("claims", []))
    claims_b = set(run_b.get("links", {}).get("claims", []))

    return {
        "shared": sorted(claims_a & claims_b),
        "only_a": sorted(claims_a - claims_b),
        "only_b": sorted(claims_b - claims_a),
    }


def find_tag_overlap(run_a: dict, run_b: dict) -> dict:
    """Compare tags between runs."""
    tags_a = set(run_a.get("tags", []))
    tags_b = set(run_b.get("tags", []))

    return {
        "shared": sorted(tags_a & tags_b),
        "only_a": sorted(tags_a - tags_b),
        "only_b": sorted(tags_b - tags_a),
    }


# ── Output formatting ───────────────────────────────────────────────────


def print_table(run_a: dict, run_b: dict, param_diffs: list, metric_diffs: list, claims: dict, tags: dict):
    """Print a formatted comparison table."""
    id_a = run_a.get("run_id", "?")
    id_b = run_b.get("run_id", "?")
    type_a = run_a.get("experiment", {}).get("type", "?")
    type_b = run_b.get("experiment", {}).get("type", "?")

    print(f"\n{'=' * 80}")
    print(f"  Run comparison")
    print(f"{'=' * 80}")
    print(f"  A: {id_a} ({type_a})")
    print(f"  B: {id_b} ({type_b})")
    print(f"{'=' * 80}")

    # Parameter diffs
    if param_diffs:
        print(f"\n## Parameter differences ({len(param_diffs)})\n")
        print(f"  {'Parameter':<35} {'Run A':<20} {'Run B':<20}")
        print(f"  {'─' * 35} {'─' * 20} {'─' * 20}")
        for d in param_diffs:
            a_str = str(d["run_a"])[:20]
            b_str = str(d["run_b"])[:20]
            print(f"  {d['parameter']:<35} {a_str:<20} {b_str:<20}")
    else:
        print("\n## Parameters: identical")

    # Metric diffs
    if metric_diffs:
        print(f"\n## Metric comparison ({len(metric_diffs)})\n")
        print(f"  {'Metric':<35} {'Run A':>12} {'Run B':>12} {'Delta':>12} {'%Change':>10}")
        print(f"  {'─' * 35} {'─' * 12} {'─' * 12} {'─' * 12} {'─' * 10}")
        for d in metric_diffs:
            a_str = f"{d['run_a']:.4f}" if d["run_a"] is not None else "—"
            b_str = f"{d['run_b']:.4f}" if d["run_b"] is not None else "—"
            delta_str = f"{d['delta']:+.4f}" if d["delta"] is not None else "—"
            pct_str = f"{d['pct_change']:+.1f}%" if d["pct_change"] is not None else "—"
            print(f"  {d['metric']:<35} {a_str:>12} {b_str:>12} {delta_str:>12} {pct_str:>10}")
    else:
        print("\n## Metrics: no comparable metrics found")

    # Claims
    print(f"\n## Claims")
    if claims["shared"]:
        print(f"  Shared: {', '.join(claims['shared'])}")
    if claims["only_a"]:
        print(f"  Only A: {', '.join(claims['only_a'])}")
    if claims["only_b"]:
        print(f"  Only B: {', '.join(claims['only_b'])}")
    if not any(claims.values()):
        print("  No claims linked to either run")

    # Tags
    print(f"\n## Tags")
    print(f"  Shared: {', '.join(tags['shared']) or '—'}")
    if tags["only_a"]:
        print(f"  Only A: {', '.join(tags['only_a'])}")
    if tags["only_b"]:
        print(f"  Only B: {', '.join(tags['only_b'])}")

    print()


def output_json(run_a: dict, run_b: dict, param_diffs: list, metric_diffs: list, claims: dict, tags: dict):
    """Output comparison as JSON."""
    result = {
        "run_a": {
            "run_id": run_a.get("run_id"),
            "type": run_a.get("experiment", {}).get("type"),
            "created": run_a.get("created_utc"),
        },
        "run_b": {
            "run_id": run_b.get("run_id"),
            "type": run_b.get("experiment", {}).get("type"),
            "created": run_b.get("created_utc"),
        },
        "parameter_diffs": param_diffs,
        "metric_diffs": metric_diffs,
        "claims": claims,
        "tags": tags,
    }
    print(json.dumps(result, indent=2, default=str))


# ── CLI ──────────────────────────────────────────────────────────────────


def main():
    parser = argparse.ArgumentParser(description="Compare two SWARM runs")
    parser.add_argument("run_a", help="First run ID")
    parser.add_argument("run_b", help="Second run ID")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    parser.add_argument("--metric", type=str, help="Focus on a specific metric (substring match)")
    args = parser.parse_args()

    run_a = load_run(args.run_a)
    run_b = load_run(args.run_b)

    params_a = extract_params(run_a)
    params_b = extract_params(run_b)
    param_diffs = diff_params(params_a, params_b)

    metrics_a = extract_metrics(run_a)
    metrics_b = extract_metrics(run_b)
    metric_diffs = diff_metrics(metrics_a, metrics_b, args.metric)

    claims = find_shared_claims(run_a, run_b)
    tags = find_tag_overlap(run_a, run_b)

    if args.json:
        output_json(run_a, run_b, param_diffs, metric_diffs, claims, tags)
    else:
        print_table(run_a, run_b, param_diffs, metric_diffs, claims, tags)


if __name__ == "__main__":
    main()
