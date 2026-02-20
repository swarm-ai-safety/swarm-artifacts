#!/usr/bin/env python3
"""
Cross-correlate parameter effects across sweep and study runs.

Detects parameter interactions, consistency patterns, and shared
effects across the SWARM experiment corpus.

Usage:
    python scripts/cross-correlate.py                              # full analysis
    python scripts/cross-correlate.py --json                       # JSON output
    python scripts/cross-correlate.py --parameter governance.transaction_tax_rate
    python scripts/cross-correlate.py --output vault/methods/cross-correlation.md
"""

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

import yaml


ROOT = Path(__file__).parent.parent
RUNS_DIR = ROOT / "runs"


# -- Helpers ----------------------------------------------------------------


def read_yaml(path: Path) -> dict:
    with open(path) as f:
        return yaml.safe_load(f) or {}


def read_json(path: Path) -> dict | list:
    with open(path) as f:
        return json.load(f)


def load_summary(run_path: Path, run_yaml: dict) -> dict | None:
    """Try to load summary.json or analysis/summary.json for a run."""
    # Explicit artifact path first
    summary_rel = run_yaml.get("artifacts", {}).get("summary")
    if summary_rel:
        p = run_path / summary_rel
        if p.exists():
            try:
                return read_json(p)
            except (json.JSONDecodeError, OSError):
                pass

    # Fallback paths
    for candidate in ["summary.json", "analysis/summary.json"]:
        p = run_path / candidate
        if p.exists():
            try:
                return read_json(p)
            except (json.JSONDecodeError, OSError):
                pass
    return None


def extract_swept_params(run_yaml: dict) -> list[str]:
    """Extract swept parameter names from run.yaml (dict or list format)."""
    swept = run_yaml.get("experiment", {}).get("swept_parameters")
    if swept is None:
        return []
    if isinstance(swept, list):
        return list(swept)
    if isinstance(swept, dict):
        return list(swept.keys())
    return []


# -- Data structures --------------------------------------------------------


class EffectRecord:
    """One parameter-metric effect observation from a single run."""
    __slots__ = ("run_id", "parameter", "metric", "effect_size",
                 "p_value", "significant", "direction")

    def __init__(self, run_id: str, parameter: str, metric: str,
                 effect_size: float, p_value: float, significant: bool):
        self.run_id = run_id
        self.parameter = parameter
        self.metric = metric
        self.effect_size = effect_size
        self.p_value = p_value
        self.significant = significant
        self.direction = "positive" if effect_size > 0 else "negative" if effect_size < 0 else "zero"


# -- Extraction -------------------------------------------------------------


def extract_effects_sweep(run_id: str, summary: dict) -> list[EffectRecord]:
    """Extract effects from a sweep summary.json."""
    records = []
    results = summary.get("results", [])
    if not isinstance(results, list):
        return records

    for r in results:
        param = r.get("parameter")
        metric = r.get("metric")
        effect = r.get("cohens_d") or r.get("effect_size")
        if param is None or metric is None or effect is None:
            continue

        p_val = r.get("t_p") or r.get("p_value", 1.0)
        sig = r.get("bonferroni_sig", False)

        records.append(EffectRecord(
            run_id=run_id, parameter=param, metric=metric,
            effect_size=float(effect), p_value=float(p_val),
            significant=bool(sig),
        ))
    return records


def extract_effects_study(run_id: str, summary: dict) -> list[EffectRecord]:
    """Extract effects from a study analysis/summary.json."""
    records = []
    tests = summary.get("pairwise_tests", [])
    if not isinstance(tests, list):
        return records

    for t in tests:
        metric = t.get("metric")
        effect = t.get("cohens_d") or t.get("effect_size")
        if metric is None or effect is None:
            continue

        # Parameter name: use group_col if present, else derive from comparison
        param = t.get("group_col") or t.get("parameter") or summary.get("parameter", "unknown")

        p_val = t.get("t_p") or t.get("p_value", 1.0)
        sig = t.get("bonferroni_sig") or t.get("significant_bonferroni", False)

        records.append(EffectRecord(
            run_id=run_id, parameter=param, metric=metric,
            effect_size=float(effect), p_value=float(p_val),
            significant=bool(sig),
        ))
    return records


# -- Scanning ---------------------------------------------------------------


def scan_runs() -> list[EffectRecord]:
    """Scan all sweep/study runs and extract effect records."""
    all_records = []

    if not RUNS_DIR.exists():
        print(f"Warning: {RUNS_DIR} does not exist", file=sys.stderr)
        return all_records

    for run_dir in sorted(RUNS_DIR.iterdir()):
        run_yaml_path = run_dir / "run.yaml"
        if not run_yaml_path.exists():
            continue

        try:
            run_yaml = read_yaml(run_yaml_path)
        except Exception:
            continue

        exp_type = run_yaml.get("experiment", {}).get("type", "")
        if exp_type not in ("sweep", "study"):
            continue

        run_id = run_yaml.get("run_id", run_dir.name)
        summary = load_summary(run_dir, run_yaml)
        if summary is None:
            continue

        if exp_type == "sweep":
            records = extract_effects_sweep(run_id, summary)
        else:
            records = extract_effects_study(run_id, summary)

        # If no parameter info in summary, try run.yaml swept_parameters
        if not records:
            continue

        # Supplement parameter names from run.yaml if needed
        swept = extract_swept_params(run_yaml)
        if swept:
            for rec in records:
                if rec.parameter == "unknown" and len(swept) == 1:
                    rec.parameter = swept[0]

        all_records.extend(records)

    return all_records


# -- Analysis ---------------------------------------------------------------


def build_param_frequency(records: list[EffectRecord]) -> dict[str, set[str]]:
    """Map parameter -> set of run_ids that tested it."""
    freq: dict[str, set[str]] = defaultdict(set)
    for r in records:
        freq[r.parameter].add(r.run_id)
    return dict(freq)


def build_effect_matrix(records: list[EffectRecord]) -> dict[str, dict[str, list[float]]]:
    """Build parameter x metric -> list of effect sizes."""
    matrix: dict[str, dict[str, list[float]]] = defaultdict(lambda: defaultdict(list))
    for r in records:
        matrix[r.parameter][r.metric].append(r.effect_size)
    return {p: dict(m) for p, m in matrix.items()}


def find_interaction_candidates(records: list[EffectRecord]) -> list[dict]:
    """Find parameter pairs with co-occurring significant effects in the same run."""
    # Group significant records by (run_id, metric)
    sig_by_run_metric: dict[tuple[str, str], set[str]] = defaultdict(set)
    for r in records:
        if r.significant:
            sig_by_run_metric[(r.run_id, r.metric)].add(r.parameter)

    # Find pairs
    interactions = []
    seen = set()
    for (run_id, metric), params in sig_by_run_metric.items():
        param_list = sorted(params)
        for i, a in enumerate(param_list):
            for b in param_list[i + 1:]:
                key = (a, b, metric)
                if key not in seen:
                    seen.add(key)
                    runs_with = [
                        rid for (rid, m), ps in sig_by_run_metric.items()
                        if m == metric and a in ps and b in ps
                    ]
                    interactions.append({
                        "param_a": a,
                        "param_b": b,
                        "metric": metric,
                        "co_occurring_runs": sorted(set(runs_with)),
                        "n_runs": len(set(runs_with)),
                    })

    return sorted(interactions, key=lambda x: -x["n_runs"])


def check_consistency(records: list[EffectRecord]) -> list[dict]:
    """Flag parameters with inconsistent effect directions across runs."""
    # Group by (parameter, metric) -> list of (run_id, direction, effect_size)
    groups: dict[tuple[str, str], list[EffectRecord]] = defaultdict(list)
    for r in records:
        if r.significant:
            groups[(r.parameter, r.metric)].append(r)

    flags = []
    for (param, metric), recs in groups.items():
        run_ids = set(r.run_id for r in recs)
        if len(run_ids) < 2:
            continue

        directions = set(r.direction for r in recs)
        effects = [r.effect_size for r in recs]
        mean_effect = sum(effects) / len(effects)
        spread = max(effects) - min(effects) if len(effects) > 1 else 0.0

        inconsistent = len(directions) > 1
        if inconsistent:
            flags.append({
                "parameter": param,
                "metric": metric,
                "n_runs": len(run_ids),
                "directions": sorted(directions),
                "mean_effect": round(mean_effect, 4),
                "spread": round(spread, 4),
                "status": "INCONSISTENT",
                "run_ids": sorted(run_ids),
            })
        elif spread > 2.0:
            flags.append({
                "parameter": param,
                "metric": metric,
                "n_runs": len(run_ids),
                "directions": sorted(directions),
                "mean_effect": round(mean_effect, 4),
                "spread": round(spread, 4),
                "status": "HIGH_VARIANCE",
                "run_ids": sorted(run_ids),
            })

    return sorted(flags, key=lambda x: (x["status"] != "INCONSISTENT", -x["spread"]))


# -- Output ----------------------------------------------------------------


def format_markdown(param_freq: dict, effect_matrix: dict,
                    interactions: list, consistency: list,
                    focus_param: str | None = None) -> str:
    """Generate the full markdown report."""
    lines = ["# Cross-correlation analysis", ""]
    total_params = len(param_freq)
    total_runs = len(set(r for runs in param_freq.values() for r in runs))
    lines.append(f"Analyzed **{total_params}** parameters across **{total_runs}** sweep/study runs.")
    lines.append("")

    # -- 1. Parameter frequency table
    lines.append("## Parameter frequency")
    lines.append("")
    lines.append("| Parameter | Runs | Run IDs |")
    lines.append("|-----------|------|---------|")
    for param in sorted(param_freq, key=lambda p: -len(param_freq[p])):
        if focus_param and param != focus_param:
            continue
        runs = param_freq[param]
        ids_str = ", ".join(sorted(runs))
        if len(ids_str) > 80:
            ids_str = ids_str[:77] + "..."
        lines.append(f"| `{param}` | {len(runs)} | {ids_str} |")
    lines.append("")

    # -- 2. Effect matrix
    lines.append("## Parameter-metric effect matrix")
    lines.append("")
    lines.append("Mean Cohen's d across runs (significant results only shown with *).")
    lines.append("")

    # Collect all metrics
    all_metrics = set()
    filtered_matrix = effect_matrix
    if focus_param:
        filtered_matrix = {p: m for p, m in effect_matrix.items() if p == focus_param}

    for param, metrics in filtered_matrix.items():
        all_metrics.update(metrics.keys())

    if all_metrics:
        metric_list = sorted(all_metrics)
        header = "| Parameter | " + " | ".join(f"`{m}`" for m in metric_list) + " |"
        sep = "|-----------|" + "|".join("-" * (len(m) + 4) for m in metric_list) + "|"
        lines.append(header)
        lines.append(sep)

        for param in sorted(filtered_matrix):
            cells = []
            for m in metric_list:
                effects = filtered_matrix[param].get(m, [])
                if effects:
                    mean_e = sum(effects) / len(effects)
                    cells.append(f"{mean_e:+.3f}")
                else:
                    cells.append("--")
            lines.append(f"| `{param}` | " + " | ".join(cells) + " |")
        lines.append("")
    else:
        lines.append("No effect data available.")
        lines.append("")

    # -- 3. Interaction candidates
    lines.append("## Interaction candidates")
    lines.append("")
    if interactions:
        lines.append("Parameter pairs with co-occurring Bonferroni-significant effects on the same metric:")
        lines.append("")
        lines.append("| Param A | Param B | Metric | Co-occurring runs |")
        lines.append("|---------|---------|--------|-------------------|")
        for ix in interactions:
            if focus_param and focus_param not in (ix["param_a"], ix["param_b"]):
                continue
            runs_str = ", ".join(ix["co_occurring_runs"])
            if len(runs_str) > 60:
                runs_str = runs_str[:57] + "..."
            lines.append(
                f"| `{ix['param_a']}` | `{ix['param_b']}` "
                f"| `{ix['metric']}` | {runs_str} |"
            )
        lines.append("")
        lines.append(
            "These pairs may exhibit interaction effects and warrant "
            "factorial analysis or dedicated interaction sweeps."
        )
    else:
        lines.append("No interaction candidates detected.")
    lines.append("")

    # -- 4. Consistency flags
    lines.append("## Cross-run consistency")
    lines.append("")
    if consistency:
        lines.append(
            "Parameters with inconsistent or high-variance effects across runs "
            "(potential moderator effects):"
        )
        lines.append("")
        lines.append("| Parameter | Metric | Status | Runs | Directions | Mean d | Spread |")
        lines.append("|-----------|--------|--------|------|------------|--------|--------|")
        for c in consistency:
            if focus_param and c["parameter"] != focus_param:
                continue
            dirs = ", ".join(c["directions"])
            lines.append(
                f"| `{c['parameter']}` | `{c['metric']}` "
                f"| {c['status']} | {c['n_runs']} "
                f"| {dirs} | {c['mean_effect']:+.4f} | {c['spread']:.4f} |"
            )
    else:
        lines.append("All cross-run effects are directionally consistent.")
    lines.append("")

    # -- Footer
    lines.append("---")
    lines.append("")
    lines.append("<!-- topics: cross-correlation, parameter-interactions, meta-analysis -->")
    lines.append("")
    return "\n".join(lines)


def format_json(param_freq: dict, effect_matrix: dict,
                interactions: list, consistency: list,
                focus_param: str | None = None) -> str:
    """Generate JSON output."""
    freq_serial = {p: sorted(runs) for p, runs in param_freq.items()}
    matrix_serial = {}
    for p, metrics in effect_matrix.items():
        matrix_serial[p] = {
            m: {"mean": round(sum(v) / len(v), 4), "n": len(v)}
            for m, v in metrics.items()
        }

    if focus_param:
        freq_serial = {p: r for p, r in freq_serial.items() if p == focus_param}
        matrix_serial = {p: m for p, m in matrix_serial.items() if p == focus_param}
        interactions = [
            ix for ix in interactions
            if focus_param in (ix["param_a"], ix["param_b"])
        ]
        consistency = [c for c in consistency if c["parameter"] == focus_param]

    result = {
        "parameter_frequency": freq_serial,
        "effect_matrix": matrix_serial,
        "interaction_candidates": interactions,
        "consistency_flags": consistency,
    }
    return json.dumps(result, indent=2, default=str)


# -- CLI --------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Cross-correlate parameter effects across SWARM sweep/study runs"
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output as JSON instead of markdown"
    )
    parser.add_argument(
        "--parameter", type=str, default=None,
        help="Focus analysis on a single parameter"
    )
    parser.add_argument(
        "--output", type=str, default=None,
        help="Write output to file instead of stdout"
    )
    args = parser.parse_args()

    records = scan_runs()
    if not records:
        print("No sweep/study data found.", file=sys.stderr)
        sys.exit(1)

    param_freq = build_param_frequency(records)
    effect_matrix = build_effect_matrix(records)
    interactions = find_interaction_candidates(records)
    consistency = check_consistency(records)

    if args.parameter and args.parameter not in param_freq:
        print(f"Parameter '{args.parameter}' not found in any run.", file=sys.stderr)
        print(f"Available: {', '.join(sorted(param_freq))}", file=sys.stderr)
        sys.exit(1)

    if args.json:
        output = format_json(param_freq, effect_matrix, interactions,
                             consistency, args.parameter)
    else:
        output = format_markdown(param_freq, effect_matrix, interactions,
                                 consistency, args.parameter)

    if args.output:
        out_path = ROOT / args.output if not Path(args.output).is_absolute() else Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(output)
        print(f"Wrote {len(output)} bytes to {out_path}", file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()
