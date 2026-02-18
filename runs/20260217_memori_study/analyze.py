#!/usr/bin/env python
"""Phase 2: Statistical analysis of Memori study sweep results."""

import json
import sys
from itertools import combinations
from pathlib import Path

import numpy as np
import pandas as pd
from scipy import stats

RUN_DIR = Path(__file__).parent
CSV_PATH = RUN_DIR / "sweep_results.csv"
OUTPUT = RUN_DIR / "summary.json"


def _default(o):
    """Numpy-safe JSON serializer."""
    if isinstance(o, (np.bool_,)):
        return bool(o)
    if isinstance(o, (np.integer,)):
        return int(o)
    if isinstance(o, (np.floating,)):
        return float(o)
    raise TypeError(f"Object of type {type(o)} is not JSON serializable")


def cohens_d(a, b):
    """Compute Cohen's d effect size."""
    na, nb = len(a), len(b)
    pooled_std = np.sqrt(((na - 1) * a.std(ddof=1) ** 2 + (nb - 1) * b.std(ddof=1) ** 2) / (na + nb - 2))
    if pooled_std == 0:
        return 0.0
    return float((a.mean() - b.mean()) / pooled_std)


def pairwise_tests(df, group_col, metric_col):
    """Run pairwise Welch's t-test + Mann-Whitney U for a metric across groups."""
    groups = sorted(df[group_col].unique())
    results = []
    for g1, g2 in combinations(groups, 2):
        a = df[df[group_col] == g1][metric_col].values
        b = df[df[group_col] == g2][metric_col].values

        # Shapiro-Wilk normality
        sw_a = stats.shapiro(a) if len(a) >= 3 else (np.nan, np.nan)
        sw_b = stats.shapiro(b) if len(b) >= 3 else (np.nan, np.nan)

        # Welch's t-test
        t_stat, t_p = stats.ttest_ind(a, b, equal_var=False)

        # Mann-Whitney U
        u_stat, u_p = stats.mannwhitneyu(a, b, alternative="two-sided")

        d = cohens_d(a, b)

        results.append({
            "group_col": group_col,
            "metric": metric_col,
            "group_1": str(g1),
            "group_2": str(g2),
            "n_1": len(a),
            "n_2": len(b),
            "mean_1": float(a.mean()),
            "mean_2": float(b.mean()),
            "std_1": float(a.std(ddof=1)),
            "std_2": float(b.std(ddof=1)),
            "t_stat": float(t_stat),
            "t_p": float(t_p),
            "u_stat": float(u_stat),
            "u_p": float(u_p),
            "cohens_d": d,
            "shapiro_p_1": float(sw_a[1]) if not np.isnan(sw_a[1]) else None,
            "shapiro_p_2": float(sw_b[1]) if not np.isnan(sw_b[1]) else None,
        })
    return results


def apply_bonferroni(tests):
    """Apply Bonferroni and Holm-Bonferroni corrections."""
    n = len(tests)
    if n == 0:
        return tests
    for t in tests:
        t["bonferroni_p"] = min(t["t_p"] * n, 1.0)

    # Holm-Bonferroni
    sorted_tests = sorted(enumerate(tests), key=lambda x: x[1]["t_p"])
    for rank, (idx, _) in enumerate(sorted_tests):
        tests[idx]["holm_p"] = min(tests[idx]["t_p"] * (n - rank), 1.0)

    for t in tests:
        t["significant_bonferroni"] = t["bonferroni_p"] < 0.05
        t["significant_holm"] = t["holm_p"] < 0.05

    return tests


def main():
    print("=" * 60)
    print("Phase 2: Statistical Analysis")
    print("=" * 60)

    df = pd.read_csv(CSV_PATH)
    print(f"Loaded {len(df)} runs from {CSV_PATH.name}")
    print()

    all_tests = []

    # Test each swept parameter against welfare and toxicity
    for param_col in ["governance.transaction_tax_rate", "governance.circuit_breaker_enabled"]:
        for metric in ["welfare", "toxicity_rate", "quality_gap"]:
            tests = pairwise_tests(df, param_col, metric)
            all_tests.extend(tests)

    # Apply multiple comparisons correction
    all_tests = apply_bonferroni(all_tests)

    # Print results
    print(f"Total hypothesis tests: {len(all_tests)}")
    sig_bonf = sum(1 for t in all_tests if t["significant_bonferroni"])
    sig_holm = sum(1 for t in all_tests if t["significant_holm"])
    print(f"Significant (Bonferroni): {sig_bonf}")
    print(f"Significant (Holm):       {sig_holm}")
    print()

    print("Detailed results:")
    print(f"{'Param':<45} {'Metric':<15} {'G1 vs G2':<20} {'t':<8} {'p':<10} {'d':<8} {'Bonf':<8}")
    print("-" * 114)
    for t in all_tests:
        star = "*" if t["significant_bonferroni"] else ""
        print(
            f"{t['group_col']:<45} {t['metric']:<15} "
            f"{t['group_1']} vs {t['group_2']:<10} "
            f"{t['t_stat']:<8.3f} {t['t_p']:<10.4f} {t['cohens_d']:<8.3f} "
            f"{t['bonferroni_p']:<8.4f}{star}"
        )

    # Compute descriptive stats per config
    grouped = df.groupby(["governance.transaction_tax_rate", "governance.circuit_breaker_enabled"])
    desc_stats = []
    for (tax, cb), group in grouped:
        desc_stats.append({
            "tax_rate": tax,
            "circuit_breaker": cb,
            "n": len(group),
            "welfare_mean": float(group["welfare"].mean()),
            "welfare_std": float(group["welfare"].std(ddof=1)),
            "welfare_ci95": float(1.96 * group["welfare"].std(ddof=1) / np.sqrt(len(group))),
            "toxicity_mean": float(group["toxicity_rate"].mean()),
            "toxicity_std": float(group["toxicity_rate"].std(ddof=1)),
            "toxicity_ci95": float(1.96 * group["toxicity_rate"].std(ddof=1) / np.sqrt(len(group))),
            "quality_gap_mean": float(group["quality_gap"].mean()),
            "quality_gap_std": float(group["quality_gap"].std(ddof=1)),
            "honest_payoff_mean": float(group["honest_payoff"].mean()),
            "honest_payoff_std": float(group["honest_payoff"].std(ddof=1)),
        })

    summary = {
        "study": "memori_governance_sweep",
        "scenario": "llm_memori_openrouter_v1",
        "total_runs": len(df),
        "configurations": len(grouped),
        "seeds_per_config": 5,
        "epochs_per_run": 2,
        "steps_per_epoch": 5,
        "hypothesis_tests": len(all_tests),
        "significant_bonferroni": sig_bonf,
        "significant_holm": sig_holm,
        "descriptive_stats": desc_stats,
        "pairwise_tests": all_tests,
    }

    with open(OUTPUT, "w") as f:
        json.dump(summary, f, indent=2, default=_default)

    print(f"\nSaved summary to {OUTPUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
