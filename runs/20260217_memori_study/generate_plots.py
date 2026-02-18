#!/usr/bin/env python
"""Phase 3: Generate plots for Memori study."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd

sys.path.insert(0, str(Path(__file__).parent.parent.parent))

RUN_DIR = Path(__file__).parent
CSV_PATH = RUN_DIR / "sweep_results.csv"
PLOT_DIR = RUN_DIR / "plots"


def main():
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    PLOT_DIR.mkdir(exist_ok=True)

    df = pd.read_csv(CSV_PATH)
    print(f"Loaded {len(df)} runs")

    # ---- Plot 1: Welfare vs tax rate (with 95% CI) ----
    fig, ax = plt.subplots(figsize=(8, 5))
    grouped = df.groupby("governance.transaction_tax_rate")["welfare"]
    means = grouped.mean()
    stds = grouped.std(ddof=1)
    n = grouped.count()
    ci95 = 1.96 * stds / np.sqrt(n)

    ax.bar(range(len(means)), means.values, yerr=ci95.values, capsize=5,
           color=["#4C78A8", "#F58518", "#E45756"], alpha=0.85)
    ax.set_xticks(range(len(means)))
    ax.set_xticklabels([f"{v:.0%}" for v in means.index])
    ax.set_xlabel("Transaction Tax Rate")
    ax.set_ylabel("Welfare (mean ± 95% CI)")
    ax.set_title("Welfare vs Transaction Tax Rate\n(LLM+Memori Agents)")
    plt.tight_layout()
    fig.savefig(PLOT_DIR / "welfare_vs_tax.png", dpi=150)
    plt.close(fig)
    print("  [1/6] welfare_vs_tax.png")

    # ---- Plot 2: Toxicity vs tax rate ----
    fig, ax = plt.subplots(figsize=(8, 5))
    grouped = df.groupby("governance.transaction_tax_rate")["toxicity_rate"]
    means = grouped.mean()
    stds = grouped.std(ddof=1)
    ci95 = 1.96 * stds / np.sqrt(grouped.count())

    ax.bar(range(len(means)), means.values, yerr=ci95.values, capsize=5,
           color=["#4C78A8", "#F58518", "#E45756"], alpha=0.85)
    ax.set_xticks(range(len(means)))
    ax.set_xticklabels([f"{v:.0%}" for v in means.index])
    ax.set_xlabel("Transaction Tax Rate")
    ax.set_ylabel("Toxicity Rate (mean ± 95% CI)")
    ax.set_title("Toxicity vs Transaction Tax Rate\n(LLM+Memori Agents)")
    plt.tight_layout()
    fig.savefig(PLOT_DIR / "toxicity_vs_tax.png", dpi=150)
    plt.close(fig)
    print("  [2/6] toxicity_vs_tax.png")

    # ---- Plot 3: Welfare vs circuit breaker ----
    fig, ax = plt.subplots(figsize=(6, 5))
    grouped = df.groupby("governance.circuit_breaker_enabled")["welfare"]
    means = grouped.mean()
    stds = grouped.std(ddof=1)
    ci95 = 1.96 * stds / np.sqrt(grouped.count())

    ax.bar(range(len(means)), means.values, yerr=ci95.values, capsize=5,
           color=["#E45756", "#59A14F"], alpha=0.85)
    ax.set_xticks(range(len(means)))
    ax.set_xticklabels(["Off", "On"])
    ax.set_xlabel("Circuit Breaker")
    ax.set_ylabel("Welfare (mean ± 95% CI)")
    ax.set_title("Welfare vs Circuit Breaker\n(LLM+Memori Agents)")
    plt.tight_layout()
    fig.savefig(PLOT_DIR / "welfare_vs_circuit_breaker.png", dpi=150)
    plt.close(fig)
    print("  [3/6] welfare_vs_circuit_breaker.png")

    # ---- Plot 4: Toxicity vs circuit breaker ----
    fig, ax = plt.subplots(figsize=(6, 5))
    grouped = df.groupby("governance.circuit_breaker_enabled")["toxicity_rate"]
    means = grouped.mean()
    stds = grouped.std(ddof=1)
    ci95 = 1.96 * stds / np.sqrt(grouped.count())

    ax.bar(range(len(means)), means.values, yerr=ci95.values, capsize=5,
           color=["#E45756", "#59A14F"], alpha=0.85)
    ax.set_xticks(range(len(means)))
    ax.set_xticklabels(["Off", "On"])
    ax.set_xlabel("Circuit Breaker")
    ax.set_ylabel("Toxicity Rate (mean ± 95% CI)")
    ax.set_title("Toxicity vs Circuit Breaker\n(LLM+Memori Agents)")
    plt.tight_layout()
    fig.savefig(PLOT_DIR / "toxicity_vs_circuit_breaker.png", dpi=150)
    plt.close(fig)
    print("  [4/6] toxicity_vs_circuit_breaker.png")

    # ---- Plot 5: Welfare-toxicity tradeoff scatter ----
    fig, ax = plt.subplots(figsize=(8, 6))
    for cb_val in [False, True]:
        subset = df[df["governance.circuit_breaker_enabled"] == cb_val]
        label = f"CB={'On' if cb_val else 'Off'}"
        marker = "o" if cb_val else "s"
        scatter = ax.scatter(
            subset["toxicity_rate"], subset["welfare"],
            c=subset["governance.transaction_tax_rate"],
            cmap="viridis", marker=marker, s=60, alpha=0.8,
            edgecolors="white", linewidth=0.5, label=label,
        )
    cbar = plt.colorbar(scatter, ax=ax)
    cbar.set_label("Tax Rate")
    ax.set_xlabel("Toxicity Rate")
    ax.set_ylabel("Welfare")
    ax.set_title("Welfare-Toxicity Tradeoff\n(LLM+Memori Agents)")
    ax.legend()
    plt.tight_layout()
    fig.savefig(PLOT_DIR / "welfare_toxicity_scatter.png", dpi=150)
    plt.close(fig)
    print("  [5/6] welfare_toxicity_scatter.png")

    # ---- Plot 6: Quality gap vs tax rate ----
    fig, ax = plt.subplots(figsize=(8, 5))
    grouped = df.groupby("governance.transaction_tax_rate")["quality_gap"]
    means = grouped.mean()
    stds = grouped.std(ddof=1)
    ci95 = 1.96 * stds / np.sqrt(grouped.count())

    ax.bar(range(len(means)), means.values, yerr=ci95.values, capsize=5,
           color=["#4C78A8", "#F58518", "#E45756"], alpha=0.85)
    ax.set_xticks(range(len(means)))
    ax.set_xticklabels([f"{v:.0%}" for v in means.index])
    ax.axhline(y=0, color="gray", linestyle="--", alpha=0.5)
    ax.set_xlabel("Transaction Tax Rate")
    ax.set_ylabel("Quality Gap (mean ± 95% CI)")
    ax.set_title("Quality Gap vs Transaction Tax Rate\n(Negative = Adverse Selection)")
    plt.tight_layout()
    fig.savefig(PLOT_DIR / "quality_gap_vs_tax.png", dpi=150)
    plt.close(fig)
    print("  [6/6] quality_gap_vs_tax.png")

    print(f"\nAll plots saved to {PLOT_DIR}/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
