#!/usr/bin/env python3
"""Generate plots for composition boundary study."""

import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "../.."))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

RUN_DIR = os.path.dirname(os.path.abspath(__file__))
PLOTS_DIR = os.path.join(RUN_DIR, "plots")

COLORS = {
    "none": "#e74c3c",
    "basic": "#f39c12",
    "moderate": "#3498db",
    "full": "#2ecc71",
}

GOV_LABELS = {
    "none": "No governance",
    "basic": "Basic (CB)",
    "moderate": "Moderate (CB+audit)",
    "full": "Full (CB+audit+stake+collusion)",
}


def load_data():
    adv = pd.read_csv(os.path.join(RUN_DIR, "csv", "adversarial_sweep.csv"))
    prof = pd.read_csv(os.path.join(RUN_DIR, "csv", "profile_sweep.csv"))
    return adv, prof


def plot_acceptance_vs_adversarial(df):
    """Fig 1: Acceptance rate vs adversarial fraction, by governance."""
    fig, ax = plt.subplots(figsize=(10, 6))

    for gov in ["none", "basic", "moderate", "full"]:
        sub = df[df["governance"] == gov]
        grouped = sub.groupby("adversarial_fraction")["acceptance_rate"]
        means = grouped.mean()
        stds = grouped.std()
        ci95 = 1.96 * stds / np.sqrt(grouped.count())

        ax.plot(means.index, means.values, "o-",
                color=COLORS[gov], label=GOV_LABELS[gov], linewidth=2)
        ax.fill_between(means.index,
                        (means - ci95).values,
                        (means + ci95).values,
                        color=COLORS[gov], alpha=0.15)

    ax.axhline(y=0.85, color="gray", linestyle="--", alpha=0.5,
               label="Cooperative threshold")
    ax.axhline(y=0.30, color="gray", linestyle=":", alpha=0.5,
               label="Collapse threshold")
    ax.set_xlabel("Adversarial Fraction", fontsize=13)
    ax.set_ylabel("Acceptance Rate", fontsize=13)
    ax.set_title("Acceptance Rate vs Adversarial Fraction", fontsize=14)
    ax.legend(fontsize=10, loc="lower left")
    ax.set_ylim(-0.05, 1.05)
    ax.grid(True, alpha=0.3)

    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS_DIR, "acceptance_vs_adversarial.png"), dpi=150)
    plt.close(fig)
    print("  Plot: acceptance_vs_adversarial.png")


def plot_toxicity_vs_adversarial(df):
    """Fig 2: Toxicity vs adversarial fraction, by governance."""
    fig, ax = plt.subplots(figsize=(10, 6))

    for gov in ["none", "basic", "moderate", "full"]:
        sub = df[df["governance"] == gov]
        grouped = sub.groupby("adversarial_fraction")["toxicity"]
        means = grouped.mean()
        ci95 = 1.96 * grouped.std() / np.sqrt(grouped.count())

        ax.plot(means.index, means.values, "o-",
                color=COLORS[gov], label=GOV_LABELS[gov], linewidth=2)
        ax.fill_between(means.index,
                        (means - ci95).values,
                        (means + ci95).values,
                        color=COLORS[gov], alpha=0.15)

    ax.axhline(y=0.50, color="gray", linestyle=":", alpha=0.5,
               label="Collapse toxicity threshold")
    ax.set_xlabel("Adversarial Fraction", fontsize=13)
    ax.set_ylabel("Toxicity E[1-p | accepted]", fontsize=13)
    ax.set_title("Toxicity vs Adversarial Fraction", fontsize=14)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS_DIR, "toxicity_vs_adversarial.png"), dpi=150)
    plt.close(fig)
    print("  Plot: toxicity_vs_adversarial.png")


def plot_welfare_vs_adversarial(df):
    """Fig 3: Welfare vs adversarial fraction, by governance."""
    fig, ax = plt.subplots(figsize=(10, 6))

    for gov in ["none", "basic", "moderate", "full"]:
        sub = df[df["governance"] == gov]
        grouped = sub.groupby("adversarial_fraction")["welfare"]
        means = grouped.mean()
        ci95 = 1.96 * grouped.std() / np.sqrt(grouped.count())

        ax.plot(means.index, means.values, "o-",
                color=COLORS[gov], label=GOV_LABELS[gov], linewidth=2)
        ax.fill_between(means.index,
                        (means - ci95).values,
                        (means + ci95).values,
                        color=COLORS[gov], alpha=0.15)

    ax.set_xlabel("Adversarial Fraction", fontsize=13)
    ax.set_ylabel("Mean Welfare (tail epochs)", fontsize=13)
    ax.set_title("Welfare vs Adversarial Fraction", fontsize=14)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS_DIR, "welfare_vs_adversarial.png"), dpi=150)
    plt.close(fig)
    print("  Plot: welfare_vs_adversarial.png")


def plot_quality_gap_vs_adversarial(df):
    """Fig 4: Quality gap vs adversarial fraction."""
    fig, ax = plt.subplots(figsize=(10, 6))

    for gov in ["none", "basic", "moderate", "full"]:
        sub = df[df["governance"] == gov]
        grouped = sub.groupby("adversarial_fraction")["quality_gap"]
        means = grouped.mean()
        ci95 = 1.96 * grouped.std() / np.sqrt(grouped.count())

        ax.plot(means.index, means.values, "o-",
                color=COLORS[gov], label=GOV_LABELS[gov], linewidth=2)
        ax.fill_between(means.index,
                        (means - ci95).values,
                        (means + ci95).values,
                        color=COLORS[gov], alpha=0.15)

    ax.axhline(y=0.0, color="black", linestyle="-", alpha=0.3)
    ax.set_xlabel("Adversarial Fraction", fontsize=13)
    ax.set_ylabel("Quality Gap (E[p|acc] - E[p|rej])", fontsize=13)
    ax.set_title("Quality Gap vs Adversarial Fraction", fontsize=14)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS_DIR, "quality_gap_vs_adversarial.png"), dpi=150)
    plt.close(fig)
    print("  Plot: quality_gap_vs_adversarial.png")


def plot_welfare_toxicity_tradeoff(df):
    """Fig 5: Welfare-toxicity tradeoff scatter."""
    fig, ax = plt.subplots(figsize=(10, 6))

    for gov in ["none", "basic", "moderate", "full"]:
        sub = df[df["governance"] == gov]
        grouped = sub.groupby("adversarial_fraction").agg({
            "welfare": "mean", "toxicity": "mean"
        })
        ax.scatter(grouped["toxicity"], grouped["welfare"],
                   c=COLORS[gov], label=GOV_LABELS[gov], s=80, zorder=3)
        ax.plot(grouped["toxicity"], grouped["welfare"],
                color=COLORS[gov], alpha=0.4, linewidth=1)

        # Annotate adversarial fractions.
        for frac, row in grouped.iterrows():
            if frac in (0.0, 0.25, 0.50):
                ax.annotate(f"{frac:.0%}", (row["toxicity"], row["welfare"]),
                            fontsize=7, alpha=0.7,
                            xytext=(5, 5), textcoords="offset points")

    ax.set_xlabel("Toxicity E[1-p | accepted]", fontsize=13)
    ax.set_ylabel("Mean Welfare", fontsize=13)
    ax.set_title("Welfare-Toxicity Tradeoff", fontsize=14)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS_DIR, "welfare_toxicity_tradeoff.png"), dpi=150)
    plt.close(fig)
    print("  Plot: welfare_toxicity_tradeoff.png")


def plot_regime_heatmap(df):
    """Fig 6: Regime heatmap (adversarial fraction × governance)."""
    regime_map = {"cooperative": 2, "contested": 1, "collapse": 0}

    # Average regime code across seeds and pop sizes.
    df_copy = df.copy()
    df_copy["regime_code"] = df_copy["regime"].map(regime_map)

    pivot = df_copy.pivot_table(
        values="regime_code",
        index="adversarial_fraction",
        columns="governance",
        aggfunc="mean",
    )
    pivot = pivot[["none", "basic", "moderate", "full"]]

    fig, ax = plt.subplots(figsize=(8, 7))
    from matplotlib.colors import ListedColormap
    cmap = ListedColormap(["#e74c3c", "#f39c12", "#2ecc71"])

    im = ax.imshow(pivot.values, aspect="auto", cmap=cmap,
                   vmin=0, vmax=2, origin="lower")

    ax.set_xticks(range(len(pivot.columns)))
    ax.set_xticklabels([GOV_LABELS[g] for g in pivot.columns],
                       rotation=30, ha="right", fontsize=10)
    ax.set_yticks(range(len(pivot.index)))
    ax.set_yticklabels([f"{f:.1%}" for f in pivot.index], fontsize=10)

    ax.set_xlabel("Governance Configuration", fontsize=13)
    ax.set_ylabel("Adversarial Fraction", fontsize=13)
    ax.set_title("Safety Regime by Configuration", fontsize=14)

    # Annotate cells.
    for i, frac in enumerate(pivot.index):
        for j, gov in enumerate(pivot.columns):
            val = pivot.values[i, j]
            label = {0: "C", 1: "T", 2: "S"}.get(round(val), "?")
            color = "white" if val < 1.5 else "black"
            ax.text(j, i, label, ha="center", va="center",
                    fontsize=11, fontweight="bold", color=color)

    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS_DIR, "regime_heatmap.png"), dpi=150)
    plt.close(fig)
    print("  Plot: regime_heatmap.png")


def plot_profile_comparison(prof_df):
    """Fig 7: Mixed profile comparison bar chart."""
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    profiles = prof_df["mixture_label"].unique()
    gov_order = ["none", "basic", "moderate", "full"]

    for ax, metric, title in zip(
        axes,
        ["acceptance_rate", "toxicity", "welfare"],
        ["Acceptance Rate", "Toxicity", "Welfare"],
    ):
        x = np.arange(len(profiles))
        width = 0.2

        for i, gov in enumerate(gov_order):
            vals = []
            for p in profiles:
                sub = prof_df[
                    (prof_df["mixture_label"] == p)
                    & (prof_df["governance"] == gov)
                ]
                vals.append(sub[metric].mean())
            ax.bar(x + i * width, vals, width, label=GOV_LABELS[gov],
                   color=COLORS[gov], alpha=0.85)

        ax.set_xticks(x + 1.5 * width)
        ax.set_xticklabels(profiles, rotation=45, ha="right", fontsize=8)
        ax.set_title(title, fontsize=12)
        ax.grid(True, alpha=0.3, axis="y")

    axes[0].legend(fontsize=8, loc="lower left")
    fig.suptitle("Mixed Profile Comparison (N=16)", fontsize=14)
    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS_DIR, "profile_comparison.png"), dpi=150)
    plt.close(fig)
    print("  Plot: profile_comparison.png")


def plot_population_size_effect(df):
    """Fig 8: Effect of population size on acceptance (moderate governance)."""
    fig, ax = plt.subplots(figsize=(10, 6))

    sub = df[df["governance"] == "moderate"]
    pop_sizes = sorted(sub["population_size"].unique())
    pop_colors = plt.cm.viridis(np.linspace(0.2, 0.9, len(pop_sizes)))

    for pop_size, color in zip(pop_sizes, pop_colors):
        pop_sub = sub[sub["population_size"] == pop_size]
        grouped = pop_sub.groupby("adversarial_fraction")["acceptance_rate"]
        means = grouped.mean()
        ci95 = 1.96 * grouped.std() / np.sqrt(grouped.count())

        ax.plot(means.index, means.values, "o-",
                color=color, label=f"N={pop_size}", linewidth=2)
        ax.fill_between(means.index,
                        (means - ci95).values,
                        (means + ci95).values,
                        color=color, alpha=0.1)

    ax.axhline(y=0.85, color="gray", linestyle="--", alpha=0.5)
    ax.set_xlabel("Adversarial Fraction", fontsize=13)
    ax.set_ylabel("Acceptance Rate", fontsize=13)
    ax.set_title("Population Size Effect (Moderate Governance)", fontsize=14)
    ax.legend(fontsize=10)
    ax.set_ylim(-0.05, 1.05)
    ax.grid(True, alpha=0.3)

    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS_DIR, "population_size_effect.png"), dpi=150)
    plt.close(fig)
    print("  Plot: population_size_effect.png")


def main():
    print("Generating plots...")
    adv, prof = load_data()

    plot_acceptance_vs_adversarial(adv)
    plot_toxicity_vs_adversarial(adv)
    plot_welfare_vs_adversarial(adv)
    plot_quality_gap_vs_adversarial(adv)
    plot_welfare_toxicity_tradeoff(adv)
    plot_regime_heatmap(adv)
    plot_profile_comparison(prof)
    plot_population_size_effect(adv)

    print(f"\n  All plots saved to {PLOTS_DIR}/")


if __name__ == "__main__":
    main()
