#!/usr/bin/env python
"""Generate /plot --sweep standard plots for the Mesa governance study."""

from __future__ import annotations

import os
from pathlib import Path

import numpy as np
import pandas as pd

# Non-interactive backend
os.environ.setdefault("MPLCONFIGDIR", "/tmp/.mplconfig")

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
from scipy import stats as sp_stats

CSV = Path(__file__).resolve().parent.parent / "sweep_results.csv"
OUT = Path(__file__).resolve().parent

df = pd.read_csv(CSV)
df["regime"] = df["adaptive"].map({True: "adaptive", False: "static"})
df["config"] = df.apply(lambda r: f"rho={r.rho_a:.1f}\n{r.regime}", axis=1)

SWEPT = ["rho_a", "adaptive"]

# ── Dark theme ──────────────────────────────────────────────────────────
plt.rcParams.update({
    "figure.facecolor": "#0d1117",
    "axes.facecolor": "#161b22",
    "axes.edgecolor": "#30363d",
    "axes.labelcolor": "#c9d1d9",
    "text.color": "#c9d1d9",
    "xtick.color": "#8b949e",
    "ytick.color": "#8b949e",
    "grid.color": "#21262d",
    "grid.alpha": 0.7,
    "legend.facecolor": "#161b22",
    "legend.edgecolor": "#30363d",
    "font.family": "monospace",
    "font.size": 11,
})
C_STATIC = "#58a6ff"
C_ADAPTIVE = "#f78166"
C_COOP = "#3fb950"
C_SELFISH = "#d29922"
C_EXPLOIT = "#f85149"

plots_written = []


# ═══════════════════════════════════════════════════════════════════════
# 1. Grouped bar: welfare by config
# ═══════════════════════════════════════════════════════════════════════
def plot_grouped_bar_welfare():
    fig, ax = plt.subplots(figsize=(14, 6))
    rhos = sorted(df["rho_a"].unique())
    x = np.arange(len(rhos))
    w = 0.35

    for offset, (regime, color) in enumerate(
        [("static", C_STATIC), ("adaptive", C_ADAPTIVE)]
    ):
        sub = df[df["regime"] == regime]
        means = [sub[sub["rho_a"] == r]["total_welfare"].mean() for r in rhos]
        stds = [sub[sub["rho_a"] == r]["total_welfare"].std() for r in rhos]
        bars = ax.bar(x + offset * w - w / 2, means, w, yerr=stds,
                      capsize=3, label=regime.title(), color=color, alpha=0.8,
                      edgecolor="#30363d", linewidth=0.5)
        # Overlay individual points
        for i, r in enumerate(rhos):
            vals = sub[sub["rho_a"] == r]["total_welfare"].values
            ax.scatter(
                np.full_like(vals, x[i] + offset * w - w / 2) + np.random.default_rng(42).uniform(-0.08, 0.08, len(vals)),
                vals, color="white", s=12, alpha=0.5, zorder=5, edgecolors="none",
            )

    ax.set_xticks(x)
    ax.set_xticklabels([f"{r:.1f}" for r in rhos])
    ax.set_xlabel("ρ_a (externality internalization)")
    ax.set_ylabel("Total welfare")
    ax.set_title("Welfare by Configuration (±1 SD, individual runs overlaid)")
    ax.legend()
    ax.grid(axis="y")
    fig.tight_layout()
    p = OUT / "welfare_by_config.png"
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)
    return p


# ═══════════════════════════════════════════════════════════════════════
# 2. Grouped bar: toxicity by config
# ═══════════════════════════════════════════════════════════════════════
def plot_grouped_bar_toxicity():
    fig, ax = plt.subplots(figsize=(14, 6))
    rhos = sorted(df["rho_a"].unique())
    x = np.arange(len(rhos))
    w = 0.35

    for offset, (regime, color) in enumerate(
        [("static", C_STATIC), ("adaptive", C_ADAPTIVE)]
    ):
        sub = df[df["regime"] == regime]
        means = [sub[sub["rho_a"] == r]["toxicity"].mean() for r in rhos]
        stds = [sub[sub["rho_a"] == r]["toxicity"].std() for r in rhos]
        ax.bar(x + offset * w - w / 2, means, w, yerr=stds,
               capsize=3, label=regime.title(), color=color, alpha=0.8,
               edgecolor="#30363d", linewidth=0.5)
        for i, r in enumerate(rhos):
            vals = sub[sub["rho_a"] == r]["toxicity"].values
            ax.scatter(
                np.full_like(vals, x[i] + offset * w - w / 2) + np.random.default_rng(42).uniform(-0.08, 0.08, len(vals)),
                vals, color="white", s=12, alpha=0.5, zorder=5, edgecolors="none",
            )

    ax.set_xticks(x)
    ax.set_xticklabels([f"{r:.1f}" for r in rhos])
    ax.set_xlabel("ρ_a (externality internalization)")
    ax.set_ylabel("Toxicity rate")
    ax.set_title("Toxicity by Configuration (±1 SD)")
    ax.legend()
    ax.grid(axis="y")
    fig.tight_layout()
    p = OUT / "toxicity_by_config.png"
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)
    return p


# ═══════════════════════════════════════════════════════════════════════
# 3. Box plots: welfare distribution per config
# ═══════════════════════════════════════════════════════════════════════
def plot_welfare_boxplot():
    fig, axes = plt.subplots(1, 2, figsize=(16, 6), sharey=True)
    rhos = sorted(df["rho_a"].unique())

    for ax, (regime, color) in zip(axes, [("static", C_STATIC), ("adaptive", C_ADAPTIVE)]):
        sub = df[df["regime"] == regime]
        data = [sub[sub["rho_a"] == r]["total_welfare"].values for r in rhos]
        bp = ax.boxplot(data, tick_labels=[f"{r:.1f}" for r in rhos], patch_artist=True,
                        widths=0.6, showfliers=True)
        for patch in bp["boxes"]:
            patch.set_facecolor(color)
            patch.set_alpha(0.6)
        for element in ["whiskers", "caps", "medians"]:
            for item in bp[element]:
                item.set_color("#c9d1d9")
        ax.set_xlabel("ρ_a")
        ax.set_title(f"{regime.title()} threshold")
        ax.grid(axis="y")

    axes[0].set_ylabel("Total welfare")
    fig.suptitle("Welfare Distribution by Configuration", fontsize=14, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.94])
    p = OUT / "welfare_boxplot.png"
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)
    return p


# ═══════════════════════════════════════════════════════════════════════
# 4. Heatmap: rho_a × regime for welfare/toxicity/quality_gap
# ═══════════════════════════════════════════════════════════════════════
def plot_heatmap():
    metrics = [
        ("total_welfare", "Welfare", "RdYlGn"),
        ("toxicity", "Toxicity", "YlOrRd_r"),
        ("quality_gap", "Quality Gap", "RdYlGn"),
    ]
    fig, axes = plt.subplots(1, 3, figsize=(18, 5))

    for ax, (col, title, cmap) in zip(axes, metrics):
        pivot = df.groupby(["regime", "rho_a"])[col].mean().unstack()
        im = ax.imshow(pivot.values, aspect="auto", cmap=cmap)
        ax.set_xticks(range(len(pivot.columns)))
        ax.set_xticklabels([f"{c:.1f}" for c in pivot.columns], fontsize=8)
        ax.set_yticks(range(len(pivot.index)))
        ax.set_yticklabels(pivot.index, fontsize=10)
        ax.set_xlabel("ρ_a")
        ax.set_title(title)

        for i in range(len(pivot.index)):
            for j in range(len(pivot.columns)):
                val = pivot.values[i, j]
                fmt = f"{val:.0f}" if abs(val) > 10 else f"{val:.3f}"
                ax.text(j, i, fmt, ha="center", va="center", fontsize=7,
                        color="black" if val > pivot.values.mean() else "white")

        fig.colorbar(im, ax=ax, shrink=0.8)

    fig.suptitle("Parameter Grid Heatmap (mean across seeds)", fontsize=14, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.93])
    p = OUT / "heatmap_rho_regime.png"
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)
    return p


# ═══════════════════════════════════════════════════════════════════════
# 5. Agent payoff comparison: per-archetype p by config
# ═══════════════════════════════════════════════════════════════════════
def plot_payoff_by_agent_type():
    fig, axes = plt.subplots(1, 3, figsize=(18, 6), sharey=True)
    rhos = sorted(df["rho_a"].unique())
    arch_cols = [
        ("mean_p_cooperative", "Cooperative", C_COOP),
        ("mean_p_selfish", "Selfish", C_SELFISH),
        ("mean_p_exploitative", "Exploitative", C_EXPLOIT),
    ]

    for ax, (col, name, color) in zip(axes, arch_cols):
        for regime, ls, marker in [("static", "-", "o"), ("adaptive", "--", "s")]:
            sub = df[df["regime"] == regime]
            means = [sub[sub["rho_a"] == r][col].mean() for r in rhos]
            stds = [sub[sub["rho_a"] == r][col].std() for r in rhos]
            ax.errorbar(rhos, means, yerr=stds, fmt=f"{marker}{ls}",
                        color=color, label=regime.title(), linewidth=2,
                        markersize=5, capsize=3, alpha=0.9)

        ax.set_xlabel("ρ_a")
        ax.set_title(f"{name} agents")
        ax.legend(fontsize=9)
        ax.grid(True)

    axes[0].set_ylabel("Mean p (quality probability)")
    fig.suptitle("Agent Quality by Archetype and Regime", fontsize=14, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.93])
    p = OUT / "payoff_by_agent_type.png"
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)
    return p


# ═══════════════════════════════════════════════════════════════════════
# 6. Effect size: adaptive vs static boost with 95% CI + significance
# ═══════════════════════════════════════════════════════════════════════
def plot_effect_size():
    rhos = sorted(df["rho_a"].unique())
    metrics = [
        ("toxicity", "Toxicity Δ (adaptive − static)", True),
        ("total_welfare", "Welfare Δ (adaptive − static)", False),
    ]
    fig, axes = plt.subplots(1, 2, figsize=(16, 6))

    for ax, (col, ylabel, invert_good) in zip(axes, metrics):
        boosts, cis, pvals = [], [], []
        for r in rhos:
            static_vals = df[(df["rho_a"] == r) & (df["regime"] == "static")][col].values
            adapt_vals = df[(df["rho_a"] == r) & (df["regime"] == "adaptive")][col].values
            diff = adapt_vals.mean() - static_vals.mean()
            se = np.sqrt(adapt_vals.var() / len(adapt_vals) + static_vals.var() / len(static_vals))
            ci = 1.96 * se
            if len(static_vals) >= 2 and len(adapt_vals) >= 2:
                _, pval = sp_stats.mannwhitneyu(adapt_vals, static_vals, alternative="two-sided")
            else:
                pval = 1.0
            boosts.append(diff)
            cis.append(ci)
            pvals.append(pval)

        colors = []
        for b, pv in zip(boosts, pvals):
            if pv >= 0.05:
                colors.append("#8b949e")  # not significant
            elif (b < 0) == invert_good:
                colors.append(C_COOP)  # good direction
            else:
                colors.append(C_EXPLOIT)  # bad direction

        x = np.arange(len(rhos))
        ax.bar(x, boosts, yerr=cis, capsize=4, color=colors, alpha=0.8,
               edgecolor="#30363d", linewidth=0.5, width=0.7)
        ax.axhline(0, color="#c9d1d9", linewidth=0.8, linestyle="--", alpha=0.5)

        for i, (b, pv) in enumerate(zip(boosts, pvals)):
            sig = "***" if pv < 0.001 else "**" if pv < 0.01 else "*" if pv < 0.05 else "ns"
            y_pos = b + cis[i] * 1.1 if b >= 0 else b - cis[i] * 1.1
            va = "bottom" if b >= 0 else "top"
            ax.text(i, y_pos, sig, ha="center", va=va, fontsize=8, fontweight="bold")

        ax.set_xticks(x)
        ax.set_xticklabels([f"{r:.1f}" for r in rhos])
        ax.set_xlabel("ρ_a")
        ax.set_ylabel(ylabel)
        ax.grid(axis="y")

    axes[0].set_title("Toxicity Effect (green = lower toxicity)")
    axes[1].set_title("Welfare Effect (green = higher welfare)")
    fig.suptitle("Adaptive vs Static: Effect Size with 95% CI", fontsize=14, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.93])
    p = OUT / "effect_size_ci.png"
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)
    return p


# ═══════════════════════════════════════════════════════════════════════
# Run all
# ═══════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    for fn in [plot_grouped_bar_welfare, plot_grouped_bar_toxicity,
               plot_welfare_boxplot, plot_heatmap, plot_payoff_by_agent_type,
               plot_effect_size]:
        p = fn()
        plots_written.append(p)
        print(f"  {p.name}")

    print(f"\nGenerated {len(plots_written)} plots in {OUT}/")
