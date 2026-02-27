#!/usr/bin/env python3
"""Generate plots for the Mesa adaptive agents study.

Compares 3 regimes: static, adaptive, adaptive_learning across rho_a sweep.
Key story: learning agents recover welfare at high rho without sacrificing toxicity gains.
"""

import sys
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from scipy import stats

# ── Load data ──────────────────────────────────────────────────────────────
RUN_DIR = Path(__file__).resolve().parent.parent
CSV_PATH = RUN_DIR / "sweep_results.csv"
PLOT_DIR = RUN_DIR / "plots"
PLOT_DIR.mkdir(exist_ok=True)

df = pd.read_csv(CSV_PATH)

REGIMES = ["static", "adaptive", "adaptive_learning"]
REGIME_LABELS = {"static": "Static", "adaptive": "Adaptive", "adaptive_learning": "Adaptive + Learning"}
REGIME_COLORS = {"static": "#7f8c8d", "adaptive": "#e74c3c", "adaptive_learning": "#2ecc71"}
RHO_VALUES = sorted(df["rho_a"].unique())

# ── Helper ─────────────────────────────────────────────────────────────────

def grouped_means(metric: str) -> dict[str, tuple[np.ndarray, np.ndarray]]:
    """Return {regime: (means, stds)} arrays aligned with RHO_VALUES."""
    result = {}
    for regime in REGIMES:
        means, sds = [], []
        for rho in RHO_VALUES:
            vals = df[(df["regime"] == regime) & (df["rho_a"] == rho)][metric]
            means.append(vals.mean())
            sds.append(vals.std())
        result[regime] = (np.array(means), np.array(sds))
    return result


# ═══════════════════════════════════════════════════════════════════════════
# Plot 1: Main metrics (welfare + toxicity) — the hero plot
# ═══════════════════════════════════════════════════════════════════════════

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

for metric, ax, ylabel in [
    ("total_welfare", ax1, "Total Welfare"),
    ("toxicity", ax2, "Toxicity Rate"),
]:
    data = grouped_means(metric)
    for regime in REGIMES:
        means, sds = data[regime]
        ax.plot(RHO_VALUES, means, "o-", color=REGIME_COLORS[regime],
                label=REGIME_LABELS[regime], linewidth=2, markersize=5)
        ax.fill_between(RHO_VALUES, means - sds, means + sds,
                        color=REGIME_COLORS[regime], alpha=0.15)
    ax.set_xlabel("Externality Internalization (ρ_a)")
    ax.set_ylabel(ylabel)
    ax.legend()
    ax.grid(True, alpha=0.3)

ax1.set_title("Welfare: Learning Agents Recover the Collapse")
ax2.set_title("Toxicity: Learning Maintains Safety Gains")
fig.suptitle("Mesa Adaptive Agents Study — 3 Regimes × 11 ρ values × 5 seeds", fontsize=13)
fig.tight_layout()
fig.savefig(PLOT_DIR / "main_metrics.png", dpi=150, bbox_inches="tight")
plt.close(fig)
print("  ✓ main_metrics.png")


# ═══════════════════════════════════════════════════════════════════════════
# Plot 2: Welfare recovery — how much welfare learning recovers vs adaptive
# ═══════════════════════════════════════════════════════════════════════════

fig, ax = plt.subplots(figsize=(10, 5))

adap = grouped_means("total_welfare")["adaptive"][0]
learn = grouped_means("total_welfare")["adaptive_learning"][0]
static = grouped_means("total_welfare")["static"][0]

recovery_pct = np.where(static - adap > 0, (learn - adap) / (static - adap) * 100, 0)

bars = ax.bar(RHO_VALUES, recovery_pct, width=0.07, color=REGIME_COLORS["adaptive_learning"],
              edgecolor="white", linewidth=0.5)
ax.axhline(100, color="gray", linestyle="--", alpha=0.5, label="Full recovery (100%)")
ax.set_xlabel("Externality Internalization (ρ_a)")
ax.set_ylabel("Welfare Recovery (%)\n(learning vs adaptive, relative to static baseline)")
ax.set_title("How Much Welfare Do Learning Agents Recover?")
ax.legend()
ax.grid(True, alpha=0.3, axis="y")

# Annotate key values
for i, rho in enumerate(RHO_VALUES):
    if rho in [0.5, 0.7, 1.0]:
        ax.annotate(f"{recovery_pct[i]:.0f}%", (rho, recovery_pct[i]),
                    textcoords="offset points", xytext=(0, 8), ha="center", fontsize=9)

fig.tight_layout()
fig.savefig(PLOT_DIR / "welfare_recovery.png", dpi=150, bbox_inches="tight")
plt.close(fig)
print("  ✓ welfare_recovery.png")


# ═══════════════════════════════════════════════════════════════════════════
# Plot 3: Learning dynamics — selfish agent task_progress improvement
# ═══════════════════════════════════════════════════════════════════════════

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

# Task progress
for regime in REGIMES:
    means, sds = [], []
    for rho in RHO_VALUES:
        vals = df[(df["regime"] == regime) & (df["rho_a"] == rho)]["avg_final_tp_selfish"]
        means.append(vals.mean())
        sds.append(vals.std())
    ax1.plot(RHO_VALUES, means, "o-", color=REGIME_COLORS[regime],
             label=REGIME_LABELS[regime], linewidth=2, markersize=5)

ax1.set_xlabel("ρ_a")
ax1.set_ylabel("Final Task Progress (Selfish Agents)")
ax1.set_title("Selfish Agents Learn to Improve Quality")
ax1.legend()
ax1.grid(True, alpha=0.3)

# Acceptance rate
data = grouped_means("acceptance_rate")
for regime in REGIMES:
    means, sds = data[regime]
    ax2.plot(RHO_VALUES, means, "o-", color=REGIME_COLORS[regime],
             label=REGIME_LABELS[regime], linewidth=2, markersize=5)
    ax2.fill_between(RHO_VALUES, means - sds, means + sds,
                     color=REGIME_COLORS[regime], alpha=0.15)

ax2.set_xlabel("ρ_a")
ax2.set_ylabel("Acceptance Rate")
ax2.set_title("Learning Agents Maintain Higher Acceptance")
ax2.legend()
ax2.grid(True, alpha=0.3)

fig.suptitle("Learning Dynamics", fontsize=13)
fig.tight_layout()
fig.savefig(PLOT_DIR / "learning_dynamics.png", dpi=150, bbox_inches="tight")
plt.close(fig)
print("  ✓ learning_dynamics.png")


# ═══════════════════════════════════════════════════════════════════════════
# Plot 4: Tradeoff frontier — welfare vs toxicity (Pareto front)
# ═══════════════════════════════════════════════════════════════════════════

fig, ax = plt.subplots(figsize=(8, 6))

for regime in REGIMES:
    sub = df[df["regime"] == regime].groupby("rho_a").agg(
        welfare=("total_welfare", "mean"),
        toxicity=("toxicity", "mean"),
    ).reset_index()
    ax.plot(sub["toxicity"], sub["welfare"], "o-", color=REGIME_COLORS[regime],
            label=REGIME_LABELS[regime], linewidth=2, markersize=6)
    # Annotate endpoints
    for idx in [0, len(sub) - 1]:
        rho = sub.iloc[idx]["rho_a"]
        ax.annotate(f"ρ={rho:.1f}", (sub.iloc[idx]["toxicity"], sub.iloc[idx]["welfare"]),
                    textcoords="offset points", xytext=(8, -5), fontsize=8, alpha=0.7)

ax.set_xlabel("Toxicity Rate (lower is better →)")
ax.set_ylabel("Total Welfare (higher is better →)")
ax.set_title("Welfare–Toxicity Tradeoff Frontier\nLearning agents push the Pareto front outward")
ax.legend()
ax.grid(True, alpha=0.3)
ax.invert_xaxis()
fig.tight_layout()
fig.savefig(PLOT_DIR / "tradeoff_frontier.png", dpi=150, bbox_inches="tight")
plt.close(fig)
print("  ✓ tradeoff_frontier.png")


# ═══════════════════════════════════════════════════════════════════════════
# Plot 5: Effect sizes — adaptive_learning vs adaptive with 95% CI
# ═══════════════════════════════════════════════════════════════════════════

fig, axes = plt.subplots(1, 3, figsize=(15, 5))

for metric, ax, title in [
    ("toxicity", axes[0], "Toxicity (lower=better)"),
    ("total_welfare", axes[1], "Total Welfare"),
    ("acceptance_rate", axes[2], "Acceptance Rate"),
]:
    diffs, cis_lo, cis_hi, pvals = [], [], [], []
    for rho in RHO_VALUES:
        learn_vals = df[(df["regime"] == "adaptive_learning") & (df["rho_a"] == rho)][metric]
        adap_vals = df[(df["regime"] == "adaptive") & (df["rho_a"] == rho)][metric]
        diff = learn_vals.mean() - adap_vals.mean()
        # Welch's t-test
        t_stat, p_val = stats.ttest_ind(learn_vals, adap_vals, equal_var=False)
        # 95% CI via pooled SE
        se = np.sqrt(learn_vals.var() / len(learn_vals) + adap_vals.var() / len(adap_vals))
        diffs.append(diff)
        cis_lo.append(diff - 1.96 * se)
        cis_hi.append(diff + 1.96 * se)
        pvals.append(p_val)

    diffs = np.array(diffs)
    cis_lo = np.array(cis_lo)
    cis_hi = np.array(cis_hi)

    colors = ["#2ecc71" if p < 0.05 else "#95a5a6" for p in pvals]
    ax.bar(RHO_VALUES, diffs, width=0.07, color=colors, edgecolor="white", linewidth=0.5)
    ax.vlines(RHO_VALUES, cis_lo, cis_hi, color="black", linewidth=1.5)
    ax.axhline(0, color="black", linewidth=0.8)
    ax.set_xlabel("ρ_a")
    ax.set_title(title)
    ax.grid(True, alpha=0.3, axis="y")

    # Significance markers
    for i, p in enumerate(pvals):
        if p < 0.001:
            marker = "***"
        elif p < 0.01:
            marker = "**"
        elif p < 0.05:
            marker = "*"
        else:
            marker = ""
        if marker:
            y = max(diffs[i], cis_hi[i]) if diffs[i] > 0 else min(diffs[i], cis_lo[i])
            ax.text(RHO_VALUES[i], y, marker, ha="center", va="bottom" if diffs[i] > 0 else "top",
                    fontsize=10, fontweight="bold")

fig.suptitle("Effect of Learning (Adaptive+Learning minus Adaptive) with 95% CI", fontsize=13)
fig.tight_layout()
fig.savefig(PLOT_DIR / "effect_sizes.png", dpi=150, bbox_inches="tight")
plt.close(fig)
print("  ✓ effect_sizes.png")


# ═══════════════════════════════════════════════════════════════════════════
# Plot 6: Archetype quality — mean p by archetype across regimes
# ═══════════════════════════════════════════════════════════════════════════

fig, axes = plt.subplots(1, 3, figsize=(15, 5))
archetypes = [
    ("mean_p_cooperative", "Cooperative", "#3498db"),
    ("mean_p_selfish", "Selfish", "#e67e22"),
    ("mean_p_exploitative", "Exploitative", "#e74c3c"),
]

for (col, arch_name, _), ax in zip(archetypes, axes):
    for regime in REGIMES:
        means = []
        for rho in RHO_VALUES:
            vals = df[(df["regime"] == regime) & (df["rho_a"] == rho)][col]
            means.append(vals.mean())
        ax.plot(RHO_VALUES, means, "o-", color=REGIME_COLORS[regime],
                label=REGIME_LABELS[regime], linewidth=2, markersize=5)
    ax.set_xlabel("ρ_a")
    ax.set_ylabel(f"Mean p ({arch_name})")
    ax.set_title(f"{arch_name} Agent Quality")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)

fig.suptitle("Agent Quality (p) by Archetype — Learning Raises Selfish Quality", fontsize=13)
fig.tight_layout()
fig.savefig(PLOT_DIR / "archetype_quality.png", dpi=150, bbox_inches="tight")
plt.close(fig)
print("  ✓ archetype_quality.png")


# ═══════════════════════════════════════════════════════════════════════════
# Plot 7: Welfare box plots by regime at key rho values
# ═══════════════════════════════════════════════════════════════════════════

key_rhos = [0.0, 0.3, 0.5, 0.7, 1.0]
fig, axes = plt.subplots(1, len(key_rhos), figsize=(16, 5), sharey=True)

for ax, rho in zip(axes, key_rhos):
    data_for_box = []
    labels = []
    colors = []
    for regime in REGIMES:
        vals = df[(df["regime"] == regime) & (df["rho_a"] == rho)]["total_welfare"]
        data_for_box.append(vals.values)
        labels.append(REGIME_LABELS[regime].replace(" + ", "\n+ "))
        colors.append(REGIME_COLORS[regime])

    bp = ax.boxplot(data_for_box, labels=labels, patch_artist=True, widths=0.6)
    for patch, color in zip(bp["boxes"], colors):
        patch.set_facecolor(color)
        patch.set_alpha(0.6)
    ax.set_title(f"ρ = {rho:.1f}")
    ax.grid(True, alpha=0.3, axis="y")
    ax.tick_params(axis="x", rotation=30, labelsize=8)

axes[0].set_ylabel("Total Welfare")
fig.suptitle("Welfare Distribution at Key ρ Values", fontsize=13)
fig.tight_layout()
fig.savefig(PLOT_DIR / "welfare_boxplots.png", dpi=150, bbox_inches="tight")
plt.close(fig)
print("  ✓ welfare_boxplots.png")


# ═══════════════════════════════════════════════════════════════════════════
# Plot 8: Governance efficiency — toxicity reduction per welfare unit lost
# ═══════════════════════════════════════════════════════════════════════════

fig, ax = plt.subplots(figsize=(10, 5))

for regime in ["adaptive", "adaptive_learning"]:
    tox = grouped_means("toxicity")[regime][0]
    wel = grouped_means("total_welfare")[regime][0]
    tox_base = tox[0]
    wel_base = wel[0]

    tox_reduction = tox_base - tox
    welfare_cost = wel_base - wel
    # Avoid division by zero
    efficiency = np.where(welfare_cost > 1, tox_reduction / welfare_cost * 1000, 0)

    ax.plot(RHO_VALUES, efficiency, "o-", color=REGIME_COLORS[regime],
            label=REGIME_LABELS[regime], linewidth=2, markersize=5)

ax.set_xlabel("ρ_a")
ax.set_ylabel("Governance Efficiency\n(toxicity reduction per 1000 welfare units)")
ax.set_title("Governance Efficiency: Learning Agents Are More Efficient at Every ρ")
ax.legend()
ax.grid(True, alpha=0.3)
fig.tight_layout()
fig.savefig(PLOT_DIR / "governance_efficiency.png", dpi=150, bbox_inches="tight")
plt.close(fig)
print("  ✓ governance_efficiency.png")


print(f"\nAll plots saved to {PLOT_DIR}/")
