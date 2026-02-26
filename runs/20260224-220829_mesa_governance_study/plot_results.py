#!/usr/bin/env python
"""Plot Mesa Governance Study results."""

import csv
from collections import defaultdict
from pathlib import Path
from statistics import mean, stdev

import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np

RUN_DIR = Path(__file__).parent
CSV_PATH = RUN_DIR / "sweep_results.csv"
PLOT_DIR = RUN_DIR / "plots"
PLOT_DIR.mkdir(exist_ok=True)

# ---------------------------------------------------------------------------
# Load data
# ---------------------------------------------------------------------------

rows = []
with open(CSV_PATH) as f:
    reader = csv.DictReader(f)
    for r in reader:
        rows.append({
            "rho_a": float(r["rho_a"]),
            "adaptive": r["adaptive"] == "True",
            "seed": int(r["seed"]),
            "toxicity": float(r["toxicity"]),
            "quality_gap": float(r["quality_gap"]),
            "total_welfare": float(r["total_welfare"]),
            "acceptance_rate": float(r["acceptance_rate"]),
            "avg_initiator_payoff": float(r["avg_initiator_payoff"]),
            "mean_p_cooperative": float(r["mean_p_cooperative"]),
            "mean_p_selfish": float(r["mean_p_selfish"]),
            "mean_p_exploitative": float(r["mean_p_exploitative"]),
        })


def aggregate(rows, adaptive_val):
    """Group by rho_a, compute mean ± std."""
    by_rho = defaultdict(list)
    for r in rows:
        if r["adaptive"] == adaptive_val:
            by_rho[r["rho_a"]].append(r)

    rhos = sorted(by_rho)
    out = {"rho": np.array(rhos)}
    metrics = ["toxicity", "quality_gap", "total_welfare", "acceptance_rate",
               "avg_initiator_payoff", "mean_p_cooperative", "mean_p_selfish",
               "mean_p_exploitative"]
    for m in metrics:
        vals = [mean(r[m] for r in by_rho[rho]) for rho in rhos]
        errs = [stdev(r[m] for r in by_rho[rho]) if len(by_rho[rho]) > 1 else 0
                for rho in rhos]
        out[m] = np.array(vals)
        out[m + "_err"] = np.array(errs)
    return out


static = aggregate(rows, False)
adaptive = aggregate(rows, True)

# ---------------------------------------------------------------------------
# Style
# ---------------------------------------------------------------------------

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

# ---------------------------------------------------------------------------
# Figure 1: 2x2 main metrics
# ---------------------------------------------------------------------------

fig, axes = plt.subplots(2, 2, figsize=(14, 10))
fig.suptitle("Mesa Bridge Governance Study\nExternality Internalization (ρ_a) × Acceptance Regime",
             fontsize=14, fontweight="bold", y=0.98)

# --- Toxicity ---
ax = axes[0, 0]
ax.fill_between(static["rho"], static["toxicity"] - static["toxicity_err"],
                static["toxicity"] + static["toxicity_err"], alpha=0.15, color=C_STATIC)
ax.fill_between(adaptive["rho"], adaptive["toxicity"] - adaptive["toxicity_err"],
                adaptive["toxicity"] + adaptive["toxicity_err"], alpha=0.15, color=C_ADAPTIVE)
ax.plot(static["rho"], static["toxicity"], "o-", color=C_STATIC, label="Static", linewidth=2, markersize=5)
ax.plot(adaptive["rho"], adaptive["toxicity"], "s-", color=C_ADAPTIVE, label="Adaptive", linewidth=2, markersize=5)
ax.set_xlabel("ρ_a (externality internalization)")
ax.set_ylabel("Toxicity rate")
ax.set_title("Toxicity  E[1−p | accepted]")
ax.legend(loc="upper right")
ax.grid(True)

# --- Total Welfare ---
ax = axes[0, 1]
ax.fill_between(static["rho"], static["total_welfare"] - static["total_welfare_err"],
                static["total_welfare"] + static["total_welfare_err"], alpha=0.15, color=C_STATIC)
ax.fill_between(adaptive["rho"], adaptive["total_welfare"] - adaptive["total_welfare_err"],
                adaptive["total_welfare"] + adaptive["total_welfare_err"], alpha=0.15, color=C_ADAPTIVE)
ax.plot(static["rho"], static["total_welfare"], "o-", color=C_STATIC, label="Static", linewidth=2, markersize=5)
ax.plot(adaptive["rho"], adaptive["total_welfare"], "s-", color=C_ADAPTIVE, label="Adaptive", linewidth=2, markersize=5)
ax.set_xlabel("ρ_a (externality internalization)")
ax.set_ylabel("Total welfare")
ax.set_title("Total Welfare")
ax.legend(loc="upper right")
ax.grid(True)

# --- Quality Gap ---
ax = axes[1, 0]
ax.fill_between(static["rho"], static["quality_gap"] - static["quality_gap_err"],
                static["quality_gap"] + static["quality_gap_err"], alpha=0.15, color=C_STATIC)
ax.fill_between(adaptive["rho"], adaptive["quality_gap"] - adaptive["quality_gap_err"],
                adaptive["quality_gap"] + adaptive["quality_gap_err"], alpha=0.15, color=C_ADAPTIVE)
ax.plot(static["rho"], static["quality_gap"], "o-", color=C_STATIC, label="Static", linewidth=2, markersize=5)
ax.plot(adaptive["rho"], adaptive["quality_gap"], "s-", color=C_ADAPTIVE, label="Adaptive", linewidth=2, markersize=5)
ax.set_xlabel("ρ_a (externality internalization)")
ax.set_ylabel("Quality gap")
ax.set_title("Quality Gap  E[p|accept] − E[p|reject]")
ax.legend(loc="upper right")
ax.grid(True)

# --- Acceptance Rate ---
ax = axes[1, 1]
ax.fill_between(static["rho"], static["acceptance_rate"] - static["acceptance_rate_err"],
                static["acceptance_rate"] + static["acceptance_rate_err"], alpha=0.15, color=C_STATIC)
ax.fill_between(adaptive["rho"], adaptive["acceptance_rate"] - adaptive["acceptance_rate_err"],
                adaptive["acceptance_rate"] + adaptive["acceptance_rate_err"], alpha=0.15, color=C_ADAPTIVE)
ax.plot(static["rho"], static["acceptance_rate"], "o-", color=C_STATIC, label="Static", linewidth=2, markersize=5)
ax.plot(adaptive["rho"], adaptive["acceptance_rate"], "s-", color=C_ADAPTIVE, label="Adaptive", linewidth=2, markersize=5)
ax.set_xlabel("ρ_a (externality internalization)")
ax.set_ylabel("Acceptance rate")
ax.set_title("Acceptance Rate")
ax.legend(loc="upper right")
ax.grid(True)
ax.yaxis.set_major_formatter(mticker.PercentFormatter(1.0))

fig.tight_layout(rect=[0, 0, 1, 0.94])
fig.savefig(PLOT_DIR / "main_metrics.png", dpi=150, bbox_inches="tight")
print(f"Saved {PLOT_DIR / 'main_metrics.png'}")

# ---------------------------------------------------------------------------
# Figure 2: Per-archetype p distribution (adaptive only)
# ---------------------------------------------------------------------------

fig2, ax2 = plt.subplots(figsize=(10, 6))
fig2.suptitle("Per-Archetype Mean p Under Adaptive Governance",
              fontsize=14, fontweight="bold")

ax2.plot(adaptive["rho"], adaptive["mean_p_cooperative"], "o-",
         color=C_COOP, label="Cooperative", linewidth=2.5, markersize=6)
ax2.plot(adaptive["rho"], adaptive["mean_p_selfish"], "s-",
         color=C_SELFISH, label="Selfish", linewidth=2.5, markersize=6)
ax2.plot(adaptive["rho"], adaptive["mean_p_exploitative"], "^-",
         color=C_EXPLOIT, label="Exploitative", linewidth=2.5, markersize=6)

# Show adaptive threshold line
rho_range = np.linspace(0, 1, 50)
threshold = 0.5 + 0.3 * rho_range
ax2.plot(rho_range, threshold, "--", color="#8b949e", linewidth=1.5,
         label="Accept threshold", alpha=0.7)
ax2.fill_between(rho_range, 0, threshold, alpha=0.05, color="#f85149")
ax2.text(0.85, 0.78, "REJECT\nZONE", fontsize=9, color="#f85149",
         alpha=0.5, ha="center", va="center")

ax2.set_xlabel("ρ_a (externality internalization)")
ax2.set_ylabel("Mean p (quality probability)")
ax2.set_ylim(0, 1)
ax2.legend(loc="center right")
ax2.grid(True)

fig2.tight_layout()
fig2.savefig(PLOT_DIR / "archetype_quality.png", dpi=150, bbox_inches="tight")
print(f"Saved {PLOT_DIR / 'archetype_quality.png'}")

# ---------------------------------------------------------------------------
# Figure 3: Toxicity-welfare tradeoff frontier
# ---------------------------------------------------------------------------

fig3, ax3 = plt.subplots(figsize=(10, 6))
fig3.suptitle("Toxicity–Welfare Tradeoff Frontier",
              fontsize=14, fontweight="bold")

# Plot each regime as a connected path
ax3.plot(static["toxicity"], static["total_welfare"], "o-",
         color=C_STATIC, label="Static", linewidth=2, markersize=7)
ax3.plot(adaptive["toxicity"], adaptive["total_welfare"], "s-",
         color=C_ADAPTIVE, label="Adaptive", linewidth=2, markersize=7)

# Annotate key rho values
for i, rho in enumerate(static["rho"]):
    if rho in (0.0, 0.5, 1.0):
        ax3.annotate(f"ρ={rho:.1f}",
                     (static["toxicity"][i], static["total_welfare"][i]),
                     textcoords="offset points", xytext=(12, 5),
                     fontsize=9, color=C_STATIC, alpha=0.8)
for i, rho in enumerate(adaptive["rho"]):
    if rho in (0.0, 0.5, 1.0):
        ax3.annotate(f"ρ={rho:.1f}",
                     (adaptive["toxicity"][i], adaptive["total_welfare"][i]),
                     textcoords="offset points", xytext=(12, -12),
                     fontsize=9, color=C_ADAPTIVE, alpha=0.8)

ax3.set_xlabel("Toxicity rate (lower is better →)")
ax3.set_ylabel("Total welfare (higher is better ↑)")
ax3.legend(loc="upper left")
ax3.grid(True)
ax3.invert_xaxis()

fig3.tight_layout()
fig3.savefig(PLOT_DIR / "tradeoff_frontier.png", dpi=150, bbox_inches="tight")
print(f"Saved {PLOT_DIR / 'tradeoff_frontier.png'}")

# ---------------------------------------------------------------------------
# Figure 4: Marginal toxicity reduction per unit welfare lost
# ---------------------------------------------------------------------------

fig4, ax4 = plt.subplots(figsize=(10, 6))
fig4.suptitle("Governance Efficiency: Toxicity Reduction per Welfare Unit",
              fontsize=14, fontweight="bold")

# For adaptive: compute Δtoxicity / Δwelfare between consecutive rho values
rhos_a = adaptive["rho"]
tox_a = adaptive["toxicity"]
wel_a = adaptive["total_welfare"]

# Marginal efficiency: how much toxicity drops per unit of welfare sacrificed
efficiency = []
rho_mid = []
for i in range(1, len(rhos_a)):
    dtox = tox_a[i - 1] - tox_a[i]  # toxicity reduction (positive = good)
    dwel = wel_a[i - 1] - wel_a[i]  # welfare cost (positive = lost)
    eff = (dtox / dwel * 1000) if dwel > 0 else 0  # per 1000 welfare units
    efficiency.append(eff)
    rho_mid.append((rhos_a[i - 1] + rhos_a[i]) / 2)

bars = ax4.bar(rho_mid, efficiency, width=0.08, color=C_ADAPTIVE, alpha=0.8,
               edgecolor="#30363d", linewidth=0.5)

# Highlight the sweet spot
max_idx = np.argmax(efficiency)
bars[max_idx].set_color("#3fb950")
bars[max_idx].set_alpha(1.0)
ax4.annotate(f"Best efficiency\nρ ≈ {rho_mid[max_idx]:.2f}",
             (rho_mid[max_idx], efficiency[max_idx]),
             textcoords="offset points", xytext=(40, 10),
             fontsize=10, color="#3fb950",
             arrowprops=dict(arrowstyle="->", color="#3fb950", lw=1.5))

ax4.set_xlabel("ρ_a (midpoint of interval)")
ax4.set_ylabel("Toxicity reduction per 1000 welfare units")
ax4.set_title("Higher = more efficient governance")
ax4.grid(True, axis="y")

fig4.tight_layout()
fig4.savefig(PLOT_DIR / "governance_efficiency.png", dpi=150, bbox_inches="tight")
print(f"Saved {PLOT_DIR / 'governance_efficiency.png'}")

plt.close("all")
print(f"\nAll plots saved to {PLOT_DIR}/")
