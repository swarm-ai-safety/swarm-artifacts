#!/usr/bin/env python3
"""Composition boundary study.

Sweeps archetype mixtures × governance configs × population sizes to
characterize where population-level safety holds.

Key questions:
  1. Where does the critical adversarial fraction lie under each governance?
  2. How does governance shift the boundary?
  3. Do mixed profiles behave differently from pure archetypes?
"""

import csv
import json
import os
import sys
import time

import numpy as np

# Ensure repo root is on path.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "../.."))

from swarm.core.behavioral_profiler import InferredProfile
from swarm.core.composition_analyzer import (
    SafetyCompositionAnalyzer,
    SafetyRegime,
    SweepConfig,
    classify_regime,
    _create_population,
)
from swarm.core.orchestrator import Orchestrator, OrchestratorConfig
from swarm.core.payoff import PayoffConfig
from swarm.governance.config import GovernanceConfig
from swarm.models.agent import AgentType

RUN_DIR = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------------------
# Study parameters
# ---------------------------------------------------------------------------

POPULATION_SIZES = [4, 8, 16, 32]
SEEDS = [42, 123, 456, 789, 1001]
N_EPOCHS = 20
STEPS_PER_EPOCH = 10

PAYOFF = PayoffConfig(
    s_plus=2.0, s_minus=1.0, h=2.0, theta=0.5,
    rho_a=0.1, rho_b=0.1, w_rep=1.0,
)

# Adversarial fractions to sweep (the key independent variable).
ADVERSARIAL_FRACTIONS = [0.0, 0.05, 0.10, 0.15, 0.20, 0.25, 0.30,
                         0.375, 0.50]

# Governance configs to compare.
GOVERNANCE_CONFIGS = {
    "none": None,
    "basic": GovernanceConfig(
        transaction_tax_rate=0.05,
        circuit_breaker_enabled=True,
        freeze_threshold_toxicity=0.7,
        freeze_threshold_violations=3,
        freeze_duration_epochs=2,
    ),
    "moderate": GovernanceConfig(
        transaction_tax_rate=0.08,
        circuit_breaker_enabled=True,
        freeze_threshold_toxicity=0.5,
        freeze_threshold_violations=2,
        freeze_duration_epochs=3,
        audit_enabled=True,
        audit_probability=0.1,
        audit_penalty_multiplier=2.0,
    ),
    "full": GovernanceConfig(
        transaction_tax_rate=0.12,
        circuit_breaker_enabled=True,
        freeze_threshold_toxicity=0.5,
        freeze_threshold_violations=2,
        freeze_duration_epochs=3,
        audit_enabled=True,
        audit_probability=0.15,
        audit_penalty_multiplier=2.5,
        staking_enabled=True,
        min_stake_to_participate=5.0,
        stake_slash_rate=0.15,
        collusion_detection_enabled=True,
    ),
}

# Profile mixtures to test (Question 3: mixed vs pure).
PROFILE_MIXTURES = {
    # Pure archetypes at varying adversarial fractions are handled by
    # the adversarial fraction sweep.  These test specific mixed profiles.
    "pure_honest": {AgentType.HONEST: 1.0},
    "pure_adversarial": {AgentType.ADVERSARIAL: 1.0},
    "honest_opportunistic_70_30": {
        AgentType.HONEST: 0.70,
        AgentType.OPPORTUNISTIC: 0.30,
    },
    "honest_deceptive_80_20": {
        AgentType.HONEST: 0.80,
        AgentType.DECEPTIVE: 0.20,
    },
    "realistic_mix": {
        AgentType.HONEST: 0.55,
        AgentType.OPPORTUNISTIC: 0.25,
        AgentType.DECEPTIVE: 0.12,
        AgentType.ADVERSARIAL: 0.08,
    },
    "high_threat": {
        AgentType.HONEST: 0.30,
        AgentType.OPPORTUNISTIC: 0.20,
        AgentType.DECEPTIVE: 0.20,
        AgentType.ADVERSARIAL: 0.30,
    },
}


# ---------------------------------------------------------------------------
# Simulation runner
# ---------------------------------------------------------------------------

def run_simulation(
    mixture: dict,
    pop_size: int,
    gov_config,
    seed: int,
) -> dict:
    """Run a single simulation and return metrics."""
    config = OrchestratorConfig(
        n_epochs=N_EPOCHS,
        steps_per_epoch=STEPS_PER_EPOCH,
        seed=seed,
        payoff_config=PAYOFF,
        governance_config=gov_config,
    )

    orch = Orchestrator(config=config)
    agents = _create_population(mixture, pop_size, seed)
    for agent in agents:
        orch.register_agent(agent)

    epoch_metrics = orch.run()
    regime = classify_regime(epoch_metrics)

    # Final third metrics.
    n = len(epoch_metrics)
    tail_start = max(0, n - max(n // 3, 1))
    tail = epoch_metrics[tail_start:]

    total_acc = sum(m.accepted_interactions for m in tail)
    total_int = sum(m.total_interactions for m in tail)

    acceptance = total_acc / total_int if total_int > 0 else 0.0
    toxicity = np.mean([m.toxicity_rate for m in tail]) if tail else 0.0
    quality_gap = np.mean([m.quality_gap for m in tail]) if tail else 0.0
    welfare = np.mean([m.total_welfare for m in tail]) if tail else 0.0

    # Per-epoch trajectories.
    epoch_acc = [
        m.accepted_interactions / m.total_interactions
        if m.total_interactions > 0 else 0.0
        for m in epoch_metrics
    ]

    return {
        "regime": regime.value,
        "acceptance_rate": float(acceptance),
        "toxicity": float(toxicity),
        "quality_gap": float(quality_gap),
        "welfare": float(welfare),
        "epoch_acceptance": epoch_acc,
        "epoch_toxicity": [m.toxicity_rate for m in epoch_metrics],
    }


# ---------------------------------------------------------------------------
# Phase 1: Adversarial fraction sweep
# ---------------------------------------------------------------------------

def phase1_adversarial_sweep():
    """Sweep adversarial fraction across governance configs and pop sizes."""
    print("=" * 70)
    print("PHASE 1: Adversarial fraction sweep")
    print("=" * 70)

    total = (
        len(ADVERSARIAL_FRACTIONS) * len(GOVERNANCE_CONFIGS)
        * len(POPULATION_SIZES) * len(SEEDS)
    )
    print(f"  {len(ADVERSARIAL_FRACTIONS)} fractions × "
          f"{len(GOVERNANCE_CONFIGS)} governance × "
          f"{len(POPULATION_SIZES)} pop sizes × "
          f"{len(SEEDS)} seeds = {total} runs")

    results = []
    done = 0
    t0 = time.time()

    for adv_frac in ADVERSARIAL_FRACTIONS:
        for gov_label, gov_config in GOVERNANCE_CONFIGS.items():
            for pop_size in POPULATION_SIZES:
                for seed in SEEDS:
                    honest_frac = 1.0 - adv_frac
                    mixture = {
                        AgentType.HONEST: honest_frac,
                        AgentType.ADVERSARIAL: adv_frac,
                    }

                    result = run_simulation(mixture, pop_size, gov_config, seed)
                    result.update({
                        "adversarial_fraction": adv_frac,
                        "governance": gov_label,
                        "population_size": pop_size,
                        "seed": seed,
                        "mixture_label": f"honest_{honest_frac:.2f}_adv_{adv_frac:.2f}",
                    })
                    results.append(result)

                    done += 1
                    if done % 20 == 0 or done == total:
                        elapsed = time.time() - t0
                        rate = done / elapsed if elapsed > 0 else 0
                        eta = (total - done) / rate if rate > 0 else 0
                        print(f"  [{done}/{total}] {elapsed:.0f}s elapsed, "
                              f"~{eta:.0f}s remaining")

    return results


# ---------------------------------------------------------------------------
# Phase 2: Mixed profile sweep
# ---------------------------------------------------------------------------

def phase2_profile_sweep():
    """Sweep mixed profiles across governance configs."""
    print("\n" + "=" * 70)
    print("PHASE 2: Mixed profile sweep")
    print("=" * 70)

    pop_size = 16  # fixed for mixed profiles
    total = len(PROFILE_MIXTURES) * len(GOVERNANCE_CONFIGS) * len(SEEDS)
    print(f"  {len(PROFILE_MIXTURES)} profiles × "
          f"{len(GOVERNANCE_CONFIGS)} governance × "
          f"{len(SEEDS)} seeds = {total} runs (pop_size={pop_size})")

    results = []
    done = 0
    t0 = time.time()

    for mix_label, mixture in PROFILE_MIXTURES.items():
        for gov_label, gov_config in GOVERNANCE_CONFIGS.items():
            for seed in SEEDS:
                result = run_simulation(mixture, pop_size, gov_config, seed)

                # Compute effective adversarial+deceptive fraction.
                threat_frac = (
                    mixture.get(AgentType.ADVERSARIAL, 0.0)
                    + mixture.get(AgentType.DECEPTIVE, 0.0)
                )

                result.update({
                    "mixture_label": mix_label,
                    "governance": gov_label,
                    "population_size": pop_size,
                    "seed": seed,
                    "adversarial_fraction": mixture.get(AgentType.ADVERSARIAL, 0.0),
                    "deceptive_fraction": mixture.get(AgentType.DECEPTIVE, 0.0),
                    "threat_fraction": threat_frac,
                })
                results.append(result)

                done += 1
                if done % 10 == 0 or done == total:
                    elapsed = time.time() - t0
                    print(f"  [{done}/{total}] {elapsed:.0f}s elapsed")

    return results


# ---------------------------------------------------------------------------
# Analysis
# ---------------------------------------------------------------------------

def analyze_adversarial_sweep(results):
    """Compute summary statistics and find critical fractions."""
    from scipy import stats as sp_stats

    print("\n" + "=" * 70)
    print("ANALYSIS: Adversarial fraction sweep")
    print("=" * 70)

    summary = {}

    for gov_label in GOVERNANCE_CONFIGS:
        gov_results = [r for r in results if r["governance"] == gov_label]

        by_frac = {}
        for r in gov_results:
            frac = r["adversarial_fraction"]
            by_frac.setdefault(frac, []).append(r)

        print(f"\n  --- Governance: {gov_label} ---")
        print(f"  {'Adv Frac':>8} {'Regime':>12} {'Accept':>8} "
              f"{'Toxicity':>8} {'QGap':>8} {'Welfare':>8} {'N':>4}")
        print(f"  {'-'*8} {'-'*12} {'-'*8} {'-'*8} {'-'*8} {'-'*8} {'-'*4}")

        frac_stats = {}
        for frac in sorted(by_frac.keys()):
            runs = by_frac[frac]
            regimes = [r["regime"] for r in runs]
            regime_mode = max(set(regimes), key=regimes.count)
            collapse_rate = regimes.count("collapse") / len(regimes)

            acc = np.mean([r["acceptance_rate"] for r in runs])
            tox = np.mean([r["toxicity"] for r in runs])
            qgap = np.mean([r["quality_gap"] for r in runs])
            welf = np.mean([r["welfare"] for r in runs])

            print(f"  {frac:>8.3f} {regime_mode:>12} {acc:>8.3f} "
                  f"{tox:>8.3f} {qgap:>+8.3f} {welf:>8.1f} {len(runs):>4}")

            frac_stats[frac] = {
                "regime_mode": regime_mode,
                "collapse_rate": collapse_rate,
                "acceptance_mean": float(acc),
                "toxicity_mean": float(tox),
                "quality_gap_mean": float(qgap),
                "welfare_mean": float(welf),
                "n_runs": len(runs),
            }

        # Find critical fraction (last stable → first collapse).
        stable_fracs = [f for f, s in frac_stats.items()
                        if s["collapse_rate"] < 0.5]
        collapse_fracs = [f for f, s in frac_stats.items()
                          if s["collapse_rate"] >= 0.5]

        crit = None
        if stable_fracs and collapse_fracs:
            crit = (max(stable_fracs) + min(collapse_fracs)) / 2.0

        print(f"\n  Critical adversarial fraction: "
              f"{crit:.3f}" if crit else "\n  Critical fraction: not reached")

        # Statistical test: welfare at 0% vs 50% adversarial.
        if 0.0 in by_frac and 0.5 in by_frac:
            w0 = [r["welfare"] for r in by_frac[0.0]]
            w50 = [r["welfare"] for r in by_frac[0.5]]
            if len(w0) >= 2 and len(w50) >= 2:
                t_stat, p_val = sp_stats.ttest_ind(w0, w50, equal_var=False)
                d = (np.mean(w0) - np.mean(w50)) / np.sqrt(
                    (np.std(w0)**2 + np.std(w50)**2) / 2
                ) if (np.std(w0) + np.std(w50)) > 0 else 0.0
                print(f"  Welfare 0% vs 50% adv: t={t_stat:.2f}, "
                      f"p={p_val:.4f}, d={d:.2f}")

        summary[gov_label] = {
            "fraction_stats": frac_stats,
            "critical_fraction": crit,
        }

    return summary


def analyze_profile_sweep(results):
    """Analyze mixed profile results."""
    print("\n" + "=" * 70)
    print("ANALYSIS: Mixed profile sweep")
    print("=" * 70)

    summary = {}
    for mix_label in PROFILE_MIXTURES:
        mix_results = [r for r in results if r["mixture_label"] == mix_label]

        by_gov = {}
        for r in mix_results:
            by_gov.setdefault(r["governance"], []).append(r)

        print(f"\n  --- Profile: {mix_label} ---")
        print(f"  {'Governance':>10} {'Regime':>12} {'Accept':>8} "
              f"{'Toxicity':>8} {'QGap':>8} {'Welfare':>8}")
        print(f"  {'-'*10} {'-'*12} {'-'*8} {'-'*8} {'-'*8} {'-'*8}")

        gov_stats = {}
        for gov_label in GOVERNANCE_CONFIGS:
            runs = by_gov.get(gov_label, [])
            if not runs:
                continue
            regimes = [r["regime"] for r in runs]
            regime_mode = max(set(regimes), key=regimes.count)

            acc = np.mean([r["acceptance_rate"] for r in runs])
            tox = np.mean([r["toxicity"] for r in runs])
            qgap = np.mean([r["quality_gap"] for r in runs])
            welf = np.mean([r["welfare"] for r in runs])

            print(f"  {gov_label:>10} {regime_mode:>12} {acc:>8.3f} "
                  f"{tox:>8.3f} {qgap:>+8.3f} {welf:>8.1f}")

            gov_stats[gov_label] = {
                "regime_mode": regime_mode,
                "acceptance_mean": float(acc),
                "toxicity_mean": float(tox),
                "quality_gap_mean": float(qgap),
                "welfare_mean": float(welf),
            }

        summary[mix_label] = gov_stats

    return summary


# ---------------------------------------------------------------------------
# CSV export
# ---------------------------------------------------------------------------

def export_csv(adv_results, profile_results):
    """Export results to CSV."""
    # Phase 1 CSV.
    csv_path = os.path.join(RUN_DIR, "csv", "adversarial_sweep.csv")
    fields = [
        "adversarial_fraction", "governance", "population_size", "seed",
        "mixture_label", "regime", "acceptance_rate", "toxicity",
        "quality_gap", "welfare",
    ]
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(adv_results)
    print(f"\n  Wrote {csv_path} ({len(adv_results)} rows)")

    # Phase 2 CSV.
    csv_path = os.path.join(RUN_DIR, "csv", "profile_sweep.csv")
    fields = [
        "mixture_label", "governance", "population_size", "seed",
        "adversarial_fraction", "deceptive_fraction", "threat_fraction",
        "regime", "acceptance_rate", "toxicity", "quality_gap", "welfare",
    ]
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(profile_results)
    print(f"  Wrote {csv_path} ({len(profile_results)} rows)")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("Composition Boundary Study")
    print(f"  Run dir: {RUN_DIR}")
    print(f"  Epochs: {N_EPOCHS}, Steps/epoch: {STEPS_PER_EPOCH}")
    print(f"  Seeds: {SEEDS}")
    t_start = time.time()

    # Phase 1.
    adv_results = phase1_adversarial_sweep()

    # Phase 2.
    profile_results = phase2_profile_sweep()

    # Export CSVs.
    export_csv(adv_results, profile_results)

    # Analysis.
    adv_summary = analyze_adversarial_sweep(adv_results)
    profile_summary = analyze_profile_sweep(profile_results)

    # Save summary JSON.
    def _default(o):
        if isinstance(o, (np.bool_,)):
            return bool(o)
        if isinstance(o, (np.integer,)):
            return int(o)
        if isinstance(o, (np.floating,)):
            return float(o)
        raise TypeError(f"Object of type {type(o)} is not JSON serializable")

    summary = {
        "adversarial_sweep": adv_summary,
        "profile_sweep": profile_summary,
        "parameters": {
            "population_sizes": POPULATION_SIZES,
            "seeds": SEEDS,
            "n_epochs": N_EPOCHS,
            "steps_per_epoch": STEPS_PER_EPOCH,
            "adversarial_fractions": ADVERSARIAL_FRACTIONS,
            "governance_configs": list(GOVERNANCE_CONFIGS.keys()),
            "profile_mixtures": list(PROFILE_MIXTURES.keys()),
        },
    }
    summary_path = os.path.join(RUN_DIR, "summary.json")
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2, default=_default)
    print(f"\n  Wrote {summary_path}")

    elapsed = time.time() - t_start
    print(f"\n  Total time: {elapsed:.0f}s ({elapsed/60:.1f}m)")
    print(f"  Total runs: {len(adv_results) + len(profile_results)}")


if __name__ == "__main__":
    main()
