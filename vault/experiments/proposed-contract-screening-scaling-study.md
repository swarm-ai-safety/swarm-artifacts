---
description: 3x3 factorial testing screening separation at N=10/25/50 against naive, adaptive, and sybil adversaries, 180 runs
type: experiment
status: proposed
run_id: pending
experiment_type: study
created: '2026-02-27'
aliases:
- proposed-screening-scaling
cssclasses:
- experiment
- experiment-study
tags:
- contract-screening
- scaling
- adaptive-adversary
- sybil
graph-group: experiment
---

# contract screening type separation should degrade at larger populations and under adaptive adversaries who learn to mimic honest signals

## Design

- **Hypothesis**: Perfect type separation (1.0) at N=10 is unlikely to hold at N=50 with adaptive adversaries. Rothschild-Stiglitz theory predicts screening equilibrium fragility when adversaries can learn honest-type signals. Sybil interaction (multiple deceptive identities) should further degrade separation by overwhelming the screening mechanism.
- **Type**: 2-factor study (population size x adversary sophistication)
- **Factor 1**: Population size — N=10 (baseline), N=25 (3x), N=50 (5x)
- **Factor 2**: Adversary sophistication — naive-deceptive (current), adaptive-mimic (learns honest signals), sybil-deceptive (3 sybil identities)
- **Seeds**: 20
- **Total runs**: 180 (3 sizes x 3 adversary types x 20 seeds)
- **Config**: tax 3%, CB enabled, screening active, small-world, 20 epochs
- **Scenario**: `scenarios/hypotheses/contract_screening_scaling.yaml`

## Motivation

[[claim-contract-screening-achieves-perfect-type-separation]] reports 1.0 separation across 11 seeds at N=10 — a remarkably strong result. But the research note on screening equilibria ([[claim-contract-screening-achieves-perfect-type-separation]]) flags Rothschild-Stiglitz fragility predictions: screening equilibria can unravel when adversaries adapt to the screening mechanism. [[claim-screening-equilibrium-generates-honest-payoff-premium]] reports a 6.7x payoff premium — a strong enough signal that sophisticated adversaries would invest in mimicry.

The market domain currently has only 2 claims. This study would triple the evidence base for screening mechanisms and establish scaling limits — critical for any real-world deployment where population size and adversary sophistication exceed the N=10 baseline.

## Expected claims

- **New**: Claim on screening degradation curve (how separation declines with N)
- **New**: Claim on adaptive adversary impact on separation (mimic learning effectiveness)
- **New**: Claim on screening x sybil interaction (identity amplification in screening)
- **Update**: [[claim-contract-screening-achieves-perfect-type-separation]] — boundary conditions narrowed to N=10 naive adversaries (if degradation found) or broadened to N=50 (if robust)
- **Update**: [[claim-screening-equilibrium-generates-honest-payoff-premium]] — payoff premium vs N and adversary sophistication

## Prerequisites

- SWARM contract screening must support N=25 and N=50 agent populations
- Adaptive-mimic adversary type: learns honest signal distribution over epochs, adjusts own signals to match
- Sybil-deceptive interaction: 3 identities per sybil controller, each participating in screening independently
- Payoff tracking per agent type must scale with population

## Analysis plan

- Two-way ANOVA (size x sophistication) on each metric, Bonferroni-corrected (k=5 metrics)
- Key contrast: N=10 naive vs N=50 adaptive (maximum stress test)
- Separation degradation curve: plot type_separation_accuracy vs N for each adversary type
- Payoff premium erosion: how does honest/deceptive ratio change with adaptive mimicry?
- Time-series: does separation degrade within a run (epoch-by-epoch tracking of adaptive mimic learning)?

## Falsification

If type separation remains >95% at N=50 with adaptive adversaries, the screening mechanism is remarkably robust and the Rothschild-Stiglitz fragility prediction does not apply in this setting.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: contract-screening, scaling, adaptive-adversary, sybil, market -->
