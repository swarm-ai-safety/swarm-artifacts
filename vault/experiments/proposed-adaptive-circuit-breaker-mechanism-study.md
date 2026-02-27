---
description: 5x3 factorial testing adaptive CB variants (CUSUM, stochastic, personal) against threshold-dancing adversaries, 300 runs
type: experiment
status: proposed
run_id: pending
experiment_type: study
created: '2026-02-27'
aliases:
- proposed-adaptive-cb
cssclasses:
- experiment
- experiment-study
tags:
- circuit-breaker
- threshold-dancing
- mechanism-design
- adaptive-governance
graph-group: experiment
---

# adaptive circuit breaker variants should defeat threshold-dancing attacks that evade the current binary design

## Design

- **Hypothesis**: Current binary CB design (fixed threshold, freeze/unfreeze) enables threshold dancing (70% evasion rate). Adaptive variants that randomize thresholds, track cumulative harm, or learn per-agent patterns should significantly reduce evasion without increasing false positives.
- **Type**: 2-factor study (CB variant x adversary strategy)
- **Factor 1**: CB variant — static (baseline), stochastic-uniform, stochastic-gaussian, CUSUM-cumulative, adaptive-personal
- **Factor 2**: Adversary strategy — none, threshold-dancer, naive-adversarial
- **Seeds**: 20
- **Total runs**: 300 (5 variants x 3 adversary types x 20 seeds)
- **Config**: 10 agents (6 honest + 2 adversarial + 2 opportunistic), tax 3%, audit 10%, small-world
- **Scenario**: `scenarios/hypotheses/adaptive_circuit_breaker.yaml`

## Motivation

[[failure-threshold-dancing]] documents 70% evasion success against the current CB design. [[claim-cb-null-may-reflect-design-limitation]] identifies the binary on/off design as a potential artifact. All 3 council reviewers flagged the CB threshold sweep as the highest-priority experimental gap. This study addresses the gap by testing 4 alternative CB mechanisms against the specific adversarial strategy that defeats the current design.

## Expected claims

If results are significant, this study would create or update:
- **New**: Claim on which CB variant(s) significantly reduce threshold-dancing evasion
- **New**: Claim on false-positive tradeoff — whether adaptive variants freeze honest agents more often
- **Update**: [[claim-cb-null-may-reflect-design-limitation]] — either confirmed (adaptive variants work) or rejected (all variants fail)
- **Update**: [[claim-circuit-breakers-dominate]] — enriched with adaptive variant comparison

## Prerequisites

- SWARM must implement `circuit_breaker_variant` parameter with 5 options
- Adversary agent must support `threshold_dancer` strategy
- CUSUM tracking requires cumulative harm state across epochs

## Analysis plan

- Two-way ANOVA (CB variant x adversary type) on each metric, Bonferroni-corrected (k=5 metrics)
- Key contrast: each adaptive variant vs static CB at threshold_dancer level
- False positive analysis: compare honest-agent freeze rates across variants at no-adversary level
- Detection latency analysis: Kaplan-Meier curves for time-to-first-freeze by variant

## Falsification

If no CB variant significantly reduces evasion_rate vs static CB against threshold dancers, the problem is fundamental to the CB approach rather than a design limitation.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: circuit-breaker, threshold-dancing, mechanism-design, adaptive-governance -->
