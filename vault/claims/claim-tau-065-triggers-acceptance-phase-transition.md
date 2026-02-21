---
description: tau_min=0.65 causes acceptance rate to drop from 100% to ~64% with exactly 160 rejections per run in memory tiers
type: claim
status: active
confidence: low
domain: memory
evidence:
  supporting:
  - run: 20260214-020518_tau_k_calibration
    metric: acceptance_rate
    detail: "tau=0.45-0.55: acceptance=1.0. tau=0.65: acceptance=0.638-0.647, exactly 160 rejections/run across all seeds. N=5 seeds"
  - run: 20260214-014153_tau_k_calibration
    metric: acceptance_rate
    detail: "tau=0.45-0.60: acceptance=1.0 across all seeds and k values. N=5 seeds"
  weakening: []
  boundary_conditions:
  - memory_tiers scenario, 10 epochs, 8 steps/epoch, 5 seeds
  - Exact 160 rejections suggests structural threshold, not stochastic
  - Toxicity drops 21% (0.312→0.245) but welfare drops 15% (360→306)
sensitivity:
  topology: untested
  agent_count: 8 agents in calibration; threshold may shift with population
  governance_interaction: write cap amplifies welfare cost at tau=0.65
supersedes: []
superseded_by: []
related_claims:
- claim-memory-promotion-gate
- claim-quality-gate-dominates
- claim-optimal-tau-range-050-to-060
- claim-write-cap-amplifies-tau-rejection
created: 2026-02-20
updated: 2026-02-20
aliases:
- tau-065-triggers-acceptance-phase-transition
cssclasses:
- claim
- claim-low
tags:
- memory
- calibration
- phase-transition
graph-group: claim
---

# tau_min at 0.65 triggers an acceptance phase transition in memory tiers

## Evidence summary

Across two calibration runs ([[20260214-014153_tau_k_calibration]] and [[20260214-020518_tau_k_calibration]]), tau_min values of 0.45–0.60 produce 100% acceptance rates. At tau_min=0.65, acceptance drops abruptly to ~64%, with exactly 160 rejections per run across all 5 seeds — suggesting a structural threshold rather than a stochastic effect.

The phase transition produces a toxicity-welfare tradeoff: toxicity drops 21% (0.312→0.245) but welfare drops 15% (360→306). This parallels [[claim-tax-phase-transition]] in the governance domain — both show governance parameters with safe operating ranges below a critical threshold and steep costs above it.

## Mechanism

The tau_min parameter sets the minimum quality threshold for memory tier promotion. At 0.65, this threshold exceeds the quality of ~36% of interactions, causing them to be rejected. The exact 160 rejections (constant across seeds) suggests the threshold bisects a discrete distribution of interaction qualities in the memory_tiers scenario.

## Open questions

- Sweep tau_min from 0.60 to 0.70 in 0.01 increments to locate the exact transition point
- Is the threshold scenario-specific (memory_tiers) or does it generalize?
- Does [[claim-write-cap-amplifies-tau-rejection]] compound the damage at tau=0.65?

---

Topics:
- [[_index]]

<!-- topics: memory, calibration, phase-transition -->
