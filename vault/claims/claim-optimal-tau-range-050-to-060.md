---
description: Optimal tau_min for memory tiers is 0.50-0.60 with flat composite scores and no welfare penalty
type: claim
status: active
confidence: low
domain: calibration
evidence:
  supporting:
  - run: 20260214-014153_tau_k_calibration
    metric: composite_score
    detail: "tau=0.45:0.511, tau=0.50:0.515, tau=0.55:0.504, tau=0.60:0.516 (arm_a). Flat optimum, recommended tau=0.60 k=16"
  - run: 20260214-020518_tau_k_calibration
    metric: composite_score
    detail: "tau=0.45:0.485, tau=0.55:0.489 (arm_a). tau=0.65:-0.237 (catastrophic). Recommended tau=0.55 k=6"
  weakening: []
  boundary_conditions:
  - memory_tiers scenario, 5 seeds per cell, non-adversarial
  - Composite score combines welfare and toxicity; exact weighting not specified
  - Sharp cliff at tau=0.65 defines upper boundary
sensitivity:
  topology: untested
  agent_count: 8 agents
  governance_interaction: write cap k_max >= 12 does not affect the optimal tau range
supersedes: []
superseded_by: []
related_claims:
- claim-tau-065-triggers-acceptance-phase-transition
- claim-optimal-tax-range-0-to-5pct
- claim-write-cap-below-12-destroys-welfare
created: 2026-02-20
updated: 2026-02-20
aliases:
- optimal-tau-range-050-to-060
cssclasses:
- claim
- claim-low
tags:
- calibration
- memory
- optimization
graph-group: claim
---

# optimal tau_min for memory tiers lies in the 0.50-0.60 range

## Evidence summary

Across two calibration runs ([[20260214-014153_tau_k_calibration]] and [[20260214-020518_tau_k_calibration]]), composite scores are flat in the 0.45-0.60 tau_min range (0.485-0.516) with a catastrophic cliff at 0.65 (-0.237). The flat optimum means governance designers have a wide safe operating range, paralleling [[claim-optimal-tax-range-0-to-5pct]] in the tax domain.

Combined recommendation from both runs: tau_min=0.55-0.60 with k_max >= 12 (which imposes zero overhead per [[claim-write-cap-below-12-destroys-welfare]]).

## Open questions

- Does the optimal range shift under adversarial conditions?
- Is the composite score weighting appropriate for all use cases?
- Does the flat optimum persist with more seeds (currently N=5)?

---

Topics:
- [[_index]]

<!-- topics: calibration, memory, optimization -->
