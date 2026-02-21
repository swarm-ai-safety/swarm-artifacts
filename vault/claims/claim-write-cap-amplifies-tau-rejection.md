---
description: Write cap compounds tau=0.65 rejection cascade, reducing welfare 51% further (306→151) at k=2
type: claim
status: active
confidence: low
domain: memory
evidence:
  supporting:
  - run: 20260214-020518_tau_k_calibration
    metric: composite_score
    detail: "tau=0.65 arm_a: composite=-0.237, welfare=306. arm_b k=2: composite=-0.443, welfare=151 (51% worse). k=4: welfare=247. k=6: welfare=279"
  weakening: []
  boundary_conditions:
  - memory_tiers scenario, tau=0.65 only, 5 seeds
  - Interaction only observed at the extreme tau value
sensitivity:
  topology: untested
  agent_count: untested
  governance_interaction: this IS the interaction finding (tau x k_max)
supersedes: []
superseded_by: []
related_claims:
- claim-tau-065-triggers-acceptance-phase-transition
- claim-write-cap-below-12-destroys-welfare
- claim-governance-cost-paradox
created: 2026-02-20
updated: 2026-02-20
aliases:
- write-cap-amplifies-tau-rejection
cssclasses:
- claim
- claim-low
tags:
- memory
- calibration
- interaction
graph-group: claim
---

# write cap amplifies the welfare cost of tau rejection at extreme tau values

## Evidence summary

In [[20260214-020518_tau_k_calibration]], at tau_min=0.65 (where [[claim-tau-065-triggers-acceptance-phase-transition]] causes ~36% rejection), adding a tight write cap compounds the welfare destruction:

| Config | Welfare | Composite |
|--------|---------|-----------|
| tau=0.65, no cap (arm_a) | 306 | -0.237 |
| tau=0.65, k=2 (arm_b) | 151 | -0.443 |
| tau=0.65, k=4 | 247 | -0.316 |
| tau=0.65, k=6 | 279 | -0.280 |

The tau rejection reduces the pool of accepted interactions; the write cap then further constrains how much welfare those accepted interactions generate. This is a governance mechanism interaction: two independently harmful parameters compound super-additively, extending [[claim-governance-cost-paradox]] to the memory domain.

## Open questions

- Does the interaction exist at tau values below 0.65, or only in the rejection regime?
- Is this a general property of stacked governance mechanisms (paralleling the tax-penalty interaction)?

---

Topics:
- [[_index]]

<!-- topics: memory, calibration, interaction -->
