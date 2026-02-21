---
description: Circuit breaker null effect in baseline v2 may reflect insufficient threshold variation in 2-level on/off design
type: claim
status: active
confidence: low
domain: methodology
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: "CB on vs off: d=0.008, p=0.92, N=700. But significant tax x CB interactions on 5 metrics suggest CB matters conditionally"
  weakening: []
  boundary_conditions:
  - Methodological critique, not empirical finding
  - CB tested as binary on/off with default thresholds; no threshold sweep
  - All 3 council reviewers flagged CB recalibration as top priority
sensitivity:
  topology: n/a (methodology note)
  agent_count: n/a
  governance_interaction: the claim IS about interaction design limitations
supersedes: []
superseded_by: []
related_claims:
- claim-tax-dominates-cb-kernel
- claim-circuit-breakers-dominate
- claim-tax-cb-interact-on-quality-gap
created: 2026-02-20
updated: 2026-02-20
aliases:
- cb-null-may-reflect-design-limitation
cssclasses:
- claim
- claim-low
tags:
- methodology
- circuit-breaker
- experimental-design
graph-group: claim
---

# circuit breaker null effect may reflect insufficient threshold variation in the experimental design

## Evidence summary

In the [[20260213-202050_baseline_governance_v2]] sweep (700 runs), circuit breakers show d=0.008 on welfare (p=0.92) — essentially zero main effect. This is a cornerstone finding supporting [[claim-tax-dominates-cb-kernel]]. However, the experimental design only tests CB as binary on/off with default thresholds, without varying the freeze threshold, freeze duration, or activation sensitivity.

The significant tax x CB interactions on 5 metrics ([[claim-tax-cb-interact-on-quality-gap]]) demonstrate that CB *does* matter conditionally, undermining the interpretation that CB is simply ineffective. The null main effect may mask threshold-dependent effects that a finer-grained sweep would reveal. All three council reviewers flagged "circuit breaker recalibration" as the top experimental priority.

## Implications

If the CB null effect is a design artifact, then [[claim-circuit-breakers-dominate]] (from other runs with different CB configurations) and [[claim-tax-dominates-cb-kernel]] may be measuring different aspects of CB effectiveness rather than contradicting each other. The resolution requires a CB threshold sweep within the baseline governance v2 framework.

## Recommended next experiment

- Sweep CB freeze threshold (0.3, 0.5, 0.7, 0.9) x CB freeze duration (1, 5, 10, 20 rounds) at fixed tax rates (0%, 5%, 10%)
- Test whether CB effect size increases with threshold optimization
- If confirmed, update [[claim-tax-dominates-cb-kernel]] with boundary condition

---

Topics:
- [[_index]]

<!-- topics: methodology, circuit-breaker, experimental-design -->
