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
  - run: 20260213-173805_baseline_governance
    metric: all
    detail: "CB null across all 6 metrics: welfare d=-0.10 p=0.66, honest_payoff d=-0.27 p=0.24, toxicity d=0.10 p=0.64. N=80, 10 seeds"
  - run: 20260217_memori_study
    metric: all
    detail: "CB null in LLM memori scenario: largest d=0.55 (quality_gap, p=0.14). 0/12 tests significant. N=30, 5 seeds"
  - run: 20260213-143751_delegation_games_study
    metric: toxicity_rate
    detail: "CB effect on toxicity negligible: d=0.078, p=0.73. CB welfare effect nominal (d=0.557, p=0.015) but not Bonferroni-significant. N=10 seeds, delegation games scenario"
  - run: 20260213-204503_agent_lab_research_safety_study
    metric: welfare
    detail: "CB null across welfare, toxicity, honest payoff in 160-run factorial. Quality gap invariant (always zero). N=10 seeds per config, 4x2x2 design"
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
- claim-governance-cost-paradox
- claim-tax-and-penalty-effects-are-orthogonal
- claim-optimal-tax-range-0-to-5pct
created: 2026-02-20
updated: 2026-02-21
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

In both the [[20260213-202050_baseline_governance_v2]] sweep (700 runs, d=0.008, p=0.92) and the [[20260213-173805_baseline_governance]] sweep (80 runs, d=-0.10, p=0.66), circuit breakers show essentially zero main effect on welfare. This is a cornerstone finding supporting [[claim-tax-dominates-cb-kernel]]. However, the experimental design only tests CB as binary on/off with default thresholds, without varying the freeze threshold, freeze duration, or activation sensitivity.

The significant tax x CB interactions on 5 metrics ([[claim-tax-cb-interact-on-quality-gap]]) demonstrate that CB *does* matter conditionally, undermining the interpretation that CB is simply ineffective. The null main effect may mask threshold-dependent effects that a finer-grained sweep would reveal. All three council reviewers flagged "circuit breaker recalibration" as the top experimental priority.

## Implications

If the CB null effect is a design artifact, then [[claim-circuit-breakers-dominate]] (from other runs with different CB configurations) and [[claim-tax-dominates-cb-kernel]] may be measuring different aspects of CB effectiveness rather than contradicting each other. The resolution requires a CB threshold sweep within the baseline governance v2 framework.

If CB is effective when properly calibrated, [[claim-governance-cost-paradox]] may be partially resolvable: the welfare cost of governance stacks could be reduced by replacing high tax rates with optimized CB thresholds. This would also expand the safe operating range identified in [[claim-optimal-tax-range-0-to-5pct]] — if CB can compensate for security at low tax rates, designers gain more policy headroom. A CB threshold sweep would also reveal whether CB operates as a third orthogonal axis alongside tax and penalty ([[claim-tax-and-penalty-effects-are-orthogonal]]), or whether it interacts with both.

## Recommended next experiment

- Sweep CB freeze threshold (0.3, 0.5, 0.7, 0.9) x CB freeze duration (1, 5, 10, 20 rounds) at fixed tax rates (0%, 5%, 10%)
- Test whether CB effect size increases with threshold optimization
- If confirmed, update [[claim-tax-dominates-cb-kernel]] with boundary condition
- The threshold sweep would simultaneously address [[failure-threshold-dancing]]: varying freeze thresholds tests both CB effectiveness and adversarial evasion resilience
- If CB threshold variation reveals significant effects, [[claim-tax-and-penalty-effects-are-orthogonal]] should be extended to test 3-way orthogonality (tax x penalty x CB threshold)

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: methodology, circuit-breaker, experimental-design -->
