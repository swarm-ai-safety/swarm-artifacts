---
description: Freeze threshold 0.5 produces highest welfare among CB-active conditions (d=0.77 vs 0.3, Bonferroni-sig, 1440 runs)
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260301_cb_threshold_sweep
    metric: welfare
    detail: "1-way ANOVA: F(3,1436)=56.87, eta2=0.106, p<0.0001. Threshold 0.5 mean welfare=372.3 vs 0.3=348.2, d=0.765, p=9.9e-25 Bonferroni-sig (6 pairs). N=360 per threshold, 10 seeds x 36 configs"
  - run: 20260301_cb_threshold_sweep
    metric: honest_payoff
    detail: "Honest payoff at 0.5=61.88 vs 0.3=57.84. 7% penalty at aggressive threshold. N=360 per group"
  weakening:
  - run: 20260301_cb_threshold_sweep
    metric: welfare
    detail: "Threshold 0.5 vs 0.9 (CB-off): d=0.037, p=0.62. CB at 0.5 does not improve welfare over CB-off. Benefit is avoiding harm, not adding value"
  boundary_conditions:
  - "8 agents, small-world topology (k=4, p=0.15), 25% adversarial fraction"
  - "10 seeds per configuration — adequate power for medium effects"
  - "Welfare optimality of 0.5 holds across all 3 tax rates and 4 violation thresholds (collapsed)"
  - "CB at 0.5 matches CB-off (0.9) — the mechanism is harm avoidance, not active benefit"
  - "Single sweep, not independently replicated across separate experimental batches"
sensitivity:
  topology: "untested beyond small-world; hub-and-spoke may shift optimal threshold"
  agent_count: "untested beyond 8 agents"
  adversarial_fraction: "untested beyond 25%; higher fractions may shift optimal threshold lower"
  agent_sophistication: "untested with LLM agents"
supersedes: []
superseded_by: []
related_claims:
- claim: claim-optimal-cb-threshold-predicted-in-03-05-range
  relation: refines
- claim: claim-cb-null-may-reflect-design-limitation
  relation: supports
- claim: claim-circuit-breakers-dominate
  relation: refines
- claim: claim-circuit-breaker-activation-has-sharp-threshold-boundary-at-toxicity-05
  relation: requires
- claim: claim-aggressive-cb-threshold-harms-honest-agents-through-false-positive-freezing
  relation: supports
- claim: claim-tax-dominates-cb-kernel
  relation: contradicts
- claim: claim-freeze-duration-and-violation-threshold-interact-on-welfare
  relation: extends
created: 2026-03-01
updated: 2026-03-01
aliases:
- cb-threshold-05-maximizes-welfare
cssclasses:
- claim
- claim-medium
tags:
- governance
- circuit-breaker
- threshold-calibration
- parameter-sensitivity
- welfare
graph-group: claim
---

# freeze threshold 0.5 maximizes welfare among circuit breaker configurations in small-world topology

## Evidence summary

The [[20260301_cb_threshold_sweep]] swept freeze_threshold_toxicity across 4 levels (0.3, 0.5, 0.7, 0.9) in a 4x4x3x3 full factorial with 10 seeds per cell (1,440 total runs). One-way ANOVA shows a significant main effect of threshold on welfare: F(3, 1436) = 56.87, eta2 = 0.106, p < 0.0001.

Threshold 0.5 produces the highest mean welfare (372.3), significantly exceeding threshold 0.3 (348.2, d = 0.765, p = 9.9e-25, Bonferroni-significant across 6 pairwise comparisons). Threshold 0.5 also exceeds 0.7 (364.2, d = 0.340, p < 0.0001, Bonferroni-significant). However, threshold 0.5 is statistically indistinguishable from 0.9 (371.4, d = 0.037, p = 0.62).

Because CB never activates at thresholds 0.7 and 0.9 ([[claim-circuit-breaker-activation-has-sharp-threshold-boundary-at-toxicity-05]]), the comparison between 0.5 and 0.9 is effectively "CB at optimal calibration" vs "CB off." The finding that these are equivalent means CB at threshold 0.5 imposes zero net welfare cost — it freezes adversarial agents without harming honest agents. This is in contrast to threshold 0.3, which imposes a significant welfare penalty through false-positive freezing ([[claim-aggressive-cb-threshold-harms-honest-agents-through-false-positive-freezing]]).

## Mechanism

At threshold 0.5, the circuit breaker freezes agents whose toxicity exceeds 0.5. This catches genuinely adversarial agents (who operate at baseline toxicity ~0.26 but spike higher during attacks) while leaving honest agents unfrozen. The result is neutral to positive for the ecosystem: adversarial agents are temporarily removed, honest agents continue unimpeded, and welfare is maintained at the CB-off baseline.

At threshold 0.3, the CB is too sensitive. Normal honest-agent toxicity fluctuations occasionally exceed 0.3, causing false-positive freezes. Each false freeze removes a productive agent from the ecosystem for 1-5 epochs, reducing welfare. The 7% honest payoff penalty at threshold 0.3 vs 0.5 confirms this mechanism.

## Boundary conditions

This finding is specific to the 8-agent small-world topology with 25% adversarial fraction. The optimal threshold may shift with topology (hub-and-spoke topologies may need tighter thresholds to prevent cascade from hub agents) or adversarial fraction (higher fractions may require more aggressive freezing). The single-sweep design provides medium confidence per the confidence criteria; independent replication would upgrade to high.

## Open questions

1. Does threshold 0.5 remain optimal at higher adversarial fractions (50%, 75%)?
2. Does the optimal threshold shift with topology (scale-free, random, complete)?
3. Can adaptive thresholds ([[claim-adaptive-cb-thresholds-should-dominate-static]]) outperform static 0.5?
4. Does the welfare-neutral property of CB at 0.5 extend to LLM-powered agents?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, circuit-breaker, threshold-calibration, parameter-sensitivity, welfare -->
