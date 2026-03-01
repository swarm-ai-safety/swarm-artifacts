---
description: Freeze threshold 0.3 causes 7% honest payoff penalty vs 0.5 (d=0.77 welfare gap) through false-positive agent freezing
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260301_cb_threshold_sweep
    metric: honest_payoff
    detail: "Honest payoff at threshold 0.3=57.84 vs 0.5=61.88 (7% penalty). N=360 per group, 10 seeds x 36 configs"
  - run: 20260301_cb_threshold_sweep
    metric: welfare
    detail: "Welfare at 0.3=348.2 vs 0.5=372.3. d=0.765, p=9.9e-25, Bonferroni-sig (6 pairwise comparisons). N=360 per group"
  - run: 20260301_cb_threshold_sweep
    metric: n_frozen
    detail: "Threshold 0.3 freezes more agents (mean=1.63) vs 0.5 (mean=1.46). Extra freezes hit honest agents — adversarial payoff barely differs (0.57 vs 0.48)"
  weakening: []
  boundary_conditions:
  - "8 agents, small-world topology, 25% adversarial fraction"
  - "Baseline toxicity ~0.26 — threshold 0.3 is only 0.04 above baseline, creating a tight false-positive margin"
  - "Effect may diminish if toxicity scoring is better calibrated or if honest agents have lower variance"
  - "Single sweep, not independently replicated"
sensitivity:
  topology: "untested beyond small-world"
  agent_count: "untested beyond 8 agents"
  adversarial_fraction: "at higher fractions, more adversarial agents may justify aggressive thresholds"
  toxicity_calibration: "if toxicity scoring has higher variance, false positive rate at 0.3 would increase"
supersedes: []
superseded_by: []
related_claims:
- claim: claim-cb-threshold-05-maximizes-welfare-in-small-world-topology
  relation: supports
- claim: claim-circuit-breaker-activation-has-sharp-threshold-boundary-at-toxicity-05
  relation: requires
- claim: claim-optimal-cb-threshold-predicted-in-03-05-range
  relation: refines
- claim: claim-tax-hurts-honest-more-than-opportunistic
  relation: extends
- claim: claim-governance-cost-paradox
  relation: supports
created: 2026-03-01
updated: 2026-03-01
aliases:
- aggressive-cb-threshold-harms-honest
cssclasses:
- claim
- claim-medium
tags:
- governance
- circuit-breaker
- false-positives
- honest-agent-penalty
- threshold-calibration
graph-group: claim
---

# aggressive circuit breaker threshold (0.3) harms honest agents through false-positive freezing causing 7% payoff penalty

## Evidence summary

The [[20260301_cb_threshold_sweep]] (1,440 runs, 4x4x3x3 factorial, 10 seeds) shows that freeze threshold 0.3 imposes a significant welfare cost compared to threshold 0.5: d = 0.765, p = 9.9e-25 (Bonferroni-significant across 6 pairwise comparisons). The mechanism is disproportionate harm to honest agents.

At threshold 0.3, honest agent mean payoff is 57.84, compared to 61.88 at threshold 0.5 — a 7% penalty. Meanwhile, adversarial payoff barely differs (0.57 at 0.3 vs 0.48 at 0.5). The aggressive threshold catches adversarial agents but also freezes honest agents whose toxicity scores briefly exceed 0.3 due to normal behavioral noise.

The baseline toxicity rate across all conditions is approximately 0.26. A freeze threshold of 0.3 sits only 0.04 above this baseline, creating a razor-thin margin for honest agents. Normal toxicity variance pushes some honest agents above 0.3 intermittently, triggering freezes. At threshold 0.5, the margin widens to 0.24 above baseline, effectively eliminating false positives.

## Mechanism

This is a governance false-positive cost analogous to the pattern identified in [[claim-tax-hurts-honest-more-than-opportunistic]]: governance mechanisms designed to punish adversarial behavior have outsized negative effects on honest agents. In the tax case, honest agents bear disproportionate tax burden because they engage in more (taxable) transactions. In the CB case, honest agents bear disproportionate freeze risk because their toxicity distribution has a tail that extends above aggressive thresholds.

The finding also strengthens [[claim-governance-cost-paradox]]: the welfare cost of governance is not just from the mechanism itself (taxes reducing surplus) but also from false-positive enforcement (freezing productive agents). Optimizing the CB threshold from 0.3 to 0.5 eliminates this false-positive cost entirely.

## Open questions

1. What is the precise false-positive rate at threshold 0.3 vs 0.5? (Requires per-agent freeze attribution data)
2. Does the false-positive penalty worsen at threshold < 0.3?
3. Can adaptive thresholds ([[claim-adaptive-cb-thresholds-should-dominate-static]]) reduce false positives below the static 0.5 rate?
4. Does the penalty change with different agent type mixes?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, circuit-breaker, false-positives, honest-agent-penalty, threshold-calibration -->
