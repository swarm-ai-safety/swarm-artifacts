---
description: Step-down procedure that is uniformly more powerful than Bonferroni while still controlling family-wise error
  rate
type: method
status: active
category: statistical
aliases:
- Holm correction
- Holm step-down
- sequential Bonferroni
- holm-bonferroni
cssclasses:
- method
graph-group: method
tags:
- multiple-comparisons
- family-wise-error-rate
- hypothesis-testing
- statistical-methods
created: 2026-02-19
updated: 2026-02-19
---

# Holm-Bonferroni step-down procedure recovers power lost by standard Bonferroni without sacrificing FWER control

## What it does

The Holm-Bonferroni method is a sequentially rejective version of the [[bonferroni-correction]]. It sorts p-values from smallest to largest and compares each against a progressively less strict threshold. This recovers statistical power — it will always reject at least as many hypotheses as Bonferroni, and often more — while maintaining the same family-wise error rate guarantee.

**Inputs:** a set of m p-values and a desired FWER (typically alpha = 0.05).
**Outputs:** a significant/not-significant verdict for each test. Guarantees FWER <= alpha.

## Why it matters

In large SWARM sweeps with many pairwise comparisons, standard [[bonferroni-correction]] can be excessively conservative. The [[20260213-202050_baseline_governance_v2]] sweep generated hundreds of pairwise comparisons across 7 tax rate levels and 2 circuit breaker states — Bonferroni retained only 18. The Holm-Bonferroni procedure would retain at least those 18, and potentially more, without inflating the false positive rate. This matters when trying to identify effects at medium parameter separations (e.g., tax 0.05 vs 0.10) that Bonferroni may miss.

## How to apply it

**Procedure:**

1. Order all m p-values from smallest to largest: p_(1) <= p_(2) <= ... <= p_(m).
2. For each p_(k) in order, compare against alpha / (m - k + 1).
3. Reject hypotheses starting from the smallest p-value.
4. Stop at the first p_(k) that fails: p_(k) >= alpha / (m - k + 1). Retain that hypothesis and all remaining ones.

```
Step-down thresholds:

  p_(1)  compared to  alpha / m         (same as Bonferroni)
  p_(2)  compared to  alpha / (m - 1)   (slightly less strict)
  p_(3)  compared to  alpha / (m - 2)   (less strict still)
  ...
  p_(m)  compared to  alpha / 1         (= alpha, uncorrected)
```

**Example with m=3 comparisons, alpha=0.05:**

| Rank | p-value | Threshold | Decision |
|------|---------|-----------|----------|
| 1 | 0.003 | 0.05/3 = 0.0167 | Reject |
| 2 | 0.020 | 0.05/2 = 0.025 | Reject |
| 3 | 0.040 | 0.05/1 = 0.05 | Reject |

Standard Bonferroni at 0.0167 would have rejected only rank 1. Holm recovers ranks 2 and 3.

## Assumptions and limitations

- **Still controls FWER, not FDR.** Like Bonferroni, Holm-Bonferroni controls the probability of any false positive, not the proportion. When screening many hypotheses in exploratory analysis, [[benjamini-hochberg]] is more appropriate.
- **Sequential dependency.** The step-down logic means that if a highly significant result is invalidated (e.g., due to a data quality issue), all subsequent rejections may change. This makes the procedure sensitive to outlier p-values.
- **Marginal gains diminish.** The power improvement over Bonferroni is most noticeable when several p-values cluster just above the Bonferroni threshold. When effects are either very strong or very weak (as in many SWARM sweeps), the two methods often agree.
- **Not yet the default in SWARM scripts.** Current analyze.py scripts implement Bonferroni as the primary FWER method and [[benjamini-hochberg]] as the FDR method. Holm-Bonferroni is recommended as a drop-in replacement for Bonferroni when more power is needed.

## Evidence of effectiveness

Holm-Bonferroni is recommended but not yet the primary correction in SWARM analysis pipelines. Its value is clearest in sweeps with many borderline results:

- [[20260213-202050_baseline_governance_v2]] — 18 results survived Bonferroni. Several additional comparisons (e.g., welfare effects at adjacent tax rate levels with d in the 0.5-0.7 range) fall just outside the Bonferroni threshold and are candidates for Holm recovery.
- [[20260213-173805_baseline_governance]] — the v1 baseline governance sweep with 280 runs showed effects with d=1.41 and d=1.33 that comfortably survive both Bonferroni and Holm, but weaker effects on honest_payoff (d=1.29) at higher comparison counts could benefit from the step-down approach.
- [[claim-circuit-breakers-dominate]] — the d=1.64 result from run [[20260211-000149_kernel_market_governance_comparison]] survives any correction method. Holm is most useful for the secondary comparisons in the same sweep (e.g., audits-only vs staking-only).

---

Topics:
- [[_index]]

<!-- topics: multiple-comparisons, family-wise-error-rate, hypothesis-testing, statistical-methods -->
