---
description: Standardized mean difference measuring practical effect magnitude, independent of sample size, used in all SWARM
  claims
type: method
status: active
category: statistical
aliases:
- Cohen's d
- effect size
- standardized mean difference
- cohens-d
cssclasses:
- method
graph-group: method
tags:
- effect-size
- hypothesis-testing
- practical-significance
- statistical-methods
created: 2026-02-19
updated: 2026-02-19
---

# Cohen's d quantifies practical effect magnitude as a standardized mean difference

## What it does

Cohen's d expresses the difference between two group means in units of their pooled standard deviation. Unlike p-values, which conflate effect size with sample size, d provides a scale-free measure of how large a difference actually is.

**Inputs:** two sample means (M1, M2) and their pooled standard deviation (s_pooled).
**Outputs:** a dimensionless number where |d| < 0.2 is small, 0.5 is medium, 0.8 is large, and values above 1.0 indicate very large effects.

## Why it matters

SWARM experiments vary widely in sample size — from 10-seed pilot runs to 700-run factorial sweeps. A p-value of 0.001 in a 700-run sweep may correspond to a trivially small effect. Cohen's d separates statistical significance from practical significance: a governance mechanism that produces d=0.2 on welfare is statistically detectable but operationally irrelevant, while d=1.64 (as seen in [[claim-circuit-breakers-dominate]]) represents a dramatic shift in system behavior.

The SWARM project rule is explicit: **never report raw p-values without effect sizes and correction methods.** Every claim card includes Cohen's d alongside Bonferroni-corrected p-values.

## How to apply it

**Formula:**

```
d = (M1 - M2) / s_pooled

where:
  s_pooled = sqrt(((n1 - 1) * s1^2 + (n2 - 1) * s2^2) / (n1 + n2 - 2))

  M1, M2     = group means
  s1, s2     = group standard deviations
  n1, n2     = group sample sizes
```

**Interpretation thresholds (Cohen, 1988):**

| |d| | Interpretation |
|-----|----------------|
| 0.2 | Small |
| 0.5 | Medium |
| 0.8 | Large |
| 1.2+ | Very large |

SWARM analysis scripts compute d automatically for every pairwise comparison. The value is stored in each claim card's evidence block:

```yaml
evidence:
  supporting:
    - run: 20260213-202050_baseline_governance_v2
      metric: welfare
      detail: "d=1.18, p<1e-14, N=700, 50 seeds, Bonferroni-corrected"
```

## Assumptions and limitations

- **Assumes approximately normal distributions.** When SWARM outcome distributions are heavily skewed (e.g., wealth distributions with adversarial outliers), d may overstate or understate the practical effect. Non-parametric alternatives (Cliff's delta, rank-biserial correlation) should be considered.
- **Sensitive to variance heterogeneity.** If one group has much larger variance than the other (common when comparing governed vs ungoverned regimes), the pooled s_pooled may not represent either group well. Welch's t-test addresses the p-value issue but d itself remains pooled.
- **Does not capture distribution shape.** Two comparisons with the same d can have very different practical implications if one involves a bimodal distribution (e.g., agents clustering into distinct strategies).
- **Thresholds are conventions, not laws.** Cohen himself described the 0.2/0.5/0.8 benchmarks as "arbitrary." In the SWARM context, even d=0.5 on welfare can represent a meaningful governance design choice.

## Evidence of effectiveness

Cohen's d is reported in every SWARM claim card. Notable values from the vault:

- **d=3.51** — [[claim-collusion-wealth-destruction]]: collusive agents accumulate 137x less wealth than honest agents under behavioral monitoring (run [[20260213-221500_collusion_tax_effect]], N=10 seeds). The largest effect size in the vault.
- **d=1.64** — [[claim-circuit-breakers-dominate]]: CB-only welfare vs full governance in the kernel market governance comparison (run [[20260211-000149_kernel_market_governance_comparison]], 70 runs, 10 seeds).
- **d=1.18** — [[claim-tax-welfare-tradeoff]]: transaction tax rate 0.025 vs 0.15 on welfare in the 700-run baseline governance v2 sweep (run [[20260213-202050_baseline_governance_v2]]).
- **d=1.41, d=1.33** — [[claim-governance-cost-paradox]]: welfare effects of transaction tax in the v1 baseline governance sweep (run [[20260213-173805_baseline_governance]]).

The [[cross-correlation]] analysis uses mean Cohen's d across runs to build the parameter-metric effect matrix, enabling comparison of effect magnitudes across different parameters and metrics.

---

Topics:
- [[_index]]

<!-- topics: effect-size, hypothesis-testing, practical-significance, statistical-methods -->
