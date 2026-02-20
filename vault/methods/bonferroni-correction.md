---
description: Divides significance threshold alpha by the number of tests to control family-wise error rate across pairwise
  comparisons
type: method
status: active
category: statistical
aliases:
- Bonferroni
- FWER correction
- Bonferroni adjustment
- bonferroni-correction
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

# Bonferroni correction controls family-wise error rate by dividing alpha by the number of comparisons

## What it does

The Bonferroni correction adjusts the significance threshold when performing multiple statistical tests simultaneously. Given a desired family-wise error rate (FWER) of alpha and m independent tests, each individual test is evaluated at alpha/m. A result is declared significant only if its p-value falls below this adjusted threshold.

**Inputs:** a set of m p-values and a desired FWER (typically alpha = 0.05).
**Outputs:** a binary significant/not-significant verdict for each test, guaranteeing that the probability of even one false positive across all m tests is at most alpha.

## Why it matters

SWARM experiments routinely compare multiple governance regimes, parameter levels, and outcome metrics in a single sweep. A 700-run sweep like [[20260213-202050_baseline_governance_v2]] with 7 tax rate levels and 2 circuit breaker states produces dozens of pairwise comparisons. Without correction, roughly 5% of null comparisons would appear significant by chance. The Bonferroni correction is the simplest and most conservative guard against this inflation.

SWARM's claim confidence criteria require Bonferroni significance for **high-confidence** claims: a result must survive Bonferroni correction AND replicate across two or more independent runs or seeds.

## How to apply it

1. Count the total number of pairwise comparisons m in the sweep.
2. Set the adjusted threshold: alpha_adj = alpha / m.
3. For each comparison, compute the two-sample t-test (or equivalent) p-value.
4. Reject the null hypothesis only if p < alpha_adj.

**Formula:**

```
alpha_adjusted = alpha / m

where:
  alpha = desired family-wise error rate (e.g., 0.05)
  m     = number of simultaneous tests
```

The SWARM analysis scripts implement this automatically:

```bash
python runs/20260213-202050_baseline_governance_v2/analyze.py
# Reports: "Bonferroni threshold: 0.05 / m = ..."
```

## Assumptions and limitations

- **Conservative.** Bonferroni assumes tests are independent. When comparisons share a control group (as in SWARM pairwise sweeps), the correction is overly strict — it will miss real effects. For dependent tests, consider [[holm-bonferroni]] or [[benjamini-hochberg]].
- **Scales poorly.** With m > 50 comparisons, the adjusted threshold becomes vanishingly small. The [[20260213-202050_baseline_governance_v2]] sweep had hundreds of potential pairwise comparisons; only 18 survived Bonferroni.
- **All-or-nothing.** It controls the probability of *any* false positive, not the *proportion* of false positives. When screening many hypotheses (e.g., during exploratory analysis), [[benjamini-hochberg]] FDR control is often more appropriate.
- **Does not replace effect size reporting.** A Bonferroni-significant p-value says nothing about practical magnitude. Always pair with [[cohens-d]].

## Evidence of effectiveness

Bonferroni correction is the default significance filter across all SWARM sweep analyses and is required for high-confidence claims.

- [[20260211-000149_kernel_market_governance_comparison]] — the foundational governance comparison (70 runs, 7 regimes, 10 seeds) reported d=1.64 for CB-only vs full governance, surviving Bonferroni correction. This result anchors [[claim-circuit-breakers-dominate]].
- [[20260213-202050_baseline_governance_v2]] — the 700-run sweep found 18 Bonferroni-significant effects across transaction_tax_rate and circuit_breaker_enabled parameters. The largest effect (tax 0.025 vs 0.15 on welfare) had d=1.18, p<0.001.
- [[20260213-221500_collusion_tax_effect]] — collusion wealth destruction (d=3.51, p<0.001) survived Bonferroni across 10 seeds, supporting [[claim-collusion-wealth-destruction]].
- [[claim-tax-welfare-tradeoff]] — rated high confidence because d=1.18 survives Bonferroni in the v2 sweep and d=0.95 survives in the independent v1 sweep.

---

Topics:
- [[_index]]

<!-- topics: multiple-comparisons, family-wise-error-rate, hypothesis-testing, statistical-methods -->
