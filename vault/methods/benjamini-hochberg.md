---
description: Controls the false discovery rate (expected proportion of false positives among rejections) using a step-up procedure
type: method
status: active
category: statistical
aliases:
- BH correction
- FDR control
- Benjamini-Hochberg procedure
- BH
- benjamini-hochberg
cssclasses:
- method
graph-group: method
tags:
- multiple-comparisons
- false-discovery-rate
- hypothesis-testing
- statistical-methods
created: 2026-02-19
updated: 2026-02-19
---

# Benjamini-Hochberg procedure controls false discovery rate for exploratory multi-comparison analysis

## What it does

The Benjamini-Hochberg (BH) procedure controls the false discovery rate (FDR) — the expected proportion of rejected hypotheses that are actually false positives. Unlike [[bonferroni-correction]] and [[holm-bonferroni]], which control the probability of *any* false positive (FWER), BH tolerates a small fraction of false positives in exchange for substantially more statistical power.

**Inputs:** a set of m p-values and a desired FDR level q (typically q = 0.05).
**Outputs:** a significant/not-significant verdict for each test. Guarantees that among all rejected hypotheses, the expected fraction of false positives is at most q.

## Why it matters

SWARM's claim confidence criteria use BH correction as the threshold for **medium-confidence** claims: "Nominally significant OR single-sweep support with BH correction." This makes BH the gatekeeper between low and medium confidence. When a result survives BH but not Bonferroni, it warrants attention but requires replication before elevation to high confidence.

In practice, BH is especially valuable during exploratory analysis phases — when a new sweep produces many comparisons and the goal is to identify which parameter-metric pairs deserve further investigation. The collusion governance study (run [[20260213-221500_collusion_tax_effect]]) found that 10/12 hypotheses survived BH while only 6/12 survived Bonferroni, revealing four additional effects worth tracking.

## How to apply it

**Procedure (step-up):**

1. Order all m p-values from smallest to largest: p_(1) <= p_(2) <= ... <= p_(m).
2. Find the largest rank k such that p_(k) <= (k / m) * q.
3. Reject all hypotheses with rank 1 through k.

```
Step-up thresholds:

  p_(1)  compared to  (1/m) * q
  p_(2)  compared to  (2/m) * q
  ...
  p_(k)  compared to  (k/m) * q     <-- largest k where p_(k) passes
  ...
  p_(m)  compared to  q             (= q, uncorrected)
```

The SWARM analysis scripts implement BH alongside Bonferroni:

```python
# From runs/20260213-202050_baseline_governance_v2/analyze.py
# Sort by p-value for BH correction
sorted_results = sorted(results, key=lambda r: r['p_value'])

# Benjamini-Hochberg: find largest rank k where p_k <= (k/m)*q
q = 0.05
m = len(sorted_results)
bh_significant = []
for k, result in enumerate(sorted_results, 1):
    if result['p_value'] <= (k / m) * q:
        bh_significant.append(result)
```

## Assumptions and limitations

- **Assumes independence or positive dependence.** BH controls FDR exactly under independent tests and conservatively under positive regression dependency (PRDS). SWARM pairwise comparisons sharing a control group satisfy PRDS, so BH is valid. Under arbitrary dependence, use the more conservative Benjamini-Yekutieli procedure.
- **Tolerates false positives by design.** At q = 0.05, up to 5% of rejected hypotheses may be false positives. This is acceptable for exploratory screening but not for confirmatory claims — hence SWARM's requirement for Bonferroni significance plus replication for high-confidence claims.
- **Order-dependent rejection set.** The step-up logic means adding or removing tests can change which hypotheses are rejected, even for tests whose p-values did not change. This is a feature (adaptive thresholding) but can be confusing when incrementally adding comparisons.
- **Does not provide adjusted p-values in the strict sense.** BH q-values are sometimes reported as "adjusted p-values" but they represent the minimum FDR at which a hypothesis would be rejected, not a probability statement about that individual test.

## Evidence of effectiveness

BH correction is implemented in all SWARM analysis scripts and defines the medium-confidence boundary for claims:

- [[20260213-221500_collusion_tax_effect]] — the collusion governance study tested 12 hypotheses. 6/12 survived Bonferroni; 10/12 survived BH at FDR = 0.05. The four BH-only results identified interaction effects between collusion penalty multiplier and transaction tax rate on toxicity, guiding subsequent investigation.
- [[20260213-202050_baseline_governance_v2]] — the 700-run baseline governance v2 sweep uses BH as a secondary filter. The analyze.py script reports both Bonferroni-significant and BH-significant results, allowing researchers to distinguish confirmatory from exploratory findings.
- [[20260213-173805_baseline_governance]] — the v1 baseline governance sweep implements BH in its analysis pipeline, with results informing the confidence level assigned to downstream claims like [[claim-tax-welfare-tradeoff]].
- [[20260213-123944_moltbook_captcha_study]] — reported 0/112 BH-significant results, correctly identifying the captcha mechanism as having no detectable effect and preventing false claims.

---

Topics:
- [[_index]]

<!-- topics: multiple-comparisons, false-discovery-rate, hypothesis-testing, statistical-methods -->
