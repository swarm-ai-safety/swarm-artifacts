---
description: "Parameter interaction matrix across 11 sweep/study runs detecting co-occurring significance and consistency"
type: method
status: active
aliases:
  - cross-correlation
  - parameter-interactions
cssclasses:
  - method
graph-group: method
tags:
  - cross-correlation
  - parameter-interactions
  - meta-analysis
created: 2026-02-19
updated: 2026-02-19
---

# Cross-correlation analysis reveals tax-penalty interaction on toxicity and high-variance tax effects on welfare

Analyzed **5** parameters across **11** sweep/study runs.

## Parameter frequency

| Parameter | Runs | Run IDs |
|-----------|------|---------|
| `acausality_depth` | 5 | 20260212-231859_ldt_acausality_study, 20260213-003757_ldt_large_population_st... |
| `governance.transaction_tax_rate` | 4 | 20260213-173805_baseline_governance, 20260213-202050_baseline_governance_v2, ... |
| `governance.circuit_breaker_enabled` | 3 | 20260213-173805_baseline_governance, 20260213-202050_baseline_governance_v2, ... |
| `decision_theory` | 2 | 20260213-013951_ldt_decision_theory_study, 20260213-101646_ldt_large_pop_dt_s... |
| `governance.collusion_penalty_multiplier` | 1 | 20260213-221500_collusion_tax_effect |

## Parameter-metric effect matrix

Mean Cohen's d across runs (significant results only shown with *).

| Parameter | `adversarial_payoff` | `deceptive_payoff` | `honest_payoff` | `opportunistic_payoff` | `quality_gap` | `rlm_payoff` | `toxicity_rate` | `welfare` |
|-----------|----------------------|--------------------|-----------------|------------------------|---------------|--------------|-----------------|-----------|
| `acausality_depth` | -0.030 | -- | -0.359 | -- | -0.107 | -- | -0.005 | -0.318 |
| `decision_theory` | +0.066 | -- | -0.627 | -- | -0.184 | -- | +0.232 | -0.524 |
| `governance.circuit_breaker_enabled` | -- | +0.117 | -0.125 | +0.109 | +0.187 | -- | -0.081 | -0.171 |
| `governance.collusion_penalty_multiplier` | -- | -- | +0.084 | -- | +0.112 | +0.230 | -0.745 | +0.167 |
| `governance.transaction_tax_rate` | -- | +0.166 | +0.670 | +0.230 | -0.027 | +4.180 | -0.186 | +0.958 |

## Interaction candidates

Parameter pairs with co-occurring Bonferroni-significant effects on the same metric:

| Param A | Param B | Metric | Co-occurring runs |
|---------|---------|--------|-------------------|
| `governance.collusion_penalty_multiplier` | `governance.transaction_tax_rate` | `toxicity_rate` | 20260213-221500_collusion_tax_effect |

These pairs may exhibit interaction effects and warrant factorial analysis or dedicated interaction sweeps.

## Cross-run consistency

Parameters with inconsistent or high-variance effects across runs (potential moderator effects):

| Parameter | Metric | Status | Runs | Directions | Mean d | Spread |
|-----------|--------|--------|------|------------|--------|--------|
| `governance.transaction_tax_rate` | `welfare` | HIGH_VARIANCE | 3 | positive | +1.5552 | 4.2664 |
| `governance.transaction_tax_rate` | `honest_payoff` | HIGH_VARIANCE | 3 | positive | +1.2438 | 2.4049 |

---

<!-- topics: cross-correlation, parameter-interactions, meta-analysis -->
