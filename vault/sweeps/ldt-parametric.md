---
description: "Parametric studies of LDT scenario variants across multiple dimensions"
type: sweep-summary
status: active
parameter: "multiple LDT parameters"
created: 2026-02-12
updated: 2026-02-19
---

## Runs in this sweep

| Run ID | Date | Parameter | Levels | Seeds | Key finding |
|--------|------|-----------|--------|-------|-------------|
| 20260212-231859_ldt_acausality_study | Feb 12 | acausality_depth | 3 | 10 | 0 sig |
| 20260213-003757_ldt_large_population_study | Feb 13 | population_size | 3 | 10 | 0 sig |
| 20260213-003804_ldt_modeling_adversary_study | Feb 13 | adversary_modeling | 3 | 10 | 0 sig |
| 20260213-003812_ldt_low_prior_study | Feb 13 | prior_strength | 3 | 10 | 0 sig |
| 20260213-003819_ldt_short_horizon_study | Feb 13 | horizon_length | 3 | 10 | 0 sig |
| 20260213-013951_ldt_decision_theory_study | Feb 13 | dt_variant | 3 | 10 | 0 sig |
| 20260213-101646_ldt_large_pop_dt_study | Feb 13 | pop+dt combo | 3 | 10 | 0 sig |

Total: ~210 runs across 7 studies.

## Convergence

Remarkably robust: ZERO Bonferroni-significant pairwise differences across ANY parameter dimension.

LDT scenario outcomes appear insensitive to:
- Acausality reasoning depth (1-3)
- Population size
- Adversary modeling sophistication
- Prior strength
- Time horizon length
- Decision theory variant
- Population × decision theory interaction

## Implications

The LDT framework may have a dominant equilibrium that absorbs parameter variation. This is either:
1. A genuine robustness property (desirable)
2. An indication that the proxy computer doesn't create enough differentiation between LDT variants (needs investigation)

Further study needed to determine if this robustness holds with more extreme parameter ranges.

<!-- topics: ldt, decision-theory, parametric, robustness, sweep-series -->
