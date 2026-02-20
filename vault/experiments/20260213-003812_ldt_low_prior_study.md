---
description: Multi-condition study of acausality_depth (3 levels, 30 total runs)
type: experiment
status: completed
run_id: 20260213-003812_ldt_low_prior_study
experiment_type: study
created: '2026-02-13'
aliases:
- 20260213-003812_ldt_low_prior_study
cssclasses:
- experiment
- experiment-study
tags:
- ldt
- study
graph-group: experiment
---

# acausality depth study (30 runs) finds 0 significant pairwise differences

## Design

- **Type**: Multi-condition study
- **Parameter**: `acausality_depth`
- **Levels**: [1, 2, 3]
- **Seeds per config**: 10
- **Total runs**: 30
- **SWARM version**: unknown @ `unknown`

## Key results

### Descriptive statistics

| Metric | 1 | 2 | 3 |
|--------|-----|-----|-----|
| welfare_mean | 125.218 | 132.160 | 127.723 |
| welfare_std | 7.931 | 8.467 | 13.528 |
| toxicity_mean | — | — | — |
| acceptance_mean | — | — | — |

### Pairwise comparisons

| Comparison | Metric | Effect size | p-value | Bonferroni sig |
|------------|--------|-------------|---------|----------------|
| 1 vs 2 | welfare | d=-0.846 | p=0.075 | no |
| 1 vs 2 | toxicity_rate | d=0.858 | p=0.080 | no |
| 1 vs 2 | quality_gap | d=0.051 | p=0.911 | no |
| 1 vs 2 | honest_payoff | d=-0.701 | p=0.134 | no |
| 1 vs 2 | adversarial_payoff | d=-0.236 | p=0.605 | no |
| 1 vs 3 | welfare | d=-0.226 | p=0.621 | no |
| 1 vs 3 | toxicity_rate | d=0.658 | p=0.158 | no |
| 1 vs 3 | quality_gap | d=-0.094 | p=0.837 | no |
| 1 vs 3 | honest_payoff | d=-0.456 | p=0.322 | no |
| 1 vs 3 | adversarial_payoff | d=0.122 | p=0.788 | no |
| 2 vs 3 | welfare | d=0.393 | p=0.393 | no |
| 2 vs 3 | toxicity_rate | d=-0.532 | p=0.259 | no |
| 2 vs 3 | quality_gap | d=-0.146 | p=0.749 | no |
| 2 vs 3 | honest_payoff | d=0.145 | p=0.751 | no |
| 2 vs 3 | adversarial_payoff | d=0.306 | p=0.503 | no |

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260213-003812_ldt_low_prior_study/analysis/summary.json`
- Sweep CSV: `runs/20260213-003812_ldt_low_prior_study/sweep_results.csv`

## Reproduction

```bash
python -m swarm study unknown --seeds 10
```

---

Topics:
- [[_index]]

<!-- topics: ldt, study -->
