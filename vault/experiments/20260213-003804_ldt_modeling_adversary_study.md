---
description: Multi-condition study of acausality_depth (3 levels, 30 total runs)
type: experiment
status: completed
run_id: 20260213-003804_ldt_modeling_adversary_study
experiment_type: study
created: '2026-02-13'
aliases:
- 20260213-003804_ldt_modeling_adversary_study
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
| welfare_mean | 107.622 | 107.439 | 108.186 |
| welfare_std | 9.702 | 9.944 | 11.224 |
| toxicity_mean | — | — | — |
| acceptance_mean | — | — | — |

### Pairwise comparisons

| Comparison | Metric | Effect size | p-value | Bonferroni sig |
|------------|--------|-------------|---------|----------------|
| 1 vs 2 | welfare | d=0.019 | p=0.967 | no |
| 1 vs 2 | toxicity_rate | d=-0.881 | p=0.064 | no |
| 1 vs 2 | quality_gap | d=0.000 | p=nan | no |
| 1 vs 2 | honest_payoff | d=0.018 | p=0.968 | no |
| 1 vs 2 | adversarial_payoff | d=0.038 | p=0.932 | no |
| 1 vs 3 | welfare | d=-0.054 | p=0.906 | no |
| 1 vs 3 | toxicity_rate | d=-0.899 | p=0.061 | no |
| 1 vs 3 | quality_gap | d=0.000 | p=nan | no |
| 1 vs 3 | honest_payoff | d=-0.052 | p=0.909 | no |
| 1 vs 3 | adversarial_payoff | d=-0.255 | p=0.577 | no |
| 2 vs 3 | welfare | d=-0.070 | p=0.877 | no |
| 2 vs 3 | toxicity_rate | d=-0.154 | p=0.734 | no |
| 2 vs 3 | quality_gap | d=0.000 | p=nan | no |
| 2 vs 3 | honest_payoff | d=-0.068 | p=0.880 | no |
| 2 vs 3 | adversarial_payoff | d=-0.270 | p=0.554 | no |

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260213-003804_ldt_modeling_adversary_study/analysis/summary.json`
- Sweep CSV: `runs/20260213-003804_ldt_modeling_adversary_study/sweep_results.csv`

## Reproduction

```bash
python -m swarm study unknown --seeds 10
```

---

Topics:
- [[_index]]

<!-- topics: ldt, study -->
