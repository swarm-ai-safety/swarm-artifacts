---
description: Multi-condition study of memori_study (0 levels, 30 total runs)
type: experiment
status: completed
run_id: 20260217_memori_study
experiment_type: study
created: '2026-02-17'
aliases:
- 20260217_memori_study
cssclasses:
- experiment
- experiment-study
tags:
- memori
- study
graph-group: experiment
---

# memori study study (30 runs) finds 0 significant pairwise differences

## Design

- **Type**: Multi-condition study
- **Parameter**: `unknown`
- **Levels**: []
- **Seeds per config**: 5
- **Total runs**: 30
- **SWARM version**: unknown @ `unknown`

## Key results

### Descriptive statistics

| Metric | 0.0|False | 0.0|True | 0.05|False | 0.05|True | 0.1|False | 0.1|True |
|--------|-----|-----|-----|-----|-----|-----|
| welfare_mean | 9.854 | 11.583 | 11.098 | 12.074 | 10.559 | 12.463 |
| welfare_std | 5.173 | 3.500 | 3.622 | 5.052 | 2.861 | 2.344 |
| toxicity_mean | 0.242 | 0.265 | 0.264 | 0.269 | 0.263 | 0.270 |
| toxicity_std | 0.064 | 0.031 | 0.011 | 0.014 | 0.024 | 0.009 |
| acceptance_mean | — | — | — | — | — | — |

### Pairwise comparisons

| Comparison | Metric | Effect size | p-value | Bonferroni sig |
|------------|--------|-------------|---------|----------------|
| 0.0 vs 0.05 | welfare | d=-0.206 | p=0.651 | no |
| 0.0 vs 0.1 | welfare | d=-0.223 | p=0.625 | no |
| 0.05 vs 0.1 | welfare | d=0.022 | p=0.962 | no |
| 0.0 vs 0.05 | toxicity_rate | d=-0.363 | p=0.436 | no |
| 0.0 vs 0.1 | toxicity_rate | d=-0.344 | p=0.458 | no |
| 0.05 vs 0.1 | toxicity_rate | d=0.019 | p=0.966 | no |
| 0.0 vs 0.05 | quality_gap | d=0.140 | p=0.760 | no |
| 0.0 vs 0.1 | quality_gap | d=0.341 | p=0.461 | no |
| 0.05 vs 0.1 | quality_gap | d=0.433 | p=0.347 | no |
| False vs True | welfare | d=-0.422 | p=0.258 | no |
| False vs True | toxicity_rate | d=-0.376 | p=0.316 | no |
| False vs True | quality_gap | d=0.548 | p=0.145 | no |

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260217_memori_study/summary.json`
- Sweep CSV: `runs/20260217_memori_study/sweep_results.csv`

## Reproduction

```bash
python -m swarm study unknown --seeds 5
```

---

Topics:
- [[_index]]

<!-- topics: memori, study -->
