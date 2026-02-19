---
description: Multi-condition study of acausality_depth (3 levels, 30 total runs)
type: experiment
status: completed
run_id: 20260213-003819_ldt_short_horizon_study
experiment_type: study
created: '2026-02-13'
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
| welfare_mean | 125.867 | 134.402 | 130.432 |
| welfare_std | 10.138 | 12.358 | 11.714 |
| toxicity_mean | — | — | — |
| acceptance_mean | — | — | — |

### Pairwise comparisons

| Comparison | Metric | Effect size | p-value | Bonferroni sig |
|------------|--------|-------------|---------|----------------|
| 1 vs 2 | welfare | d=-0.755 | p=0.109 | no |
| 1 vs 2 | toxicity_rate | d=0.371 | p=0.417 | no |
| 1 vs 2 | quality_gap | d=0.315 | p=0.491 | no |
| 1 vs 2 | honest_payoff | d=-0.565 | p=0.222 | no |
| 1 vs 2 | adversarial_payoff | d=-0.883 | p=0.065 | no |
| 1 vs 3 | welfare | d=-0.417 | p=0.364 | no |
| 1 vs 3 | toxicity_rate | d=-0.254 | p=0.578 | no |
| 1 vs 3 | quality_gap | d=0.037 | p=0.935 | no |
| 1 vs 3 | honest_payoff | d=-0.265 | p=0.561 | no |
| 1 vs 3 | adversarial_payoff | d=-0.265 | p=0.561 | no |
| 2 vs 3 | welfare | d=0.330 | p=0.470 | no |
| 2 vs 3 | toxicity_rate | d=-0.634 | p=0.173 | no |
| 2 vs 3 | quality_gap | d=-0.347 | p=0.447 | no |
| 2 vs 3 | honest_payoff | d=0.331 | p=0.469 | no |
| 2 vs 3 | adversarial_payoff | d=0.597 | p=0.199 | no |

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260213-003819_ldt_short_horizon_study/analysis/summary.json`
- Sweep CSV: `runs/20260213-003819_ldt_short_horizon_study/sweep_results.csv`

## Reproduction

```bash
python -m swarm study unknown --seeds 10
```

---

Topics:
- [[_index]]

<!-- topics: ldt, study -->
