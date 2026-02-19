---
description: Multi-condition study of acausality_depth (3 levels, 30 total runs)
type: experiment
status: completed
run_id: 20260212-231859_ldt_acausality_study
experiment_type: study
created: '2026-02-12'
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
| welfare_mean | 125.070 | 132.160 | 127.720 |
| welfare_std | 7.920 | 8.470 | 13.530 |
| toxicity_mean | 0.336 | 0.326 | 0.333 |
| acceptance_mean | 0.897 | 0.913 | 0.901 |

### Pairwise comparisons

| Comparison | Metric | Effect size | p-value | Bonferroni sig |
|------------|--------|-------------|---------|----------------|
| 1 vs 2 | welfare | d=-0.865 | p=0.069 | no |
| 1 vs 2 | toxicity_rate | d=0.849 | p=0.082 | no |
| 1 vs 2 | quality_gap | d=0.114 | p=0.802 | no |
| 1 vs 2 | honest_payoff | d=-0.703 | p=0.133 | no |
| 1 vs 2 | adversarial_payoff | d=-0.260 | p=0.568 | no |
| 1 vs 3 | welfare | d=-0.240 | p=0.600 | no |
| 1 vs 3 | toxicity_rate | d=0.639 | p=0.170 | no |
| 1 vs 3 | quality_gap | d=-0.019 | p=0.967 | no |
| 1 vs 3 | honest_payoff | d=-0.457 | p=0.321 | no |
| 1 vs 3 | adversarial_payoff | d=0.096 | p=0.833 | no |
| 2 vs 3 | welfare | d=0.393 | p=0.393 | no |
| 2 vs 3 | toxicity_rate | d=-0.532 | p=0.259 | no |
| 2 vs 3 | quality_gap | d=-0.146 | p=0.749 | no |
| 2 vs 3 | honest_payoff | d=0.145 | p=0.751 | no |
| 2 vs 3 | adversarial_payoff | d=0.306 | p=0.503 | no |

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260212-231859_ldt_acausality_study/analysis/summary.json`
- Sweep CSV: `runs/20260212-231859_ldt_acausality_study/sweep_results.csv`

## Reproduction

```bash
python -m swarm study unknown --seeds 10
```

---

Topics:
- [[_index]]

<!-- topics: ldt, acausality, study -->
