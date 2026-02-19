---
description: Multi-condition study of decision_theory (3 levels, 30 total runs)
type: experiment
status: completed
run_id: 20260213-101646_ldt_large_pop_dt_study
experiment_type: study
created: '2026-02-13'
---

# decision theory study (30 runs) finds 0 significant pairwise differences

## Design

- **Type**: Multi-condition study
- **Parameter**: `decision_theory`
- **Levels**: ['tdt', 'fdt', 'udt']
- **Seeds per config**: 10
- **Total runs**: 30
- **SWARM version**: unknown @ `unknown`

## Key results

### Descriptive statistics

| Metric | tdt | fdt | udt |
|--------|-----|-----|-----|
| welfare_mean | 366.381 | 371.409 | 387.678 |
| welfare_std | 19.687 | 16.329 | 16.609 |
| toxicity_mean | — | — | — |
| acceptance_mean | — | — | — |

### Pairwise comparisons

| Comparison | Metric | Effect size | p-value | Bonferroni sig |
|------------|--------|-------------|---------|----------------|
| tdt vs fdt | welfare | d=-0.278 | p=0.542 | no |
| tdt vs fdt | toxicity_rate | d=-0.117 | p=0.797 | no |
| tdt vs fdt | quality_gap | d=-0.159 | p=0.727 | no |
| tdt vs fdt | honest_payoff | d=-0.595 | p=0.204 | no |
| tdt vs fdt | adversarial_payoff | d=0.280 | p=0.543 | no |
| tdt vs udt | welfare | d=-1.169 | p=0.018 | no |
| tdt vs udt | toxicity_rate | d=0.202 | p=0.657 | no |
| tdt vs udt | quality_gap | d=-0.582 | p=0.209 | no |
| tdt vs udt | honest_payoff | d=-1.253 | p=0.013 | no |
| tdt vs udt | adversarial_payoff | d=0.163 | p=0.722 | no |
| fdt vs udt | welfare | d=-0.988 | p=0.040 | no |
| fdt vs udt | toxicity_rate | d=0.350 | p=0.444 | no |
| fdt vs udt | quality_gap | d=-0.311 | p=0.497 | no |
| fdt vs udt | honest_payoff | d=-0.901 | p=0.060 | no |
| fdt vs udt | adversarial_payoff | d=-0.190 | p=0.677 | no |

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260213-101646_ldt_large_pop_dt_study/analysis/summary.json`
- Sweep CSV: `runs/20260213-101646_ldt_large_pop_dt_study/sweep_results.csv`

## Reproduction

```bash
python -m swarm study unknown --seeds 10
```

---

Topics:
- [[_index]]

<!-- topics: ldt, study -->
