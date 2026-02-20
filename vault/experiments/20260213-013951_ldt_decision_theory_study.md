---
description: Multi-condition study of decision_theory (3 levels, 30 total runs)
type: experiment
status: completed
run_id: 20260213-013951_ldt_decision_theory_study
experiment_type: study
created: '2026-02-13'
aliases:
- 20260213-013951_ldt_decision_theory_study
cssclasses:
- experiment
- experiment-study
tags:
- ldt
- study
graph-group: experiment
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
| welfare_mean | 125.067 | 132.160 | 127.723 |
| welfare_std | 7.923 | 8.467 | 13.528 |
| toxicity_mean | — | — | — |
| acceptance_mean | — | — | — |

### Pairwise comparisons

| Comparison | Metric | Effect size | p-value | Bonferroni sig |
|------------|--------|-------------|---------|----------------|
| tdt vs fdt | welfare | d=-0.865 | p=0.069 | no |
| tdt vs fdt | toxicity_rate | d=0.849 | p=0.082 | no |
| tdt vs fdt | quality_gap | d=0.114 | p=0.802 | no |
| tdt vs fdt | honest_payoff | d=-0.703 | p=0.133 | no |
| tdt vs fdt | adversarial_payoff | d=-0.260 | p=0.568 | no |
| tdt vs udt | welfare | d=-0.240 | p=0.600 | no |
| tdt vs udt | toxicity_rate | d=0.639 | p=0.170 | no |
| tdt vs udt | quality_gap | d=-0.019 | p=0.967 | no |
| tdt vs udt | honest_payoff | d=-0.457 | p=0.321 | no |
| tdt vs udt | adversarial_payoff | d=0.096 | p=0.833 | no |
| fdt vs udt | welfare | d=0.393 | p=0.393 | no |
| fdt vs udt | toxicity_rate | d=-0.532 | p=0.259 | no |
| fdt vs udt | quality_gap | d=-0.146 | p=0.749 | no |
| fdt vs udt | honest_payoff | d=0.145 | p=0.751 | no |
| fdt vs udt | adversarial_payoff | d=0.306 | p=0.503 | no |

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260213-013951_ldt_decision_theory_study/analysis/summary.json`
- Sweep CSV: `runs/20260213-013951_ldt_decision_theory_study/sweep_results.csv`

## Reproduction

```bash
python -m swarm study unknown --seeds 10
```

---

Topics:
- [[_index]]

<!-- topics: ldt, study -->
