---
description: 'baseline_governance: 80-run sweep of transaction_tax_rate, circuit_breaker_enabled, 4 Bonferroni-significant
  findings'
type: experiment
status: completed
run_id: 20260213-173805_baseline_governance
experiment_type: sweep
created: '2026-02-13'
aliases:
- 20260213-173805_baseline_governance
cssclasses:
- experiment
- experiment-sweep
tags:
- baseline
- governance
graph-group: experiment
---

# baseline governance sweep (80 runs) finds 4 Bonferroni-significant effects across transaction_tax_rate, circuit_breaker_enabled

## Design

- **Hypothesis**: Not recorded
- **Type**: Parameter sweep
- **Parameters swept**:
- `governance.transaction_tax_rate`: [0.0, 0.05, 0.1, 0.15]
- `governance.circuit_breaker_enabled`: [False, True]
- **Seeds**: 1 seeds
- **Total runs**: 80
- **SWARM version**: unknown @ `unknown`

## Key results

- **transaction_tax_rate** (0.0 vs 0.15) on welfare: mean 62.54 vs 53.18, d=1.41 (large), p<0.001, Bonferroni-corrected
- **transaction_tax_rate** (0.0 vs 0.1) on welfare: mean 62.54 vs 52.32, d=1.33 (large), p<0.001, Bonferroni-corrected
- **transaction_tax_rate** (0.0 vs 0.1) on honest_payoff: mean 16.14 vs 12.94, d=1.29 (large), p<0.001, Bonferroni-corrected
- **transaction_tax_rate** (0.05 vs 0.15) on welfare: mean 60.80 vs 53.18, d=1.13 (large), p=0.0010, Bonferroni-corrected

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260213-173805_baseline_governance/summary.json`
- Sweep CSV: `runs/20260213-173805_baseline_governance/sweep_results.csv`
- Script: `runs/20260213-173805_baseline_governance/analyze.py`
- Script: `runs/20260213-173805_baseline_governance/generate_plots.py`
- Script: `runs/20260213-173805_baseline_governance/run_sweep.py`

## Reproduction

```bash
python -m swarm sweep unknown --seeds 1
```

---

Topics:
- [[_index]]

<!-- topics: baseline, governance -->
