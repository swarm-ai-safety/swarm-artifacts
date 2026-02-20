---
description: 'baseline_governance_v2: 700-run sweep of transaction_tax_rate, circuit_breaker_enabled, 18 Bonferroni-significant
  findings'
type: experiment
status: completed
run_id: 20260213-202050_baseline_governance_v2
experiment_type: sweep
created: '2026-02-13'
aliases:
- 20260213-202050_baseline_governance_v2
cssclasses:
- experiment
- experiment-sweep
tags:
- baseline
- governance
graph-group: experiment
---

# baseline governance v2 sweep (700 runs) finds 18 Bonferroni-significant effects across transaction_tax_rate, circuit_breaker_enabled

## Design

- **Hypothesis**: Not recorded
- **Type**: Parameter sweep
- **Parameters swept**:
- `governance.transaction_tax_rate`: [0.0, 0.025, 0.05, 0.075, 0.1, 0.125, 0.15]
- `governance.circuit_breaker_enabled`: [False, True]
- **Seeds**: 1 seeds
- **Total runs**: 700
- **SWARM version**: unknown @ `unknown`

## Key results

- **transaction_tax_rate** (0.025 vs 0.15) on welfare: mean 59.07 vs 50.96, d=1.18 (large), p<0.001, Bonferroni-corrected
- **transaction_tax_rate** (0.025 vs 0.125) on welfare: mean 59.07 vs 51.15, d=1.14 (large), p<0.001, Bonferroni-corrected
- **transaction_tax_rate** (0.0 vs 0.15) on welfare: mean 59.01 vs 50.96, d=1.00 (large), p<0.001, Bonferroni-corrected
- **transaction_tax_rate** (0.0 vs 0.125) on welfare: mean 59.01 vs 51.15, d=0.97 (large), p<0.001, Bonferroni-corrected
- **transaction_tax_rate** (0.025 vs 0.15) on honest_payoff: mean 14.81 vs 12.79, d=0.80 (large), p<0.001, Bonferroni-corrected

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260213-202050_baseline_governance_v2/summary.json`
- Sweep CSV: `runs/20260213-202050_baseline_governance_v2/sweep_results.csv`
- Script: `runs/20260213-202050_baseline_governance_v2/analyze.py`
- Script: `runs/20260213-202050_baseline_governance_v2/generate_plots.py`
- Script: `runs/20260213-202050_baseline_governance_v2/run_sweep.py`

## Reproduction

```bash
python -m swarm sweep unknown --seeds 1
```

---

Topics:
- [[_index]]

<!-- topics: baseline, governance -->
