---
description: 'collusion_tax_effect: 160-run sweep of transaction_tax_rate, collusion_penalty_multiplier,
  21 Bonferroni-significant findings'
type: experiment
status: completed
run_id: 20260213-221500_collusion_tax_effect
experiment_type: sweep
created: '2026-02-13'
---

# collusion tax effect sweep (160 runs) finds 21 Bonferroni-significant effects across transaction_tax_rate, collusion_penalty_multiplier

## Design

- **Hypothesis**: Not recorded
- **Type**: Parameter sweep
- **Parameters swept**:
- `governance.transaction_tax_rate`: [0.0, 0.02, 0.05, 0.1]
- `governance.collusion_penalty_multiplier`: [0.5, 1.0, 1.5, 2.0]
- **Seeds**: 1 seeds
- **Total runs**: 160
- **SWARM version**: unknown @ `unknown`

## Key results

- **transaction_tax_rate** (0.0 vs 0.1) on rlm_payoff: mean 220.85 vs 194.45, d=6.02 (large), p<1e-14, Bonferroni-corrected
- **transaction_tax_rate** (0.0 vs 0.05) on rlm_payoff: mean 220.85 vs 208.75, d=4.98 (large), p<1e-14, Bonferroni-corrected
- **transaction_tax_rate** (0.02 vs 0.1) on rlm_payoff: mean 215.77 vs 194.45, d=4.96 (large), p<1e-14, Bonferroni-corrected
- **transaction_tax_rate** (0.0 vs 0.1) on welfare: mean 3791.52 vs 3385.95, d=4.80 (large), p<1e-14, Bonferroni-corrected
- **transaction_tax_rate** (0.02 vs 0.1) on welfare: mean 3738.88 vs 3385.95, d=4.22 (large), p<1e-14, Bonferroni-corrected

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Summary: `runs/20260213-221500_collusion_tax_effect/summary.json`
- Sweep CSV: `runs/20260213-221500_collusion_tax_effect/sweep_results.csv`
- Script: `runs/20260213-221500_collusion_tax_effect/analyze.py`
- Script: `runs/20260213-221500_collusion_tax_effect/generate_plots.py`
- Script: `runs/20260213-221500_collusion_tax_effect/run_sweep.py`

## Reproduction

```bash
python -m swarm sweep unknown --seeds 1
```

---

Topics:
- [[_index]]

<!-- topics: collusion -->
