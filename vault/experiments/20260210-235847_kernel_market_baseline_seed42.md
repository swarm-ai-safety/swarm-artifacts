---
description: Single baseline run of kernel_market_baseline_seed42, final welfare=2.2
type: experiment
status: completed
run_id: 20260210-235847_kernel_market_baseline_seed42
experiment_type: single
created: '2026-02-10'
---

# single-run baseline with welfare=2.2 (kernel market baseline seed42)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 42
- **Epochs**: 20
- **Steps per epoch**: 10
- **Agents**: 8
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 2.215
- **Toxicity rate**: 0.464
- **Acceptance rate**: 0.889
- **Quality gap**: 0.143

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-235847_kernel_market_baseline_seed42/csv/kernel_market_baseline_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: baseline, kernel, market, seed-42 -->
