---
description: Single baseline run of strict_governance_seed42, final welfare=4.6
type: experiment
status: completed
run_id: 20260210-002820_strict_governance_seed42
experiment_type: single
created: '2026-02-10'
---

# single-run baseline with welfare=4.6 (strict governance seed42)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 42
- **Epochs**: 10
- **Steps per epoch**: 10
- **Agents**: 7
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 4.567
- **Toxicity rate**: 0.375
- **Acceptance rate**: 0.833
- **Quality gap**: 0.247

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-002820_strict_governance_seed42/csv/strict_governance_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: governance, seed-42 -->
