---
description: Single baseline run of strict_governance_seed42, final welfare=2.3
type: experiment
status: completed
run_id: 20260210-005952_strict_governance_seed42
experiment_type: single
created: '2026-02-10'
aliases:
- 20260210-005952_strict_governance_seed42
cssclasses:
- experiment
- experiment-single
tags:
- governance
- seed-42
graph-group: experiment
---

# single-run baseline with welfare=2.3 (strict governance seed42)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 42
- **Epochs**: 15
- **Steps per epoch**: 12
- **Agents**: 7
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 2.255
- **Toxicity rate**: 0.239
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-005952_strict_governance_seed42/csv/strict_governance_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: governance, seed-42 -->
