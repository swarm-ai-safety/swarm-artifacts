---
description: Single baseline run of rlm_governance_lag_seed42, final welfare=58.6
type: experiment
status: completed
run_id: 20260210-235816_rlm_governance_lag_seed42
experiment_type: single
created: '2026-02-10'
---

# single-run baseline with welfare=58.6 (rlm governance lag seed42)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 42
- **Epochs**: 50
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 58.627
- **Toxicity rate**: 0.336
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

- [[claim-smarter-agents-earn-less]] (high) — governance, rlm

## Artifacts

- CSV: `runs/20260210-235816_rlm_governance_lag_seed42/csv/rlm_governance_lag_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: governance, rlm, seed-42 -->
