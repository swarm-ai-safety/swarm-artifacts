---
description: Single baseline run of 202707_self_optimizer_hodoscope, final welfare=21.0
type: experiment
status: completed
run_id: 20260224_202707_self_optimizer_hodoscope
experiment_type: single
created: '2026-02-24'
---

# single-run baseline with welfare=21.0 (202707 self optimizer hodoscope)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 42
- **Epochs**: 20
- **Steps per epoch**: 10
- **Agents**: 8
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 21.016
- **Toxicity rate**: 0.354
- **Acceptance rate**: 0.967
- **Quality gap**: 0.095

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Plot: `runs/20260224_202707_self_optimizer_hodoscope/plots/action_type.png`
- Plot: `runs/20260224_202707_self_optimizer_hodoscope/plots/agent_type.png`
- Plot: `runs/20260224_202707_self_optimizer_hodoscope/plots/combined_4panel.png`
- Plot: `runs/20260224_202707_self_optimizer_hodoscope/plots/epoch_evolution.png`
- Plot: `runs/20260224_202707_self_optimizer_hodoscope/plots/quality.png`

## Reproduction

```bash
python -m swarm run unknown --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: untagged -->
