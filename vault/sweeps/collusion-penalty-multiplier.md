---
description: Runs exploring collusion penalty sensitivity and tax interaction
type: sweep-summary
status: active
parameter: governance.collusion_penalty_multiplier
created: 2026-02-13
updated: 2026-02-19
aliases:
- governance.collusion_penalty_multiplier
- collusion-penalty-multiplier
cssclasses:
- sweep-summary
tags:
- governance
- collusion
- penalty
- sweep-series
graph-group: sweep
---

## Runs in this sweep

| Run ID | Date | Seeds | Penalty levels | Tax levels | Key finding |
|--------|------|-------|---------------|------------|-------------|
| 20260213-221500_collusion_tax_effect | Feb 13 | 10 | 4 (0.5-2.0) | 4 | 21 Bonferroni-sig |

## Convergence

Single sweep with 160 runs (10 seeds per combination). Key findings:
- Penalty multiplier 0.5-1.5x: minimal effect on welfare or toxicity
- Penalty multiplier 2.0x: toxicity increases (d=-1.12, p<0.0001), welfare decreases
- Tax rate dominates penalty multiplier in variance explained

## Phase transition surface

Destabilization threshold at penalty multiplier ~1.5x. Below this, penalties are absorbed; above, system destabilizes.
Tax-penalty interaction is weak (no significant interaction term).

<!-- topics: governance, collusion, penalty, sweep-series -->
