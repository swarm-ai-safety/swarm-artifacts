---
description: Runs exploring collusion penalty sensitivity and tax interaction
type: sweep-summary
status: active
parameter: governance.collusion_penalty_multiplier
created: 2026-02-13
updated: 2026-02-21
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
| 20260213-123944_moltbook_captcha_study | Feb 13 | 10 | 3 (0, 1.0, 2.0) | — | 0/112 sig, penalty null |

## Convergence

Two sweeps (160 + 200 runs). Key findings:
- Penalty multiplier 0.5-1.5x: minimal effect on welfare or toxicity
- Penalty multiplier 2.0x: toxicity increases (d=-1.12, p<0.0001), welfare decreases
- Tax rate dominates penalty multiplier in variance explained
- Moltbook CAPTCHA study (200 runs): penalty 0-2.0x shows zero effect on all 7 metrics; 0/112 Bonferroni-significant ([[claim-captcha-difficulty-and-collusion-penalty-have-no-governance-effect]])

## Phase transition surface

Destabilization threshold at penalty multiplier ~1.5x. Below this, penalties are absorbed; above, system destabilizes.
Tax-penalty interaction is weak (no significant interaction term in marginal analysis), though [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]] notes possible super-additive toxicity at extreme combinations. [[claim-collusion-penalty-has-no-economic-effect]] confirms zero economic effect across all tested levels. [[claim-tax-and-penalty-effects-are-orthogonal]] formalizes the clean partition.

<!-- topics: governance, collusion, penalty, sweep-series -->
