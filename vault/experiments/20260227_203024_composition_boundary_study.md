---
description: "Systematic sweep of adversarial fraction x governance x population size characterizes cooperative regime boundaries and governance cost-benefit"
type: experiment
status: completed
run_id: 20260227_203024_composition_boundary_study
experiment_type: study
created: '2026-02-27'
updated: '2026-02-28'
---

# Composition boundary study finds moderate governance extends cooperative regime 2.5x while full governance imposes pure deadweight welfare loss

## Design

- **Type**: Multi-condition study (2 phases)
- **Phase 1 — Adversarial sweep**: 9 adversarial fractions (0-50%) x 4 governance configs x 4 population sizes (4,8,16,32) x 5 seeds = 720 runs
- **Phase 2 — Profile sweep**: 6 profile mixtures x 4 governance configs x 5 seeds at N=16 = 120 runs
- **Total**: 840 simulation runs
- **Epochs**: 20 per run, 10 steps per epoch
- **Seeds**: 42, 123, 456, 789, 1001

### Governance configurations

| Config | Tax | CB | Audit | Staking | Collusion det. |
|--------|-----|----|-------|---------|----------------|
| None | 0% | no | no | no | no |
| Basic | 5% | yes | no | no | no |
| Moderate | 8% | yes | p=0.10, 2x | no | no |
| Full | 12% | yes | p=0.15, 2.5x | min=5, slash=15% | yes |

### Profile mixtures (Phase 2)

| Label | Honest | Opportunistic | Deceptive | Adversarial |
|-------|--------|---------------|-----------|-------------|
| pure_honest | 100% | - | - | - |
| pure_adversarial | - | - | - | 100% |
| honest_opportunistic_70_30 | 70% | 30% | - | - |
| honest_deceptive_80_20 | 80% | - | 20% | - |
| realistic_mix | 55% | 25% | 12% | 8% |
| high_threat | 30% | 20% | 20% | 30% |

## Key results

### Phase 1: Regime boundaries

The regime heatmap shows moderate governance maintaining cooperative regime through 50% adversarial (5% collapse), while none/basic transition to contested at 15-20%. No critical adversarial fraction (majority collapse) was reached in any configuration.

### Phase 1: Welfare across governance

| Config | Welfare at 0% adv | Welfare at 50% adv | Toxicity at 50% adv |
|--------|-------------------|--------------------|--------------------|
| None | 15.96 | 6.40 | 0.425 |
| Basic | 15.94 | 5.74 | 0.418 |
| Moderate | 15.04 | 7.52 | 0.311 |
| Full | 12.06 | 5.02 | 0.319 |

Moderate governance Pareto-dominates the welfare-toxicity frontier at high adversarial fractions.

### Phase 2: Mixed profiles under moderate governance

Realistic mix (55/25/12/8) achieves 96.4% acceptance under moderate governance vs 88.5% under no governance. High-threat profile (30% adversarial + 20% deceptive) achieves cooperative regime under moderate governance but contested under none/basic.

## Claims extracted

- [[claim-moderate-governance-extends-cooperative-regime-to-50pct-adversarial]] — Moderate governance extends cooperative regime boundary 2.5x (medium confidence)
- [[claim-full-governance-welfare-penalty-exceeds-safety-gain-over-moderate]] — Full governance costs 20% welfare with no safety gain over moderate (medium confidence)
- [[claim-moderate-governance-pareto-dominates-welfare-toxicity-frontier]] — Moderate governance Pareto-dominates at high adversarial fractions (medium confidence)
- [[claim-realistic-mixed-profiles-are-governance-responsive-under-moderate-governance]] — Realistic mixed populations achieve near-pure-honest outcomes under moderate governance (low confidence)

## Claims enriched

- [[claim-governance-cost-paradox]] — New evidence: full vs moderate comparison quantifies the cost paradox as 20% welfare for zero safety gain
- [[claim-governance-parameters-have-narrow-safe-operating-envelopes]] — New boundary: adversarial composition shows gradual degradation rather than cliff effect

## Artifacts

- Summary: `runs/20260227_203024_composition_boundary_study/summary.json`
- Adversarial sweep CSV: `runs/20260227_203024_composition_boundary_study/csv/adversarial_sweep.csv` (720 rows)
- Profile sweep CSV: `runs/20260227_203024_composition_boundary_study/csv/profile_sweep.csv` (120 rows)
- Plots: regime heatmap, welfare/acceptance/toxicity vs adversarial, welfare-toxicity tradeoff, profile comparison, population size effect

## Reproduction

```bash
cd runs/20260227_203024_composition_boundary_study
python run_study.py
python generate_plots.py
```

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: composition, governance, adversarial, study -->
