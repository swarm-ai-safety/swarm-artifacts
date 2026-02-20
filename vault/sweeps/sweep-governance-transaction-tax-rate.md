---
description: 'Sweep series for transaction tax rate: 4 runs, 1100 total configurations'
type: sweep-summary
status: active
parameter: governance.transaction_tax_rate
values_tested:
- '0.0'
- '0.02'
- '0.025'
- '0.05'
- '0.075'
- '0.1'
- '0.125'
- '0.15'
created: '2026-02-13'
updated: '2026-02-19'
aliases:
- governance.transaction_tax_rate
- sweep-governance-transaction-tax-rate
cssclasses:
- sweep-summary
tags:
- baseline
- circuit-breaker
- circuit-breaker-enabled
- collusion
- collusion-detection
- collusion-detection-enabled
- collusion-penalty-multiplier
- governance
- payoff
- quality
- study
- sweep
- toxicity
- transaction-tax
- transaction-tax-rate
- welfare
graph-group: sweep
---

# transaction tax rate sweep series shows significant effects across 4 independent runs

## Runs in this sweep

| Run ID | Date | Type | Seeds | Levels | Total Runs | Bonferroni Sig |
|--------|------|------|-------|--------|------------|----------------|
| 20260213-173805_baseline_governance | 2026-02-13 | sweep | 1 | 4 | 80 | 4 |
| 20260213-202050_baseline_governance_v2 | 2026-02-13 | sweep | 1 | 7 | 700 | 18 |
| 20260213-204503_agent_lab_research_safety_study | 2026-02-13 | study | 1 | 0 | 160 | 0 |
| 20260213-221500_collusion_tax_effect | 2026-02-13 | sweep | 1 | 4 | 160 | 21 |

## Values tested

`governance.transaction_tax_rate`: 0.0, 0.02, 0.025, 0.05, 0.075, 0.1, 0.125, 0.15

## Convergence

4 runs have explored this parameter with a combined 1100 configurations.
Effect is robust: Bonferroni-significant findings replicated across runs.

## Open questions

- Has the parameter space been fully covered?
- Are there interaction effects with other parameters?
- Do results generalize across topologies?

---

Topics:
- [[_index]]

<!-- topics: baseline, circuit-breaker, circuit-breaker-enabled, collusion, collusion-detection, collusion-detection-enabled, collusion-penalty-multiplier, governance, payoff, quality, study, sweep, toxicity, transaction-tax, transaction-tax-rate, welfare -->
