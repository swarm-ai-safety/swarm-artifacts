---
description: 2-factor mesa bridge study (adaptive vs static x 11 rho levels, 5 seeds) reveals adaptive governance reduces toxicity 34% but at 70% welfare cost
type: experiment
status: completed
run_id: 20260224-220829_mesa_governance_study
experiment_type: study
created: '2026-02-27'
aliases:
- mesa_governance_study
cssclasses:
- experiment
- experiment-study
tags:
- mesa
- governance
- externality-internalization
- adaptive-acceptance
- toxicity-welfare-tradeoff
graph-group: experiment
---

# mesa bridge governance study shows adaptive acceptance trades welfare for toxicity reduction while static externality tax is pure deadweight loss

## Design

- **Hypothesis**: Adaptive acceptance thresholds that internalize externalities can reduce toxicity, but at what welfare cost compared to static (non-adaptive) taxation?
- **Type**: 2-factor study (acceptance regime x externality internalization)
- **Factor 1**: Acceptance regime — adaptive (threshold = 0.5 + 0.3 * rho_a) vs static (fixed threshold)
- **Factor 2**: Externality internalization (rho_a) — 0.0 to 1.0 in 0.1 increments (11 levels)
- **Seeds**: [42, 123, 256, 789, 1024]
- **Total runs**: 110 (2 regimes x 11 rho levels x 5 seeds)
- **Metrics**: toxicity, total_welfare, quality_gap, acceptance_rate, per-archetype quality (cooperative, selfish, exploitative)

## Key results

### Adaptive governance reduces toxicity monotonically

Under the adaptive regime, increasing rho_a from 0.0 to 1.0 reduces toxicity from 0.237 to 0.157 (a 33.8% reduction). The relationship is strongly linear (Pearson r = -0.90, R-squared = 0.81 across all 55 adaptive runs). Welch's t-test for rho=0.0 vs rho=1.0: d = 12.22, p < 1e-82, Bonferroni-corrected (k=4 metrics).

### Static regime shows zero behavioral change under externality tax

Under the static regime, toxicity (0.237), quality_gap (0.434), and acceptance_rate (0.590) are **identical** across all rho levels — the same values at rho=0.0 and rho=1.0. Only total_welfare decreases (1141 → 723, d = 14.94). This demonstrates that externality internalization without adaptive screening is pure deadweight loss: the tax extracts resources but produces no behavioral or safety improvement.

### Adaptive vs static at rho=0.5

| Metric | Adaptive | Static | d | p (Bonferroni k=4) |
|--------|----------|--------|---|--------------------|
| Toxicity | 0.214 ± 0.005 | 0.237 ± 0.008 | -3.26 | 1.0e-06 *** |
| Welfare | 907 ± 25 | 932 ± 26 | -0.98 | 0.48 ns |
| Acceptance | 0.528 ± 0.010 | 0.590 ± 0.014 | -5.04 | 6.6e-15 *** |
| Quality gap | 0.425 ± 0.017 | 0.434 ± 0.017 | -0.48 | 1.0 ns |

At moderate governance (rho=0.5), adaptive achieves significantly lower toxicity and acceptance rate with only a modest, non-significant welfare cost — a favorable operating point.

### Mesa agent objectives are invariant to governance

Agent archetype probabilities are constant across all 110 runs:
- Cooperative: p = 0.791
- Selfish: p = 0.408
- Exploitative: p = 0.325

This confirms that mesa-optimized agents do not adapt their objectives to governance regimes. The governance mechanism works by filtering (selective acceptance/rejection), not by changing agent behavior. This is a critical property for mesa alignment: governance is a selection mechanism, not an alignment mechanism.

### Governance efficiency is approximately constant

The marginal toxicity reduction per 1000 welfare units is roughly constant across the rho range:
- rho=0.3: 0.11 per 1k welfare
- rho=0.7: 0.09 per 1k welfare
- rho=1.0: 0.10 per 1k welfare

This suggests a linear tradeoff frontier — there is no diminishing return in toxicity reduction efficiency, nor is there a "sweet spot" where governance becomes disproportionately efficient.

### Extreme governance destroys welfare

At rho=1.0 (full internalization), adaptive governance reduces acceptance from 59% to 19% and welfare from 1141 to 340 (a 70.2% collapse, d = 21.50, Bonferroni p < 1e-252). The toxicity reduction (33.8%) comes at catastrophic welfare cost. This extends [[claim-governance-cost-paradox]] to the mesa bridge scenario.

## Claims affected

- **New**: [[claim-adaptive-acceptance-reduces-toxicity-monotonically-with-externality-internalization]] — r=-0.90, d=12.22
- **New**: [[claim-static-externality-tax-is-pure-deadweight-welfare-loss]] — zero behavioral change, only welfare decreases
- **New**: [[claim-mesa-agent-objectives-are-invariant-to-governance-regime]] — all 3 archetype probabilities constant across 110 runs
- **New**: [[claim-adaptive-governance-trades-welfare-for-toxicity-at-constant-marginal-rate]] — ~0.10 per 1k welfare, linear frontier
- **Supports**: [[claim-governance-cost-paradox]] — welfare cost exceeds toxicity benefit at rho>=0.8
- **Supports**: [[claim-tax-welfare-tradeoff]] — welfare monotonically declines with rho under both regimes

## Artifacts

- Summary: `runs/20260224-220829_mesa_governance_study/summary.json`
- CSV: `runs/20260224-220829_mesa_governance_study/sweep_results.csv`
- Plots: `runs/20260224-220829_mesa_governance_study/plots/`
- Analysis: `runs/20260224-220829_mesa_governance_study/plot_results.py`

## Reproduction

```bash
python -m swarm study mesa_bridge_governance --regime adaptive,static --rho 0.0:0.1:1.0 --seeds 42,123,256,789,1024
```

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: mesa, governance, externality-internalization, adaptive-acceptance, toxicity-welfare-tradeoff -->
