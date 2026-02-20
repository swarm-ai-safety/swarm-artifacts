---
description: Full factorial parameter grid crossed with multiple seeds to detect main effects and interactions in governance
  mechanisms
type: method
status: active
category: governance-design
aliases:
- parameter sweep
- factorial design
- grid sweep
- full factorial
- factorial-sweep
cssclasses:
- method
graph-group: method
tags:
- experimental-design
- parameter-sweep
- factorial
- governance
- statistical-methods
created: 2026-02-19
updated: 2026-02-19
---

# Factorial parameter sweeps cross governance parameters with multiple seeds to detect main effects and interactions

## What it does

A factorial sweep enumerates every combination of parameter levels and runs each combination across multiple random seeds. This produces a complete grid of outcomes that supports estimation of main effects (how each parameter independently affects metrics), interaction effects (how parameter combinations produce non-additive outcomes), and within-cell variance (how sensitive results are to random seed).

**Inputs:** a list of parameters, each with a set of discrete levels; a seed count; and a SWARM scenario definition.
**Outputs:** a sweep_results.csv with one row per (parameter combination, seed) pair, plus summary statistics aggregated across seeds.

## Why it matters

Multi-agent simulations exhibit complex nonlinear dynamics — the effect of enabling circuit breakers may depend on the transaction tax rate. One-parameter-at-a-time sweeps cannot detect these interactions. Factorial designs expose them by construction. The [[20260213-202050_baseline_governance_v2]] sweep crossed 7 transaction_tax_rate levels with 2 circuit_breaker_enabled states, producing a 7x2 = 14-cell grid. The [[cross-correlation]] analysis detected that transaction_tax_rate and circuit_breaker_enabled have co-occurring significant effects on welfare, flagging the pair as an interaction candidate.

Without factorial designs, SWARM would risk making claims about individual mechanisms that are actually conditional on other parameters being held at specific values.

## How to apply it

**Design steps:**

1. **Select parameters and levels.** Choose governance parameters to vary and define discrete levels for each. Keep the grid tractable — a 7x2x3 design with 50 seeds produces 2,100 runs.
2. **Define the scenario.** Use a SWARM scenario YAML specifying the base configuration, with parameter overrides defined in the sweep grid.
3. **Set seed count.** More seeds reduce within-cell variance and increase power for detecting effects. SWARM convention: minimum 10 seeds for pilot, 50 seeds for confirmatory sweeps.
4. **Execute the sweep.**

```bash
python -m swarm sweep <scenario> --seeds <N>
```

5. **Analyze with pairwise comparisons.** For each metric, compute pairwise t-tests between parameter level groups. Apply [[bonferroni-correction]] for confirmatory findings and [[benjamini-hochberg]] for exploratory screening. Report [[cohens-d]] for every comparison.

**Grid structure example** (baseline_governance_v2):

```
transaction_tax_rate:      [0.0, 0.025, 0.05, 0.075, 0.1, 0.125, 0.15]
circuit_breaker_enabled:   [False, True]
seeds:                     50
--------------------------------------------------------------
Total cells:               7 × 2 = 14
Total runs:                14 × 50 = 700
Pairwise comparisons:      C(7,2) × 2 metrics × 2 CB states = many
```

6. **Check for interactions.** Compare effect sizes of one parameter across levels of the other. If d changes substantially, an interaction is present and the main effect should not be interpreted in isolation.

## Assumptions and limitations

- **Combinatorial explosion.** Adding parameters or levels multiplies the grid exponentially. A 5-parameter sweep with 5 levels each and 50 seeds requires 156,250 runs. In practice, SWARM sweeps are limited to 2-3 parameters at a time, with interactions across sweeps detected by the [[cross-correlation]] analysis.
- **Assumes parameter independence is worth testing.** Factorial designs invest heavily in interaction detection. If domain knowledge strongly suggests no interactions, a fractional factorial or Latin hypercube design may be more efficient.
- **Equal allocation.** Standard factorial designs allocate the same number of seeds to every cell, even those far from the region of interest. Adaptive designs could focus seeds on interesting parameter regions, but SWARM does not yet implement this.
- **Discrete levels only.** Continuous parameters must be discretized, potentially missing effects that occur between levels. The tax rate sweep uses 2.5% increments — a phase transition at 3% would be invisible.
- **Analysis assumes independent seeds.** The pairwise t-test framework treats seeds within a cell as independent samples. If the random seed interacts with the parameter (e.g., certain seeds produce pathological topologies), this assumption is violated.

## Evidence of effectiveness

Factorial sweeps are the primary experimental design in SWARM and have produced the majority of high-confidence claims:

- [[20260213-202050_baseline_governance_v2]] — the definitive 700-run factorial sweep (7 tax rates x 2 CB states x 50 seeds). Produced 18 Bonferroni-significant findings including the d=1.18 tax-welfare effect underlying [[claim-tax-welfare-tradeoff]] and supporting evidence for [[claim-circuit-breakers-dominate]].
- [[20260213-173805_baseline_governance]] — the v1 sweep (280 runs, 10 seeds) that first identified the tax-welfare relationship (d=1.41) and the governance cost paradox documented in [[claim-governance-cost-paradox]].
- [[20260211-000149_kernel_market_governance_comparison]] — a 7-regime sweep (70 runs, 10 seeds) comparing governance compositions. The factorial structure enabled direct CB-only vs full-governance comparison (d=1.64) that anchors [[claim-circuit-breakers-dominate]].
- [[20260213-221500_collusion_tax_effect]] — swept collusion_penalty_multiplier and transaction_tax_rate jointly, enabling the [[cross-correlation]] analysis to detect their co-occurring Bonferroni-significant effects on toxicity_rate.

---

Topics:
- [[_index]]

<!-- topics: experimental-design, parameter-sweep, factorial, governance, statistical-methods -->
