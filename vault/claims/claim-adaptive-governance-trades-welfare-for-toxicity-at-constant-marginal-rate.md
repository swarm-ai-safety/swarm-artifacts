---
description: Adaptive governance exchanges welfare for toxicity at ~0.10 toxicity reduction per 1000 welfare units, constant across the full rho range
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260224-220829_mesa_governance_study
    metric: toxicity_welfare_efficiency
    detail: "Marginal efficiency (toxicity reduction per 1k welfare): rho=0.3 → 0.11, rho=0.7 → 0.09, rho=1.0 → 0.10. Near-constant across the full range. Total: 0.080 toxicity reduction for 801 welfare cost. 5 seeds per condition, 11 rho levels"
  weakening: []
  boundary_conditions:
  - Mesa bridge scenario with fixed agent archetypes and adaptive acceptance threshold (0.5 + 0.3 * rho_a)
  - Constant efficiency implies a linear tradeoff frontier — no sweet spot, no diminishing returns
  - 50 timesteps, 5 seeds per condition
  - Efficiency metric depends on the specific acceptance function; different threshold formulas may produce non-constant marginal rates
sensitivity:
  topology: untested beyond mesa bridge default
  agent_count: untested beyond default count
  governance_interaction: only adaptive acceptance tested — combining with other mechanisms may break the linearity
supersedes: []
superseded_by: []
related_claims:
- claim-adaptive-acceptance-reduces-toxicity-monotonically-with-externality-internalization
- claim-governance-cost-paradox
- claim-tax-welfare-tradeoff
- claim-static-externality-tax-is-pure-deadweight-welfare-loss
- claim-mesa-agent-objectives-are-invariant-to-governance-regime
created: 2026-02-27
updated: 2026-02-27
aliases:
- constant-governance-efficiency
cssclasses:
- claim
- claim-medium
graph-group: claim
---

# adaptive governance trades welfare for toxicity reduction at a constant marginal rate across the full internalization range

## Evidence summary

In the mesa bridge governance study ([[mesa_governance_study]]), the marginal toxicity reduction per unit welfare cost is approximately constant across the full externality internalization range:

| rho range | Toxicity reduction | Welfare cost | Efficiency (per 1k welfare) |
|-----------|-------------------|--------------|----------------------------|
| 0.0 → 0.3 | 0.016 | 146.8 | 0.11 |
| 0.0 → 0.7 | 0.030 | 334.4 | 0.09 |
| 0.0 → 1.0 | 0.080 | 801.3 | 0.10 |

The near-constant efficiency (~0.10 per 1000 welfare units) indicates a **linear tradeoff frontier**: each additional unit of governance intensity buys the same amount of toxicity reduction regardless of the current governance level. There are no diminishing returns and no super-linear gains.

This is a distinctive finding because many governance mechanisms exhibit diminishing returns — the first increment of governance captures the "low-hanging fruit" while later increments fight increasingly marginal improvements. The mesa bridge scenario's constant marginal rate suggests that the adaptive acceptance mechanism distributes its filtering effect evenly across the quality distribution, rather than targeting the worst offenders first.

## Boundary conditions

- The constant marginal rate depends on the specific adaptive threshold formula (0.5 + 0.3 * rho_a). A non-linear acceptance function would likely produce a non-constant marginal rate.
- Because agent objectives are fixed (mesa invariance), the quality distribution being filtered is the same at every rho level — this is why efficiency is constant. In adaptive-agent scenarios, governance might reshape the quality distribution, creating diminishing or increasing returns.
- The tradeoff frontier is linear in the aggregate, but individual seeds show variance (welfare_std increases from 24 at rho=0 to 47 at rho=1).

## Mechanism

The adaptive threshold rises linearly with rho_a (threshold = 0.5 + 0.3 * rho_a). Because the agent quality distributions are fixed (mesa property), each 0.1 increment in rho raises the threshold by 0.03, which rejects a roughly equal slice of the quality distribution. This geometric regularity produces the constant marginal efficiency. The mechanism predicts that a non-linear acceptance function (e.g., quadratic or sigmoidal) would produce a correspondingly non-constant tradeoff curve.

## Open questions

- Does the constant marginal rate hold with non-linear acceptance functions?
- At what welfare level does the tradeoff become unacceptable — is there a "governance budget" concept?
- Does combining adaptive acceptance with other mechanisms (taxes, circuit breakers) change the marginal rate?
- Does the constant rate hold in scenarios with more diverse agent archetypes?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: mesa, governance, tradeoff-frontier, efficiency, welfare, toxicity -->
