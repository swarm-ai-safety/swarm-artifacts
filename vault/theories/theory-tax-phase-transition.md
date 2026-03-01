---
description: S-curve welfare response to tax (flat 0-5%, steep 5-10%, flat >12.5%) parallels first-order phase transitions in econophysics
type: theory
status: proposed
scope: "Baseline governance v1/v2, collusion tax context. Small-world topology k=4 p=0.15, 8-12 agents. Tax range 0-15%. Excludes kernel v4"

constituent_claims:
  - claim: "claim-tax-phase-transition"
    role: premise
  - claim: "claim-optimal-tax-range-0-to-5pct"
    role: evidence
  - claim: "claim-welfare-plateaus-above-12pct-tax"
    role: evidence
  - claim: "claim-tax-phase-transition-hysteresis-predicted-but-untested"
    role: prediction
  - claim: "claim-critical-slowing-down-would-confirm-tax-phase-transition"
    role: prediction

open_predictions:
  - "prediction-tax-hysteresis"
  - "prediction-critical-slowing-down"

created: 2026-02-28
updated: 2026-02-28

_schema:
  required: [description, type, status, scope, constituent_claims, created]
  optional: [open_predictions, updated]
  enums:
    type: [theory]
    status: [proposed, supported, contested, superseded]
    role: [premise, prediction, boundary, evidence]
  constraints:
    description: "max 200 chars, states the theory as a proposition, no trailing period"
    constituent_claims: "minimum 2 entries, each with claim ID and role"
    scope: "must specify domain, topology, agent types, or other applicability conditions"
---

# Transaction tax welfare response exhibits genuine phase transition characteristics with critical threshold at 5-10%

## Constituent claims

| Claim | Role | Confidence |
|-------|------|------------|
| [[claim-tax-phase-transition]] | premise | high |
| [[claim-optimal-tax-range-0-to-5pct]] | evidence | medium |
| [[claim-welfare-plateaus-above-12pct-tax]] | evidence | medium |
| [[claim-tax-phase-transition-hysteresis-predicted-but-untested]] | prediction | low |
| [[claim-critical-slowing-down-would-confirm-tax-phase-transition]] | prediction | low |

## Scope & boundary conditions

**Validated domains:**
- **Baseline governance v1**: 80 runs, 10 seeds, 8 agents. Phase transition replicates (d=1.13-1.41 across adjacent tax pairs, Bonferroni-corrected).
- **Baseline governance v2**: 700 runs, 100 seeds, 8 agents. Primary evidence: S-curve with 3% decline 0-5%, 14% decline 5-10%, flat >12.5% (d=1.18, Bonferroni-corrected).
- **Collusion tax effect**: 160 runs, 10 seeds, 12 agents. Monotonic decline confirmed with 3-4x larger effect sizes (d=1.10-4.80), possibly amplified by collusion-enabled composition.

**Excluded domains (known boundary violation):**
- **Kernel v4 code scenario**: welfare monotonically *increases* 0%→15% tax. No S-curve, no transition detected. N=5 seeds, underpowered but directionally contradictory.

**Parameter scope:**
- Tax range: 0-15%
- Topology: small-world (k=4, p=0.15)
- Population: 8-12 agents
- No redistribution modeled

## Thesis

The welfare response to transaction tax is not a smooth, proportional decline but exhibits the three hallmarks of a first-order phase transition:

1. **Pre-transition stability (0-5% tax).** Welfare declines only ~3%. The ecosystem absorbs low taxation through behavioral adaptation — marginal transactions remain profitable and agents maintain participation levels ([[claim-optimal-tax-range-0-to-5pct]]).

2. **Sharp transition (5-10% tax).** Welfare drops 14% in a narrow band. This is consistent with a cascade mechanism: once tax exceeds a critical threshold, marginal interactions become unprofitable, agents withdraw from participation, which further reduces welfare for remaining agents, creating a positive feedback loop.

3. **Post-transition plateau (>12.5% tax).** Welfare flattens because the ecosystem has already contracted to its minimum viable state ([[claim-welfare-plateaus-above-12pct-tax]]). Further taxation has no additional effect because there are no more marginal interactions to eliminate.

This S-curve mirrors first-order phase transitions documented in econophysics:
- **Khashanah & Simaan (PNAS 2022)**: agent withdrawal cascades at critical thresholds in competitive markets driven by network effects.
- **Gualdi et al. (2015)**: first-order-like transitions with hysteresis in minimal macroeconomic agent-based models.

If the analogy holds, catastrophe theory makes two specific predictions:

**Prediction 1: Hysteresis.** Raising tax through the transition and then lowering it back should NOT restore the original welfare level. Agents who withdrew during the cascade may not re-enter at the same threshold, creating an irreversible welfare loss ([[claim-tax-phase-transition-hysteresis-predicted-but-untested]]).

**Prediction 2: Critical slowing down.** Near the transition point (5-10%), the system should exhibit slower convergence to equilibrium — measured as increased variance or autocorrelation in welfare time series ([[claim-critical-slowing-down-would-confirm-tax-phase-transition]]).

## Predictions

1. **Hysteresis test.** Run a tax ramp-up (0%→15%) followed by ramp-down (15%→0%) within a single simulation. If genuine phase transition, welfare at 5% during ramp-down should be significantly lower than welfare at 5% during ramp-up. Effect size: expect d≥0.5 between ascending and descending welfare at matched tax rates.

2. **Critical slowing down.** Measure convergence time (epochs to reach steady-state welfare) as a function of tax rate. If genuine phase transition, convergence time should peak in the 5-10% band — potentially 2-5x longer than at 0% or 15%.

3. **Topology dependence of critical point.** If the transition is driven by network cascade dynamics, the critical tax rate should shift with network connectivity: lower clustering → lower critical tax (transitions occur earlier). Test with complete graph (should have no transition — all interactions equally affected) and ring topology (should have sharper transition — cascade propagation constrained).

4. **Population size scaling.** If genuine critical phenomenon, the transition should sharpen with larger populations (analogous to thermodynamic limit). Test with N=20, 50, 100 agents — the slope in the 5-10% band should steepen.

## Falsification criteria

This theory would be **falsified** if:
- **No hysteresis detected** at N≥30 seeds: welfare at 5% is statistically identical on ramp-up and ramp-down (d<0.2, p>0.05 Bonferroni-corrected). This would suggest the S-curve is a smooth nonlinearity, not a phase transition.
- **No critical slowing down**: convergence time is constant across all tax rates. This would rule out cascade-driven dynamics.
- **The kernel v4 reversal replicates at N≥20**: if welfare reliably increases with tax in multiple scenarios, the S-curve is scenario-specific rather than a universal property of multi-agent economies under taxation.
- **Complete graph shows identical S-curve**: if the transition is topology-independent, the network cascade mechanism is wrong.
- **Redistribution eliminates the transition**: if returning tax revenue as public goods smooths the S-curve, the transition is an artifact of wealth extraction rather than a genuine dynamical phase change.

## Open questions

- What is the microscopic mechanism? Is it agent withdrawal, interaction frequency reduction, or behavioral strategy switching?
- Does the collusion-enabled amplification (3-4x effect sizes) indicate that collusion networks act as cascade accelerators near the critical point?
- Can the critical tax rate be predicted from network properties (clustering coefficient, degree distribution)?
- Is there a second transition at very high tax rates (>20%) where agents adopt qualitatively different strategies?
- How does the welfare non-normality at extreme tax rates ([[claim-welfare-non-normality-at-extreme-tax]]) relate to the post-transition state?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, transaction-tax, phase-transition, theory -->
