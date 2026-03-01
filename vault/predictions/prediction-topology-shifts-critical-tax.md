---
description: Network topology should shift the critical tax rate — complete graphs eliminate the transition, rings sharpen it
type: prediction
status: open
source_claim: "theory-tax-phase-transition"
hypothesis: "If the tax phase transition is driven by network cascade dynamics, then (a) complete graphs should show no transition (all interactions equally affected), (b) ring topology should show a sharper transition at a lower critical tax rate, and (c) scale-free topology should show heterogeneous response with hubs transitioning last"
test_protocol: "Run baseline governance tax sweep (0-15%) on 4 topologies: small-world (control), complete, ring, scale-free. 20 seeds x 7 tax rates x 4 topologies = 560 runs. Compare S-curve shape and critical tax rate across topologies."

resolution:
  run: ""
  outcome: ""
  detail: ""

created: 2026-02-28

_schema:
  required: [description, type, status, source_claim, hypothesis, created]
  optional: [test_protocol, resolution, updated]
  enums:
    type: [prediction]
    status: [open, confirmed, refuted, expired]
    outcome: [confirmed, refuted, inconclusive]
  constraints:
    description: "max 200 chars, no trailing period"
    hypothesis: "must be a precise if-then statement"
    source_claim: "must reference a valid claim or theory ID"
---

# Network topology shifts the critical tax rate and transition sharpness

## Source

Derived from [[theory-tax-phase-transition]]. If the tax transition is driven by network cascade dynamics (agent withdrawal propagating through connections), topology should be a critical moderator.

## Hypothesis

Three topology-specific predictions:

1. **Complete graph: no transition.** When all agents are connected to all others, there are no local cascade dynamics — all interactions are affected equally by tax. The S-curve should flatten to a smooth, proportional decline.

2. **Ring topology: sharper transition at lower critical tax.** Ring topology constrains cascade propagation to nearest neighbors, creating a serial chain reaction. Once one agent withdraws, its two neighbors lose their primary interaction partner. The transition should be sharper (steeper slope in the 5-10% band) and occur at a lower tax rate.

3. **Scale-free topology: heterogeneous response.** High-degree hub agents absorb tax impact through diversified interactions, while low-degree peripheral agents are more vulnerable. The transition should be gradual, with periphery agents transitioning first and hubs last.

## Test protocol

- **Scenario:** Baseline governance, 8 agents
- **Topologies:**
  1. Small-world (k=4, p=0.15) — control, replicating existing evidence
  2. Complete graph (k=7)
  3. Ring (k=2, p=0)
  4. Scale-free (Barabasi-Albert, m=2)
- **Tax rates:** 0%, 2.5%, 5%, 7.5%, 10%, 12.5%, 15%
- **Seeds:** 20 per cell (560 total runs)
- **Key metrics:**
  1. Mean welfare at each tax rate per topology
  2. S-curve slope in the 5-10% band (estimated via finite differences)
  3. Critical tax rate (inflection point of fitted logistic curve)
- **Statistical test:** 2-way ANOVA (topology x tax rate), Bonferroni-corrected post-hoc
- **Falsification threshold:** If complete graph shows identical S-curve to small-world (interaction F<1, p>0.20), the network cascade mechanism is wrong

## Resolution

_Fill this section when the prediction is tested._

| Field | Value |
|-------|-------|
| Run | `` |
| Outcome | |
| Detail | |

## Implications

**If confirmed:** Establishes topology as a governance design parameter — practitioners can shift the critical tax rate by modifying network structure. Strengthens the phase transition interpretation by demonstrating topology-dependence consistent with cascade dynamics.

**If refuted (complete graph shows same S-curve):** The transition is not driven by network cascades but by individual agent economics (marginal interaction profitability). Topology is irrelevant to governance cost, simplifying the design space.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, transaction-tax, phase-transition, topology, prediction -->
