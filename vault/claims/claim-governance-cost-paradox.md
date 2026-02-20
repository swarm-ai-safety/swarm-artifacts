---
description: "Full governance stacks impose larger welfare costs than toxicity reduction benefits at all adversarial levels tested"
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
    - run: "20260211-232952_gastown_composition_study"
      metric: "welfare"
      detail: "Welfare penalty at 0% adversarial = -215.9 (58% reduction), N=42"
  weakening: []
  boundary_conditions:
    - "GasTown workspace, 7 agents, 30 epochs, full governance stack"
sensitivity:
  topology: "Tested on GasTown small-world only; unknown whether hub-and-spoke or ring topologies amplify or dampen the cost"
  agent_count: "7 agents; cost-per-agent may scale non-linearly with larger populations"
supersedes: []
superseded_by: []
related_claims:
  - claim-tax-welfare-tradeoff
  - claim-quality-gate-dominates
created: 2026-02-19
updated: 2026-02-19
---

## Governance Cost Paradox

The full governance stack — comprising transaction taxes, circuit breakers, collusion penalties, and reputation decay — imposes welfare costs that exceed the toxicity reduction benefits at every adversarial penetration level tested (0%, 10%, 20%, 30%).

**Evidence summary.** In the GasTown composition study (N=42 runs, 7 agents, 30 epochs), the fully governed regime produced a welfare penalty of -215.9 at 0% adversarial penetration, representing a 58% reduction relative to the ungoverned baseline. As adversarial penetration increased, the governance stack did reduce toxicity, but the marginal welfare cost of each unit of toxicity reduction remained net-negative across all tested levels.

**Boundary conditions.** This result is established only for the GasTown workspace with 7 agents and 30-epoch horizons. The full governance stack was applied as a monolithic bundle; individual mechanism contributions are decomposed in related claims (see `claim-quality-gate-dominates`, `claim-tax-welfare-tradeoff`). It is unknown whether longer horizons would allow reputation effects to eventually offset the welfare penalty.

**Open questions.**
- Does the paradox hold under partial governance stacks (e.g., tax + quality gate only)?
- Is there a population threshold above which governance overhead amortizes?
- How does the welfare penalty interact with redistribution mechanisms?

<!-- topics: governance, welfare, cost-benefit, gastown -->
