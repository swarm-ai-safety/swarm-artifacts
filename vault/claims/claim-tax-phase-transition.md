---
description: "Welfare decline under transaction tax is non-linear with phase transition between 5-10% tax rate"
type: claim
status: active
confidence: high
domain: governance
evidence:
  supporting:
    - run: "20260213-202050_baseline_governance_v2"
      metric: "welfare"
      detail: "0-5% tax: 3% decline; 5-10%: 14% decline; 10-15%: flat. d=1.18, N=700, Bonferroni-corrected"
  weakening: []
  boundary_conditions:
    - "Small-world topology k=4 p=0.15, 8 agents, tax range 0-15%"
    - "No redistribution modeled"
sensitivity:
  topology: "Small-world k=4 p=0.15; phase transition point may shift under different clustering coefficients"
  agent_count: "8 agents; transition sharpness may change with population size"
supersedes: []
superseded_by: []
related_claims:
  - claim-tax-welfare-tradeoff
  - claim-tax-dominates-cb-kernel
created: 2026-02-19
updated: 2026-02-19
---

## Tax Phase Transition

The relationship between transaction tax rate and welfare is non-linear, with a phase transition occurring between 5% and 10% tax rate. Below 5%, welfare declines only 3%. Between 5% and 10%, welfare drops 14%. Above 10%, the decline flattens as the ecosystem has already contracted.

**Evidence summary.** In the baseline governance v2 study (N=700 runs, 8 agents, small-world topology k=4 p=0.15), tax rates were swept from 0% to 15%. The welfare response exhibited a clear S-shaped curve with the steepest decline in the 5–10% band (d = 1.18, Bonferroni-corrected). This non-linearity suggests that the ecosystem undergoes a structural transition — likely driven by marginal interactions becoming unprofitable and agents withdrawing from participation — rather than a smooth proportional response to taxation.

**Boundary conditions.** No redistribution was modeled; if tax revenue were returned to agents (e.g., as public goods or direct transfers), the phase transition point might shift or disappear. The small-world topology with k=4 and p=0.15 provides moderate connectivity; sparser or denser graphs may shift the critical tax rate. The 0–15% range may not capture behavior at extreme tax rates.

**Open questions.**
- Does redistribution of tax revenue shift or eliminate the phase transition?
- Is the phase transition point topology-dependent (i.e., does it shift with connectivity)?
- Can the transition be predicted from network properties alone?
- What happens to toxicity across the phase transition — does it also show non-linear behavior?

<!-- topics: governance, transaction-tax, phase-transition, welfare -->
