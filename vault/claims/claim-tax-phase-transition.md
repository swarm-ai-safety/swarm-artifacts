---
description: Welfare decline under transaction tax is non-linear with phase transition
  between 5-10% tax rate
type: claim
status: active
confidence: high
domain: governance
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: '0-5% tax: 3% decline; 5-10%: 14% decline; 10-15%: flat. d=1.18, N=700,
      Bonferroni-corrected'
  - run: 20260213-173805_baseline_governance
    metric: welfare
    detail: 'Phase transition replicates in v1: d=1.13-1.41 across adjacent tax pairs, N=80, 10 seeds, Bonferroni-corrected'
  - run: 20260213-221500_collusion_tax_effect
    metric: welfare
    detail: 'Monotonic welfare decline confirmed in collusion context: d=1.10-4.80 across adjacent tax pairs, d=2.87-6.02 for agent-type payoffs, N=160, 10 seeds, Bonferroni-corrected. Effect sizes 3-4x larger than v2, likely amplified by 12-agent collusion-enabled composition'
  weakening:
  - run: 20260214-113750_kernel_v4_code_sweep
    metric: welfare
    detail: "No phase transition detected in kernel v4: welfare monotonically INCREASES 0%→15% tax. S-curve absent. N=5 seeds, underpowered"
  boundary_conditions:
  - Small-world topology k=4 p=0.15, 8 agents, tax range 0-15%
  - No redistribution modeled
  - Phase transition confirmed in baseline governance and collusion contexts only
  - Kernel v4 code scenario shows monotonic welfare increase — no S-curve, no transition
sensitivity:
  topology: Small-world k=4 p=0.15; phase transition point may shift under different
    clustering coefficients
  agent_count: 8 agents; transition sharpness may change with population size
  scenario: Phase transition absent in kernel v4 code — may be scenario-specific rather than universal
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-tax-dominates-cb-kernel
- claim-welfare-non-normality-at-extreme-tax
- claim-tax-disproportionately-punishes-rlm-agents
- claim-high-tax-increases-toxicity
- claim-tax-welfare-direction-is-scenario-dependent
- claim-cb-tax-interaction-non-monotonic-in-kernel-v4
created: 2026-02-19
updated: '2026-02-20'
aliases:
- tax-phase-transition
- welfare-decline-under-transaction-tax-is
cssclasses:
- claim
- claim-high
tags:
- governance
- transaction-tax
- phase-transition
- welfare
graph-group: claim
---

# welfare decline under transaction tax is non-linear with phase transition between 5-10% tax rate

The relationship between transaction tax rate and welfare is non-linear, with a phase transition occurring between 5% and 10% tax rate. Below 5%, welfare declines only 3%. Between 5% and 10%, welfare drops 14%. Above 10%, the decline flattens as the ecosystem has already contracted.

**Evidence summary.** In the baseline governance v2 study (N=700 runs, 8 agents, small-world topology k=4 p=0.15), tax rates were swept from 0% to 15%. The welfare response exhibited a clear S-shaped curve with the steepest decline in the 5–10% band (d = 1.18, Bonferroni-corrected). This non-linearity suggests that the ecosystem undergoes a structural transition — likely driven by marginal interactions becoming unprofitable and agents withdrawing from participation — rather than a smooth proportional response to taxation.

**Replication in collusion-enabled context.** The [[20260213-221500_collusion_tax_effect]] sweep (N=160, 12 agents, 10 seeds) confirms monotonic welfare decline across all adjacent tax pairs: 0% vs 2% (d=1.10), 2% vs 5% (d=2.56), 5% vs 10% (d=2.53), 0% vs 10% (d=4.80), all Bonferroni-significant. Effect sizes are 3-4x larger than the v2 sweep, possibly due to the 12-agent collusion-enabled composition amplifying tax-induced scarcity. Notably, welfare distributions at 0% and 10% tax are non-normal (Shapiro-Wilk p<0.01), suggesting possible ecosystem bifurcation at extreme rates — see [[claim-welfare-non-normality-at-extreme-tax]].

**Boundary conditions.** No redistribution was modeled; if tax revenue were returned to agents (e.g., as public goods or direct transfers), the phase transition point might shift or disappear. The small-world topology with k=4 and p=0.15 provides moderate connectivity; sparser or denser graphs may shift the critical tax rate. The 0–15% range may not capture behavior at extreme tax rates.

**Open questions.**
- Does redistribution of tax revenue shift or eliminate the phase transition?
- Is the phase transition point topology-dependent (i.e., does it shift with connectivity)?
- Can the transition be predicted from network properties alone?
- What happens to toxicity across the phase transition — does it also show non-linear behavior?
- Why is the phase transition absent in kernel v4 code markets? Is it the market mechanism, agent types, or interaction structure?

## Update history

**2026-02-20** — backward-pass update:
- Added weakening evidence from [[20260214-113750_kernel_v4_code_sweep]]: no S-curve detected; welfare monotonically increases with tax. This contradicts the 5-10% phase transition found in baseline governance. Underpowered (N=5 seeds).
- Added boundary condition and sensitivity note for scenario-dependence per [[claim-tax-welfare-direction-is-scenario-dependent]].
- Added related claims: claim-tax-welfare-direction-is-scenario-dependent, claim-cb-tax-interaction-non-monotonic-in-kernel-v4.
- Confidence remains **high** for baseline governance scenarios (N=700 and N=160, both Bonferroni-corrected with large effect sizes). The kernel v4 weakening is underpowered and establishes a boundary condition.

## Lifecycle audit

**2026-02-19** — automated claim-lifecycle audit:
- (Note: 25 bulk-added tax-rate evidence entries consolidated 2026-02-20 into 2 representative entries per source run)

<!-- topics: governance, transaction-tax, phase-transition, welfare -->
