---
description: Full governance stacks impose larger welfare costs than toxicity reduction
  benefits at all adversarial levels tested
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260211-232952_gastown_composition_study
    metric: welfare
    detail: Welfare penalty at 0% adversarial = -215.9 (58% reduction), N=42
  - run: 20260213-173805_baseline_governance
    metric: welfare
    detail: 'Tax-induced welfare decline replicates governance cost: d=1.13-1.41 across pairwise tax comparisons, N=80, 10 seeds, Bonferroni-corrected'
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: 'Tax-induced welfare decline at scale: d=0.51-1.18 across 18 pairwise tax comparisons, N=700, 100 seeds, Bonferroni-corrected'
  weakening:
  - run: 20260214-113750_kernel_v4_code_sweep
    metric: welfare
    detail: "Welfare INCREASES with tax in kernel v4 code scenario (12.18→16.96, 0%→15%), contradicting universal governance cost. N=5 seeds, underpowered"
  - run: 20260217_memori_study
    metric: welfare
    detail: "No governance sensitivity in LLM memori agents (d<0.23, 0/12 tests sig). Governance imposes pure overhead in all-honest LLM population. N=5 seeds, 2 epochs"
  boundary_conditions:
  - GasTown workspace, 7 agents, 30 epochs, full governance stack
  - Kernel v4 code scenario shows welfare INCREASE under tax — paradox may be scenario-specific
  - Memori LLM scenario shows zero governance response — cost is pure overhead with no adversarial behavior to deter
sensitivity:
  topology: Tested on GasTown small-world only; unknown whether hub-and-spoke or ring
    topologies amplify or dampen the cost
  agent_count: 7 agents; cost-per-agent may scale non-linearly with larger populations
  scenario: Paradox confirmed in GasTown and baseline governance; direction reversal in kernel v4 narrows universality
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-quality-gate-dominates
- claim-memory-promotion-gate
- claim-tax-disproportionately-punishes-rlm-agents
- claim-high-tax-increases-toxicity
- claim-collusion-penalty-has-no-economic-effect
- claim-tax-and-penalty-effects-are-orthogonal
- claim-tax-welfare-direction-is-scenario-dependent
- claim-cb-tax-interaction-non-monotonic-in-kernel-v4
- claim-memori-agents-show-no-governance-sensitivity
- claim-captcha-difficulty-and-collusion-penalty-have-no-governance-effect
- claim-freeze-duration-and-violation-threshold-interact-on-welfare
- claim-reputation-decay-rate-improves-welfare
- claim-full-governance-reduces-welfare-in-concordia
- claim-graduated-defense-reduces-damage-monotonically
- claim-full-governance-stack-prevents-most-attack-types
created: 2026-02-19
updated: 2026-02-21
aliases:
- governance-cost-paradox
- full-governance-stacks-impose-larger-welfare
cssclasses:
- claim
- claim-medium
tags:
- governance
- welfare
- cost-benefit
- gastown
graph-group: claim
---

# Full governance stacks impose larger welfare costs than toxicity reduction benefits at all adversarial levels tested

The full governance stack — comprising transaction taxes, circuit breakers, collusion penalties, and reputation decay — imposes welfare costs that exceed the toxicity reduction benefits at every adversarial penetration level tested (0%, 10%, 20%, 30%).

**Evidence summary.** In the GasTown composition study (N=42 runs, 7 agents, 30 epochs), the fully governed regime produced a welfare penalty of -215.9 at 0% adversarial penetration, representing a 58% reduction relative to the ungoverned baseline. As adversarial penetration increased, the governance stack did reduce toxicity, but the marginal welfare cost of each unit of toxicity reduction remained net-negative across all tested levels.

**Boundary conditions.** This result is established only for the GasTown workspace with 7 agents and 30-epoch horizons. The full governance stack was applied as a monolithic bundle; individual mechanism contributions are decomposed in related claims (see `claim-quality-gate-dominates`, `claim-tax-welfare-tradeoff`). It is unknown whether longer horizons would allow reputation effects to eventually offset the welfare penalty.

**Open questions.**
- Does the paradox hold under partial governance stacks (e.g., tax + quality gate only)?
- Is there a population threshold above which governance overhead amortizes?
- How does the welfare penalty interact with redistribution mechanisms?
- Does the paradox generalize beyond baseline governance scenarios, given the kernel v4 reversal?

## Update history

**2026-02-20** — backward-pass update:
- Added weakening evidence from [[20260214-113750_kernel_v4_code_sweep]]: welfare increases with tax in kernel v4 code scenario, contradicting universal governance cost. Underpowered (N=5 seeds).
- Added weakening evidence from [[20260217_memori_study]]: zero governance sensitivity in LLM memori agents. Governance imposes pure overhead in all-honest population. Underpowered (N=5 seeds, 2 epochs).
- Added boundary conditions noting scenario-dependence of the paradox per [[claim-tax-welfare-direction-is-scenario-dependent]].
- Added related claims: claim-tax-welfare-direction-is-scenario-dependent, claim-cb-tax-interaction-non-monotonic-in-kernel-v4, claim-memori-agents-show-no-governance-sensitivity.
- Confidence remains **high** for the GasTown/baseline governance context (Bonferroni-significant, multi-run replication). Weakening evidence is underpowered and does not yet challenge the core finding within its established boundary.

## Lifecycle audit

**2026-02-19** — automated claim-lifecycle audit:
- (Note: 22 bulk-added tax-rate evidence entries consolidated 2026-02-20 into 2 representative entries per source run)
- Upgraded confidence: medium -> high

<!-- topics: governance, welfare, cost-benefit, gastown -->
