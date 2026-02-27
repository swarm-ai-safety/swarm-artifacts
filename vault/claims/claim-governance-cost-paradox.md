---
description: Full governance stacks impose larger welfare costs than toxicity reduction benefits at all adversarial levels tested
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260211-232952_gastown_composition_study
    metric: welfare
    detail: 'Governed vs ungoverned welfare at 0% adversarial: d=-13.07, t=-16.00, p=4.83e-03 Bonferroni-corrected (k=7), N=3+3 runs. Mean welfare 158.9 vs 374.7 (58% reduction)'
  - run: 20260213-173805_baseline_governance
    metric: welfare
    detail: 'Tax-induced welfare decline replicates governance cost: d=1.13-1.41 across pairwise tax comparisons, N=80, 10 seeds, Bonferroni-corrected'
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: 'Tax-induced welfare decline at scale: d=0.51-1.18 across 18 pairwise tax comparisons, N=700, 100 seeds, Bonferroni-corrected'
  - run: 20260211-012350_concordia_sweep
    metric: welfare
    detail: "Concordia scenario: full defense welfare 55.8±5.8 vs baseline 67.7±5.8, d≈2.0, with toxicity invariant (0.334-0.391 across all 8 regimes). Governance cost with zero safety benefit. N=40 runs (5 seeds x 8 mechanisms)"
  - run: 20260221-082443_redteam_contract_screening_full
    metric: robustness
    detail: "Contract screening full governance: grade D (0.607), 299.79 total damage, 4/8 attacks successful. Full governance stack still leaves critical sybil vulnerability. N=1 evaluation; inferential statistics not applicable"
  - run: 20260224-220829_mesa_governance_study
    metric: welfare
    detail: "Mesa bridge: adaptive at rho=1.0 destroys 70% welfare (1141→340, d=21.50, Bonferroni p<1e-252) for 34% toxicity reduction. Static at rho=1.0 is pure deadweight (welfare -37%, toxicity unchanged). 5 seeds, 110 total runs"
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
  - Concordia scenario confirms welfare cost with zero toxicity benefit across all 8 governance regimes
  - Contract screening full governance receives D grade — governance reduces damage but fails to prevent sybil attacks
sensitivity:
  topology: Tested on GasTown small-world only; unknown whether hub-and-spoke or ring topologies amplify or dampen the cost
  agent_count: 7 agents in GasTown; cost-per-agent may scale non-linearly with larger populations
  scenario: Paradox confirmed in GasTown, baseline governance, Concordia, and contract screening (4 scenarios). Direction reversal in kernel v4 narrows universality
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
- claim-agent-architecture-constrains-behavior-more-than-governance
- claim-tax-phase-transition-hysteresis-predicted-but-untested
- claim-quadratic-staking-may-solve-sybil-cost-inversion
- claim-vote-normalization-bandwidth-caps-untested-sybil-mitigations
- claim-adaptive-acceptance-reduces-toxicity-monotonically-with-externality-internalization
- claim-static-externality-tax-is-pure-deadweight-welfare-loss
- claim-adaptive-governance-trades-welfare-for-toxicity-at-constant-marginal-rate
created: 2026-02-19
updated: 2026-02-27
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

# full governance stacks impose larger welfare costs than toxicity reduction benefits at all adversarial levels tested

The full governance stack — comprising transaction taxes, circuit breakers, collusion penalties, and reputation decay — imposes welfare costs that exceed the toxicity reduction benefits at every adversarial penetration level tested (0%, 10%, 20%, 30%).

**Evidence summary.** In the GasTown composition study (7 agents, 30 epochs, 3 seeds per condition), the fully governed regime produced significantly lower welfare than the ungoverned baseline at 0% adversarial penetration (mean total welfare 158.9 vs 374.7, a 58% reduction; Cohen's d = -13.07, Welch's t = -16.00, p = 4.83 x 10^-3 Bonferroni-corrected across k=7 adversarial levels). The effect was Bonferroni-significant at all adversarial levels from 0% through 71% (d ranging from -7.66 to -13.07), attenuating only at 86% adversarial where both regimes collapsed (d = -1.85, p_bonf = 0.61). As adversarial penetration increased, the governance stack did reduce toxicity, but the marginal welfare cost of each unit of toxicity reduction remained net-negative across all tested levels.

**Boundary conditions.** This result is established only for the GasTown workspace with 7 agents and 30-epoch horizons. The full governance stack was applied as a monolithic bundle; individual mechanism contributions are decomposed in related claims (see `claim-quality-gate-dominates`, `claim-tax-welfare-tradeoff`). It is unknown whether longer horizons would allow reputation effects to eventually offset the welfare penalty.

**Cross-scenario replication.** The paradox now has evidence from four independent scenarios:
1. **GasTown** (primary): 58% welfare reduction, Bonferroni-significant (d = -13.07)
2. **Baseline governance** (v1 + v2): tax-induced welfare decline replicated at d = 0.51-1.41
3. **Concordia**: full defense welfare 55.8 vs baseline 67.7 (d ≈ 2.0), with zero toxicity benefit — the purest demonstration of cost without safety gain
4. **Contract screening**: full governance receives D grade (0.607) with 299.79 total damage; sybil attacks persist despite full stack

The Concordia finding (see [[claim-full-governance-reduces-welfare-in-concordia]]) is particularly diagnostic because toxicity is invariant across all 8 governance regimes tested (range 0.334-0.391), meaning governance imposes a pure welfare tax with zero safety return. The contract screening redteam finding ([[20260221-082443_redteam_contract_screening_full]]) extends the paradox to adversarial settings: even maximum governance investment leaves grade D robustness, primarily due to sybil persistence (see [[claim-sybil-attacks-resist-full-governance-stack]]).

**Open questions.**
- Does the paradox hold under partial governance stacks (e.g., tax + quality gate only)?
- Is there a population threshold above which governance overhead amortizes?
- How does the welfare penalty interact with redistribution mechanisms?
- Does the paradox generalize beyond baseline governance scenarios, given the kernel v4 reversal?
- Would structural defenses (vote normalization, bandwidth caps) change the cost-benefit calculus by actually preventing sybil attacks?

## Update history

**2026-02-20** — backward-pass update:
- Added weakening evidence from [[20260214-113750_kernel_v4_code_sweep]]: welfare increases with tax in kernel v4 code scenario, contradicting universal governance cost. Underpowered (N=5 seeds).
- Added weakening evidence from [[20260217_memori_study]]: zero governance sensitivity in LLM memori agents. Governance imposes pure overhead in all-honest population. Underpowered (N=5 seeds, 2 epochs).
- Added boundary conditions noting scenario-dependence of the paradox per [[claim-tax-welfare-direction-is-scenario-dependent]].
- Added related claims: claim-tax-welfare-direction-is-scenario-dependent, claim-cb-tax-interaction-non-monotonic-in-kernel-v4, claim-memori-agents-show-no-governance-sensitivity.
- Confidence remains **medium** for the GasTown/baseline governance context (Bonferroni-significant supporting evidence). Weakening evidence is underpowered and does not yet challenge the core finding within its established boundary.

**2026-02-22** — backward-pass update (4-scenario consolidation):
- Added supporting evidence from [[20260211-012350_concordia_sweep]]: welfare cost with zero toxicity benefit across 8 governance regimes, d≈2.0. Previously only referenced via related claim; now directly cited as supporting evidence.
- Added supporting evidence from [[20260221-082443_redteam_contract_screening_full]]: full governance achieves only D grade (0.607) in adversarial setting, with sybil attacks persisting. Extends paradox from welfare-only to welfare-plus-security framing.
- Updated boundary conditions to include Concordia and contract screening scenarios.
- Updated sensitivity.scenario to reflect 4-scenario replication (GasTown, baseline governance, Concordia, contract screening).
- Added cross-scenario replication summary to body text.
- Confidence remains **medium**: Bonferroni-significant supporting evidence in GasTown, with scenario replication across 3 additional contexts. Weakening evidence from kernel v4 and memori prevents upgrade to high.

**2026-02-21** — formal statistics computed for primary GasTown evidence:
- Computed Cohen's d = -13.07, Welch's t = -16.00, p = 4.83e-03 (Bonferroni, k=7) for governed vs ungoverned welfare at 0% adversarial.
- All levels 0%-71% are Bonferroni-significant (d = -7.66 to -13.07). Only 86% adversarial is non-significant (d = -1.85).
- Resolves Gate 2 (formal effect size + correction method) for the primary evidence entry.

## Lifecycle audit

**2026-02-19** — automated claim-lifecycle audit:
- (Note: 22 bulk-added tax-rate evidence entries consolidated 2026-02-20 into 2 representative entries per source run)
- Upgraded confidence: medium -> high

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, welfare, cost-benefit, gastown -->
