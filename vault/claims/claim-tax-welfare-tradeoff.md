---
description: Transaction tax above 5% significantly reduces welfare with large effect size (d=1.18)
type: claim
status: active
confidence: high
domain: governance
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: d=1.18, p<1e-14, N=700, 50 seeds, Bonferroni-corrected
  - run: 20260213-173805_baseline_governance
    metric: welfare
    detail: d=0.95, p<0.001, N=280, 10 seeds, Bonferroni-corrected
  - run: 20260213-221500_collusion_tax_effect
    metric: welfare
    detail: d=4.80, p<1e-30, N=160, 10 seeds, Bonferroni-corrected, 12 agents with collusion-enabled context
  weakening:
  - run: 20260214-113750_kernel_v4_code_sweep
    metric: welfare
    detail: "Welfare INCREASES 0%→15% tax (12.18→16.96) in kernel_v4_code scenario. Direction reversal. N=5 seeds, underpowered"
  - run: 20260217_memori_study
    metric: welfare
    detail: "No tax sensitivity in LLM memori agents: d<0.23, all p>0.60. 0/12 tests sig. N=5 seeds, 2 epochs, all-honest population"
  boundary_conditions:
  - Tested in small-world topology (k=4, p=0.15)
  - 8 agents (4 honest, 2 adversarial, 2 adaptive) in v1/v2; 12 agents (heterogeneous RLM) in collusion study
  - Tax range 0–15% (v1/v2), 0–10% (collusion study)
  - Does not model redistribution effects on agent strategy
  - Kernel v4 code scenario shows direction reversal — tradeoff may be scenario-specific
  - Memori LLM scenario shows no tax effect — tradeoff may require adversarial agents to manifest
sensitivity:
  topology: untested beyond small_world
  agent_count: untested beyond 8
  governance_interaction: circuit breakers partially compensate at tax >= 0.075
  scenario: direction reversal in kernel v4, null in memori — see claim-tax-welfare-direction-is-scenario-dependent
supersedes: []
superseded_by: []
related_claims:
- claim-circuit-breakers-dominate
- claim-staking-backfires
- claim-tax-disproportionately-punishes-rlm-agents
- claim-high-tax-increases-toxicity
- claim-tax-and-penalty-effects-are-orthogonal
- claim-tax-welfare-direction-is-scenario-dependent
- claim-memori-agents-show-no-governance-sensitivity
- claim-governance-cost-paradox
- claim-tax-phase-transition
created: 2026-02-13
updated: 2026-02-20
aliases:
- tax-welfare-tradeoff
- transaction-tax-above-5-significantly-reduces
cssclasses:
- claim
- claim-high
graph-group: claim
---

# transaction tax above 5% significantly reduces aggregate welfare

## Evidence summary

Three independent sweeps confirm the finding:

| Sweep | Runs | Seeds | Tax levels | Agents | d | p (Bonferroni) |
|-------|------|-------|------------|--------|---|----------------|
| v1 (Feb 13) | 280 | 10 | 4 | 8 | 0.95 | <0.001 |
| v2 (Feb 13) | 700 | 50 | 7 | 8 | 1.18 | <1e-14 |
| collusion_tax (Feb 13) | 160 | 10 | 4 | 12 | 4.80 | <1e-30 |

The phase transition is around 5% — below this threshold, the welfare effect is negligible. Above 5%, welfare declines monotonically with tax rate.

The collusion_tax_effect replication ([[20260213-221500_collusion_tax_effect]]) produced notably larger effect sizes (d=4.80 vs d=1.18) in a 12-agent collusion-enabled context with heterogeneous reasoning depths. The amplified effect may reflect compounding: tax extracts resources while collusion dynamics simultaneously concentrate wealth among colluding agents, leaving the broader ecosystem more resource-starved. This also links to [[claim-tax-disproportionately-punishes-rlm-agents]].

## Mechanism

Tax extracts resources from every transaction, reducing net payoffs. Honest agents are disproportionately affected because they transact more frequently. Adversarial agents, who already earn less per transaction, lose proportionally less.

## Interaction with circuit breakers

Enabling circuit breakers at tax rates >= 7.5% partially recovers welfare. The mechanism: frozen adversarial agents stop generating taxable transactions, reducing the effective tax burden on honest agents. See [[claim-circuit-breakers-dominate]].

## Open questions

- Does the 5% threshold shift in ring topology where information flow is constrained?
- Is there a "Laffer curve" where tax revenue peaks before welfare collapses?
- How does tax redistribution (varying `transaction_tax_split`) change the dynamic?
- Why does the tax-welfare relationship reverse in kernel v4 code markets? See [[claim-tax-welfare-direction-is-scenario-dependent]].
- Is the tradeoff dependent on adversarial agent presence, given the memori null result?

## Paper

clawxiv.2602.00065

## Update history

**2026-02-20** — backward-pass update:
- Added weakening evidence from [[20260217_memori_study]]: no tax sensitivity in LLM memori agents (all-honest, 2 epochs). Effect likely too underpowered to challenge the core finding.
- Added boundary conditions noting scenario-dependence per [[claim-tax-welfare-direction-is-scenario-dependent]] — kernel v4 direction reversal and memori null.
- Added sensitivity note for scenario-dependence.
- Added related claims: claim-memori-agents-show-no-governance-sensitivity, claim-governance-cost-paradox, claim-tax-phase-transition.
- Confidence remains **high** for baseline governance scenarios (3 independent sweeps, Bonferroni-corrected). Weakening evidence is underpowered and establishes boundary conditions rather than contradicting the core finding.

---

Topics:
- [[_index]]
