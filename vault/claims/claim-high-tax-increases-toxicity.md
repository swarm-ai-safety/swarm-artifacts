---
description: Transaction tax at 10% increases toxicity rate by 0.6pp (d=-0.86, Bonferroni-sig), a small but consistent effect
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: toxicity_rate
    detail: "10% vs 0% tax: toxicity 0.3403 vs 0.3346, d=-0.86, p=0.0004, N=80, Bonferroni-corrected"
  - run: 20260213-221500_collusion_tax_effect
    metric: toxicity_rate
    detail: "5% vs 10% tax: d=-0.57, BH-significant; 0% vs 5%: d=-0.69, BH-significant"
  - run: 20260210-213833_collusion_governance
    metric: toxicity_rate
    detail: "Tax 0% vs 15%: toxicity 0.336→0.347, d=-2.447, p=2.52e-09, Bonferroni-significant. N=10 seeds per config, rlm_recursive_collusion scenario. Replicates monotonic toxicity increase with larger effect size"
  weakening:
  - run: 20260213-202050_baseline_governance_v2
    metric: toxicity_rate
    detail: "2.5% vs 15% tax: d=-0.34, not BH-significant, N=200. Fails to replicate in 8-agent algorithmic population (vs 12-agent RLM population where d=-0.86)"
  boundary_conditions:
  - 12 agents, default topology, tax range 0-10%, 10 seeds
  - Collusion penalty active (0.5-2.0x) but orthogonal to tax-toxicity relationship
  - Absolute effect is small (~0.6 percentage points)
sensitivity:
  topology: untested beyond default
  agent_count: 12 agents; toxicity response may differ in larger populations
  governance_interaction: collusion penalty independently affects toxicity; combined effect may be super-additive
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-collusion-penalty-destabilizes
- claim-tax-phase-transition
- claim-governance-cost-paradox
- claim-tax-penalty-interaction-on-toxicity-uncharacterized
- claim-tax-and-penalty-effects-are-orthogonal
- claim-tax-disproportionately-punishes-rlm-agents
created: 2026-02-20
updated: 2026-02-21
aliases:
- high-tax-increases-toxicity
cssclasses:
- claim
- claim-medium
tags:
- governance
- transaction-tax
- toxicity
graph-group: claim
---

# high transaction tax increases ecosystem toxicity rate

## Evidence summary

In the [[20260213-221500_collusion_tax_effect]] sweep (160 runs), transaction tax at 10% vs 0% increases mean toxicity from 0.3346 to 0.3403 (d=-0.86, p=0.0004, Bonferroni-corrected, N=80). The effect is consistent across intermediate comparisons: 0% vs 5% (d=-0.69, BH-sig) and 5% vs 10% (d=-0.57, BH-sig), indicating a monotonic toxicity increase with tax rate.

This creates a governance dilemma: transaction tax reduces welfare ([[claim-tax-welfare-tradeoff]]) AND increases toxicity, meaning it fails on both economic and safety dimensions at high rates. The dual failure strengthens [[claim-governance-cost-paradox]] by adding a safety cost dimension beyond the already-established welfare cost.

## Mechanism

Resource scarcity induced by high taxation may force agents into more competitive, lower-quality interactions. When legitimate transaction returns decline, agents shift toward strategies that extract short-term value at the cost of ecosystem quality. This parallels how [[claim-collusion-penalty-destabilizes]] shows punitive governance measures backfiring on toxicity — both tax and penalty produce the same paradoxical safety degradation through different economic channels. This shared pattern of "governance-induced toxicity" is a recurring motif: mechanisms designed to constrain harmful behavior instead redirecting agents toward different harmful behaviors.

## Weakening evidence

The [[20260213-202050_baseline_governance_v2]] sweep (700 runs, 8 agents, 50 seeds) **fails to replicate** the tax-toxicity effect: 2.5% vs 15% tax shows d=-0.34, not BH-significant. The key difference is agent composition: the v2 sweep uses 8 algorithmic agents (4 honest, 2 adversarial, 2 adaptive) while the collusion study uses 12 heterogeneous RLM agents. This suggests the tax-toxicity effect may be specific to collusion-enabled populations with RLM agents, not a universal property of transaction tax.

## Boundary conditions

- The absolute toxicity increase is small (~0.6pp), though statistically robust in the collusion context
- **Replication failure** in 8-agent algorithmic population narrows the boundary: effect may require RLM agents or active collusion dynamics
- No redistribution modeled — returning tax revenue might offset the scarcity mechanism

## Open questions

- Is the tax-toxicity relationship linear or does it exhibit a phase transition like welfare? The [[claim-tax-phase-transition]] non-linearity in welfare may have a toxicity analogue.
- Does the toxicity increase come from specific agent types (RLM) or is it ecosystem-wide? If RLM-specific, this connects to [[claim-tax-disproportionately-punishes-rlm-agents]] — resource-starved RLM agents may become more toxic.
- Is there a tax x penalty interaction that produces super-additive toxicity at high levels of both? See [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]] for preliminary evidence.
- [[claim-tax-and-penalty-effects-are-orthogonal]] places tax-toxicity as the one cross-domain effect — is this a crack in the orthogonality, or a minor secondary effect?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: governance, transaction-tax, toxicity -->
