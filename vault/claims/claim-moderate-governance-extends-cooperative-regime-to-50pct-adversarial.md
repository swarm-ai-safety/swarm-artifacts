---
description: Moderate governance (CB+audit) maintains cooperative regime up to 50% adversarial fraction where none/basic collapse at 15-20%
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260227_203024_composition_boundary_study
    metric: regime
    detail: "Phase 1 adversarial sweep: 9 fractions x 4 governance x 4 pop sizes x 5 seeds = 720 runs. Moderate governance stays cooperative through 37.5% adversarial (0% collapse) and cooperative at 50% (5% collapse). None/basic transition to contested at 20%/15% respectively. Regime classification by modal outcome across seeds"
  - run: 20260227_203024_composition_boundary_study
    metric: acceptance
    detail: "Moderate acceptance at 50% adversarial: 0.763 (vs none 0.525, basic 0.502). Acceptance delta moderate-vs-none at 50% adv: +0.238. At 37.5%: moderate 0.855 vs none 0.648 (+0.207). 20 runs per cell"
  weakening: []
  boundary_conditions:
  - "Tested with honest-vs-adversarial binary mixtures only; untested with deceptive or opportunistic agents in the adversarial sweep"
  - "Population sizes 4-32; scaling behavior beyond 32 unknown"
  - "20 epochs, 5 seeds per cell; longer horizons may shift boundaries"
  - "No critical fraction (majority collapse) reached in any config up to 50% adversarial"
sensitivity:
  topology: untested — default topology only
  agent_count: tested at 4, 8, 16, 32 agents across all conditions
  governance_interaction: "Moderate = CB + 8% tax + audit(p=0.1, 2x penalty). Basic = CB + 5% tax. Full adds staking + collusion detection + 12% tax"
supersedes: []
superseded_by: []
related_claims:
- claim: claim-governance-cost-paradox
  relation: refines
- claim: claim-full-governance-stack-prevents-most-attack-types
  relation: extends
- claim: claim-governance-parameters-have-narrow-safe-operating-envelopes
  relation: supports
- claim: claim-circuit-breakers-dominate
  relation: refines
- claim: claim-graduated-defense-reduces-damage-monotonically
  relation: supports
created: 2026-02-28
aliases:
- moderate-governance-extends-cooperative-regime
cssclasses:
- claim
- claim-medium
tags:
- governance
- composition
- adversarial
- regime-boundary
graph-group: claim
---

# Moderate governance extends the cooperative regime boundary to 50% adversarial fraction

## Evidence summary

The composition boundary study ([[20260227_203024_composition_boundary_study]]) swept 9 adversarial fractions (0-50%) across 4 governance configurations and 4 population sizes with 5 seeds each (720 total runs in the adversarial sweep alone).

The regime heatmap reveals a dramatic governance-dependent boundary shift:

| Adv fraction | None | Basic (CB) | Moderate (CB+audit) | Full (CB+audit+stake+collusion) |
|-------------|------|-----------|--------------------|---------------------------------|
| 0-10% | cooperative | cooperative | cooperative | cooperative |
| 15% | cooperative | contested | cooperative | cooperative |
| 20% | contested | contested | cooperative | cooperative |
| 25-30% | contested | contested | cooperative | cooperative |
| 37.5% | contested | contested | cooperative | cooperative |
| 50% | contested | contested | cooperative (5% collapse) | contested (5% collapse) |

Moderate governance maintains the cooperative regime through 50% adversarial penetration (only 5% collapse rate), while none/basic governance transitions to contested by 15-20% adversarial. This represents a roughly 2.5-3x extension of the safe operating boundary.

The acceptance rate data quantifies the separation: at 50% adversarial, moderate governance achieves 0.763 acceptance rate versus 0.525 (none) and 0.502 (basic). The welfare-toxicity tradeoff plot confirms moderate governance Pareto-dominates none and basic at high adversarial fractions.

No critical adversarial fraction (majority-collapse threshold) was reached in any governance configuration up to 50% adversarial — the system degrades gradually rather than collapsing suddenly, which is consistent with the [[claim-governance-parameters-have-narrow-safe-operating-envelopes|narrow envelope]] pattern applying to population composition rather than governance parameters.

**Confidence: medium.** Single study with 20 runs per cell (5 seeds x 4 population sizes), providing adequate within-cell replication. No formal statistical testing of regime classification proportions across conditions. Replication in independent scenarios needed for high confidence.

## Mechanism

Moderate governance adds audit probability (p=0.1) with 2x penalty multiplier on top of circuit breakers. This creates a dual deterrence mechanism: CB handles behavioral threshold violations while stochastic auditing imposes expected costs on adversarial strategies that evade CB detection. The audit probability is high enough to create meaningful expected penalty without being so aggressive that it causes false-positive welfare destruction. This explains why moderate outperforms both basic (no audit deterrent) and full (12% tax + staking overhead crushes baseline welfare).

## Open questions

- What is the actual critical adversarial fraction under moderate governance? Sweeping 50-75% would determine if there is a cliff.
- Does the boundary hold with mixed adversarial strategies (deceptive + adversarial) rather than pure adversarial?
- Would adaptive audit probability (increasing with detected adversarial signals) extend the boundary further?
- Is the moderate governance advantage scenario-dependent, as tax welfare direction is for other scenarios?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, composition, adversarial, regime-boundary -->
