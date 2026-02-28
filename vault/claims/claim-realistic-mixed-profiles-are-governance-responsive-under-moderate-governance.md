---
description: Realistic mixed populations (55% honest, 25% opportunistic, 12% deceptive, 8% adversarial) achieve near-pure-honest outcomes under moderate governance
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260227_203024_composition_boundary_study
    metric: acceptance
    detail: "Phase 2 profile sweep (N=16 pop, 5 seeds per cell). Realistic mix under moderate governance: acceptance 0.964 vs pure_honest 1.000. Under none: acceptance 0.885 vs pure_honest 1.000. Moderate governance closes 71% of the acceptance gap between realistic_mix and pure_honest"
  - run: 20260227_203024_composition_boundary_study
    metric: welfare
    detail: "Realistic mix under moderate governance: welfare 16.07 vs pure_honest 18.79 (86% of pure honest). Under none: welfare 17.70 vs pure_honest 22.71 (78% of pure honest). Moderate governance improves the realistic_mix welfare ratio from 78% to 86% of the pure-honest ceiling"
  - run: 20260227_203024_composition_boundary_study
    metric: toxicity
    detail: "Realistic mix under moderate governance: toxicity 0.312 vs under none: 0.334. Quality gap under moderate: 0.071 vs under none: 0.129 (45% reduction). Moderate governance halves the quality gap in realistic mixed populations"
  - run: 20260227_203024_composition_boundary_study
    metric: regime
    detail: "All 6 profile mixtures maintain cooperative regime under moderate governance, including high_threat (30% honest, 20% opportunistic, 20% deceptive, 30% adversarial) which is contested under none and basic. 5 seeds per cell"
  weakening: []
  boundary_conditions:
  - "Phase 2 profile sweep at fixed population size N=16; untested at other sizes"
  - "5 seeds per profile-governance combination; underpowered for formal testing"
  - "Realistic mix composition is a specific ratio (55/25/12/8); sensitivity to mixture ratios untested"
  - "20 epochs; opportunistic behavior may evolve over longer horizons"
sensitivity:
  topology: untested
  agent_count: tested at N=16 only
  governance_interaction: "Moderate governance uniquely effective for mixed profiles; full governance achieves similar regime protection but at lower welfare"
supersedes: []
superseded_by: []
related_claims:
- claim: claim-moderate-governance-extends-cooperative-regime-to-50pct-adversarial
  relation: supports
- claim: claim-tax-hurts-honest-more-than-opportunistic
  relation: extends
- claim: claim-contract-screening-achieves-perfect-type-separation
  relation: extends
- claim: claim-agent-architecture-constrains-behavior-more-than-governance
  relation: refines
created: 2026-02-28
aliases:
- realistic-mixed-profiles-governance-responsive
cssclasses:
- claim
- claim-low
tags:
- governance
- composition
- agent-behavior
- mixed-profiles
graph-group: claim
---

# Realistic mixed populations achieve near-pure-honest outcomes under moderate governance

## Evidence summary

The composition boundary study Phase 2 ([[20260227_203024_composition_boundary_study]]) tested 6 agent profile mixtures across 4 governance configurations at N=16 with 5 seeds each (120 total runs).

The "realistic_mix" profile (55% honest, 25% opportunistic, 12% deceptive, 8% adversarial) shows strong governance responsiveness under moderate governance:

| Metric | No governance | Moderate | Pure honest (moderate) |
|--------|-------------|----------|----------------------|
| Acceptance | 0.885 | 0.964 | 1.000 |
| Toxicity | 0.334 | 0.312 | 0.251 |
| Quality gap | 0.129 | 0.071 | 0.000 |
| Welfare | 17.70 | 16.07 | 18.79 |
| Regime | cooperative | cooperative | cooperative |

Moderate governance closes 71% of the acceptance gap and 45% of the quality gap between realistic_mix and pure_honest populations. This suggests that the opportunistic and deceptive agents in the mixture are governance-responsive — they shift toward honest-like behavior when audit mechanisms create sufficient expected costs for exploitation.

The most dramatic finding is with the "high_threat" profile (30% honest, 20% opportunistic, 20% deceptive, 30% adversarial). Under no governance and basic governance, this profile produces a contested regime. Under moderate governance, it achieves cooperative regime with 0.829 acceptance rate, demonstrating that moderate governance can stabilize even highly adversarial populations.

This refines [[claim-agent-architecture-constrains-behavior-more-than-governance]] — while agent architecture constrains behavior in homogeneous populations, governance modulates behavior in heterogeneous populations where agent types respond differently to incentives.

**Confidence: low.** Only 5 seeds per cell, N=16 population, single study. No formal statistical testing between governance conditions for profile mixtures. Key for generating hypotheses, but underpowered for strong conclusions.

## Mechanism

Opportunistic agents respond to expected payoff calculations. Under no governance, exploitation is costless and opportunistic agents behave adversarially when profitable. Moderate governance introduces audit risk (10% probability, 2x penalty) that shifts the expected payoff of exploitation below the expected payoff of cooperation for opportunistic agents. Deceptive agents may also be partially deterred by the quality gap detection implicit in the audit mechanism. The 8% adversarial fraction in the realistic mix is below the regime transition boundary (~15-20% under no governance), so the remaining adversarial agents cannot destabilize the system after opportunistic agents have been converted to cooperative behavior.

## Open questions

- At what audit probability does the opportunistic conversion saturate? Is 10% already near optimal?
- Do deceptive agents genuinely cooperate under moderate governance, or do they merely evade detection?
- Would a longer horizon (50+ epochs) allow deceptive agents to learn audit patterns and revert to exploitation?
- Is the realistic mix composition (55/25/12/8) representative of actual multi-agent deployment scenarios?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, composition, agent-behavior, mixed-profiles -->
