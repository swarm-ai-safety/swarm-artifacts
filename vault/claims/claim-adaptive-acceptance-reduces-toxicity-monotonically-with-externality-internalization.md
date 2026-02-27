---
description: Adaptive acceptance thresholds linearly reduce toxicity (r=-0.90, 34% reduction at full internalization) with Bonferroni-significant effects
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260224-220829_mesa_governance_study
    metric: toxicity
    detail: "Pearson r=-0.90 (N=55 adaptive runs), R²=0.81. rho=0 vs rho=1: d=12.22, p<1e-82, Bonferroni-corrected (k=4). Toxicity 0.237→0.157 (-33.8%). 5 seeds per condition"
  weakening: []
  boundary_conditions:
  - Mesa bridge scenario only — agents have fixed archetype probabilities (cooperative 0.79, selfish 0.41, exploitative 0.32)
  - Adaptive threshold formula: 0.5 + 0.3 * rho_a — specific to this acceptance function
  - 50 timesteps, 5 seeds per condition, 1500 interactions per run
  - Unknown whether the linear relationship holds in scenarios with adaptive agents (non-mesa objectives)
sensitivity:
  topology: untested beyond mesa bridge default
  agent_count: untested beyond default count
  governance_interaction: rho_a is the only governance parameter varied — interaction with taxes, circuit breakers untested
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-governance-cost-paradox
- claim-static-externality-tax-is-pure-deadweight-welfare-loss
- claim-mesa-agent-objectives-are-invariant-to-governance-regime
- claim-adaptive-governance-trades-welfare-for-toxicity-at-constant-marginal-rate
- claim-high-tax-increases-toxicity
created: 2026-02-27
updated: 2026-02-27
aliases:
- adaptive-acceptance-toxicity
cssclasses:
- claim
- claim-medium
graph-group: claim
---

# adaptive acceptance thresholds reduce toxicity monotonically as externality internalization increases

## Evidence summary

In the mesa bridge governance study ([[mesa_governance_study]]), adaptive acceptance thresholds that scale with externality internalization (rho_a) produce a monotonic, strongly linear reduction in toxicity (Pearson r = -0.90, R² = 0.81 across 55 runs). At rho_a = 0.0 (no internalization), toxicity is 0.237; at rho_a = 1.0 (full internalization), toxicity drops to 0.157, a 33.8% reduction. This effect is Bonferroni-significant (d = 12.22, p < 1e-82, Bonferroni k=4 metrics) comparing rho=0 to rho=1.

The mechanism is filtering, not behavioral change: the adaptive threshold (0.5 + 0.3 * rho_a) progressively rejects lower-quality interactions. Agent archetype probabilities remain constant across all conditions (see [[claim-mesa-agent-objectives-are-invariant-to-governance-regime]]), confirming that the toxicity reduction comes from selective acceptance rather than agent adaptation.

At a moderate operating point (rho=0.5), adaptive governance achieves significantly lower toxicity than static governance (d = -3.26, Bonferroni p = 1.0e-06) with no significant welfare penalty (d = -0.98, p = 0.48).

## Boundary conditions

- Only tested in mesa bridge scenario with fixed agent archetypes
- Adaptive threshold is a specific linear function of rho — other acceptance functions may produce different toxicity profiles
- The monotonic relationship may not hold if agents can adapt their strategies in response to governance (non-mesa case)
- 5 seeds per condition — sufficient for the very large effect sizes observed, but replication with more seeds would strengthen confidence

## Mechanism

The adaptive acceptance threshold rises with rho_a, making the governance mechanism increasingly selective about which interactions to permit. Because exploitative and selfish agents produce lower-quality interactions (p = 0.32 and 0.41 respectively vs cooperative p = 0.79), they are disproportionately rejected at higher rho values. This differential filtering reduces toxicity (the fraction of accepted interactions that are low-quality) without requiring any behavioral change from the agents.

## Open questions

- Does the linear r=-0.90 relationship hold for non-linear acceptance functions?
- What happens when agents can adapt their strategies in response to governance (undermining the mesa invariance property)?
- Is there a minimum rho at which the toxicity reduction becomes practically meaningful for safety guarantees?
- Would combining adaptive acceptance with other governance mechanisms (taxes, circuit breakers) produce super-additive toxicity reduction?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: mesa, governance, externality-internalization, toxicity, adaptive-acceptance -->
