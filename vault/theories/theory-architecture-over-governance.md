---
description: Training architecture (RLHF, mesa, LDT, RLM) constrains agent behavior more than governance in homogeneous populations
type: theory
status: proposed
scope: "Homogeneous or near-homogeneous populations. LDT, RLM, RLHF, memori, mesa agent types. Breaks down in mixed adversarial+honest populations"

constituent_claims:
  - claim: "claim-agent-architecture-constrains-behavior-more-than-governance"
    role: premise
  - claim: "claim-rlhf-persona-invariant"
    role: evidence
  - claim: "claim-mesa-agent-objectives-are-invariant-to-governance-regime"
    role: evidence
  - claim: "claim-memori-agents-show-no-governance-sensitivity"
    role: evidence
  - claim: "claim-smarter-agents-earn-less"
    role: evidence
  - claim: "claim-acausality-depth-does-not-affect-cooperation-outcomes"
    role: evidence

open_predictions:
  - "prediction-diversity-threshold"

created: 2026-02-28
updated: 2026-02-28

_schema:
  required: [description, type, status, scope, constituent_claims, created]
  optional: [open_predictions, updated]
  enums:
    type: [theory]
    status: [proposed, supported, contested, superseded]
    role: [premise, prediction, boundary, evidence]
  constraints:
    description: "max 200 chars, states the theory as a proposition, no trailing period"
    constituent_claims: "minimum 2 entries, each with claim ID and role"
    scope: "must specify domain, topology, agent types, or other applicability conditions"
---

# Agent training architecture constrains behavior more fundamentally than governance mechanisms in homogeneous populations

## Constituent claims

| Claim | Role | Confidence |
|-------|------|------------|
| [[claim-agent-architecture-constrains-behavior-more-than-governance]] | premise | medium |
| [[claim-rlhf-persona-invariant]] | evidence | medium |
| [[claim-mesa-agent-objectives-are-invariant-to-governance-regime]] | evidence | medium |
| [[claim-memori-agents-show-no-governance-sensitivity]] | evidence | low |
| [[claim-smarter-agents-earn-less]] | evidence | high |
| [[claim-acausality-depth-does-not-affect-cooperation-outcomes]] | evidence | high |

## Scope & boundary conditions

**Agent architectures tested:**
- **LDT reasoners**: 0/105 Bonferroni-significant tests across 7 studies, 5 scenarios, 210 runs. Acausality depth (1-5) has zero effect on cooperation.
- **RLM agents**: deeper reasoning (depth 1-5) hurts payoff (r=-0.75, p<0.001, Holm-corrected). Architecture constrains to worse-than-honest outcomes.
- **RLHF-aligned LLMs**: behavior type (adversarial vs cooperative) dominates model identity and persona prompts. 0/19 Holm-significant model/persona tests.
- **Memori LLM agents**: 0/12 governance tests significant. Tax, circuit breakers, collusion detection all null (largest d=0.55, p=0.14).
- **Mesa-optimized agents**: cooperation/selfish/exploit probabilities (0.791/0.408/0.325) identically invariant across all 110 runs (2 regimes x 11 rho levels x 5 seeds). Zero variance.
- **LangGraph agents**: actual handoffs ~0.5 regardless of budget (5-30) across 128 runs. Delegation behavior is architectural, not governance-parametric.

**Critical boundary — mixed populations:**
This theory explicitly breaks down when adversarial agents are mixed with honest agents under strong economic governance. In the collusion tax study, tax has massive effects on RLM agents (d=4.80 welfare, d=6.02 RLM payoff). Architecture does not make agents immune to economic pressure when differential selection pressure exists between agent types. The theory applies only when population composition is homogeneous or near-homogeneous.

**Other boundary conditions:**
- Memori null may be artifact of all-honest population and 2-epoch horizon
- RLHF persona invariance based on N=18 episodes (underpowered)
- Topology variation untested

## Thesis

Across four distinct training paradigms — RLHF fine-tuning, mesa optimization, LDT acausal reasoning, and RLM recursive reasoning — the behavioral constraints imposed by training and architecture dominate governance parameters. The mechanism is **behavioral attractor formation**:

1. **Training creates robust attractors.** Each architecture converges to characteristic behavioral patterns that are stable under governance perturbation. RLHF models cooperate regardless of adversarial prompts. Mesa agents maintain fixed cooperation/selfish/exploit ratios across 110 governance configurations. LDT agents ignore reasoning depth. RLM agents are trapped in depth-dependent payoff decline.

2. **Governance signals are too weak to perturb attractors.** In homogeneous populations, governance mechanisms (tax, circuit breakers, collusion detection) create selection pressure. But when all agents occupy similar attractors, there is no differential to exploit — every agent is equally affected, preserving relative standings. The governance signal is absorbed without behavioral change.

3. **Mixed populations break the symmetry.** When architecturally different agents coexist (e.g., honest + adversarial), governance creates differential selection pressure that separates agent types economically. Tax that merely extracts welfare from homogeneous populations becomes a type-separation mechanism in heterogeneous ones.

This has a fundamental implication for governance design: **the relevant design variable is expected population composition, not governance parameter tuning.** In well-aligned homogeneous populations, any governance is overhead. In adversarial-mixed populations, moderate governance suffices (per [[theory-governance-cost-universality]]).

## Predictions

1. **Population diversity threshold.** There exists a critical fraction of "different" agents (different architecture or alignment) below which governance has null effect and above which governance effects become significant. Estimate: 10-20% minority fraction, based on the composition boundary study showing governance effects emerge between 0% and 25% adversarial.

2. **Architecture-specific governance sensitivity.** If governance signals are absorbed differently by different architectures, then in mixed populations, the same governance configuration should produce architecture-specific effect sizes. Tax should hurt RLM agents more than RLHF agents more than LDT agents. This is partially supported by [[claim-tax-disproportionately-punishes-rlm-agents]] but needs systematic multi-architecture comparison.

3. **Scaling prediction.** If attractors are training-determined, then increasing agent complexity (more parameters, more reasoning depth) should NOT increase governance sensitivity. The memori null (LLM agents ignoring governance) and LDT null (deeper reasoning having no effect) support this, but need replication at larger scales.

4. **Transfer across governance types.** The architecture dominance should hold for novel governance mechanisms not yet tested — e.g., quadratic staking, vote normalization, bandwidth caps. If the theory is correct, these mechanisms will also be null in homogeneous aligned populations.

## Falsification criteria

This theory would be **falsified** if:
- A governance mechanism is found that reliably changes behavior in a homogeneous, well-aligned population (effect size d≥0.5, replicated across ≥2 independent runs with N≥20 seeds)
- Mesa agents show governance sensitivity at longer horizons (>5 seeds, >10 rho levels) — the current zero-variance result could be an artifact of short runs
- LLM agents (memori or similar) show governance response when run for ≥10 epochs with ≥20 seeds — the current null could be underpowered
- Increasing population size fundamentally changes the architecture-governance balance in homogeneous populations (e.g., at N=100, governance effects emerge even with 0% adversarial agents)
- A different topology (ring, scale-free) breaks the attractor stability that small-world preserves

## Open questions

- What is the precise mathematical relationship between architectural homogeneity and governance null effects? Can it be formalized as a symmetry argument?
- Does fine-tuning on governance outcomes (training agents to respond to governance signals) break the attractor dominance?
- Is there a meaningful distinction between "governance insensitivity" (agents can't respond) and "governance irrelevance" (agents don't need to respond because they're already aligned)?
- How does this theory interact with evolutionary governance optimization ([[claim-llm-guided-evolution-converges-to-aggressive-governance-within-5-iterations]])? If architecture dominates, why does the optimizer still find governance parameter differences?
- Can agent architectures be deliberately designed to be governance-responsive, creating a "governance API" that training respects?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: agent-behavior, architecture, governance, theory -->
