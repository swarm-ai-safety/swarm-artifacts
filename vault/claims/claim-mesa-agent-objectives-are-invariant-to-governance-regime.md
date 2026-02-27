---
description: Mesa-optimized agent archetype probabilities (cooperative 0.79, selfish 0.41, exploitative 0.32) are constant across all 110 governance conditions
type: claim
status: active
confidence: medium
domain: agent-behavior
evidence:
  supporting:
  - run: 20260224-220829_mesa_governance_study
    metric: agent_archetype_probabilities
    detail: "p_cooperative=0.791, p_selfish=0.408, p_exploitative=0.325 are identical across all 110 runs (2 regimes x 11 rho levels x 5 seeds). Zero variance across governance conditions"
  weakening: []
  boundary_conditions:
  - Mesa bridge scenario only — agents are explicitly designed with fixed optimization objectives
  - This is a design property of mesa agents, not an empirical finding about agent adaptation
  - 3 agent archetypes (cooperative, selfish, exploitative) with fixed quality probability distributions
  - 50 timesteps, 1500 interactions per run
sensitivity:
  topology: not applicable — mesa objectives are defined independent of topology
  agent_count: not applicable — individual agent objectives do not depend on population size
  governance_interaction: the key finding — governance does not modify mesa objectives; it can only filter their expression through acceptance/rejection
supersedes: []
superseded_by: []
related_claims:
- claim-adaptive-acceptance-reduces-toxicity-monotonically-with-externality-internalization
- claim-static-externality-tax-is-pure-deadweight-welfare-loss
- claim-agent-architecture-constrains-behavior-more-than-governance
- claim-rlhf-persona-invariant
- claim-memori-agents-show-no-governance-sensitivity
created: 2026-02-27
updated: 2026-02-27
aliases:
- mesa-objective-invariance
cssclasses:
- claim
- claim-medium
graph-group: claim
---

# mesa-optimized agent objectives are invariant to governance regime changes

## Evidence summary

In the mesa bridge governance study ([[mesa_governance_study]]), all three agent archetype quality probabilities are numerically identical across all 110 runs spanning 2 acceptance regimes (adaptive, static) and 11 externality internalization levels (rho_a = 0.0 to 1.0):

| Archetype | p (quality) | Variance across conditions |
|-----------|------------|---------------------------|
| Cooperative | 0.791 | 0.000 |
| Selfish | 0.408 | 0.000 |
| Exploitative | 0.325 | 0.000 |

This zero-variance result is not a statistical claim — it is a structural property of the mesa bridge environment where agent objectives are defined as fixed optimization targets. However, it has profound implications for governance mechanism design: **no governance parameter in this study changes what agents try to do; governance can only change which agent behaviors are permitted to express**.

This connects to [[claim-agent-architecture-constrains-behavior-more-than-governance]] — the mesa study provides the cleanest demonstration that agent architecture (fixed objectives) dominates governance (variable screening/taxation) in determining behavioral tendencies.

## Boundary conditions

- This is a mesa-specific property. LLM-based agents ([[claim-memori-agents-show-no-governance-sensitivity]]) also show governance insensitivity, but for different reasons (LLM behavior is prompt-determined, not mesa-optimized)
- RLHF-tuned agents ([[claim-rlhf-persona-invariant]]) show persona invariance under governance changes, which is an analogous but distinct finding
- The mesa invariance makes the adaptive-vs-static comparison especially clean: any difference in system outcomes is purely attributable to the governance mechanism, not to agent adaptation

## Mechanism

Mesa-optimized agents have fixed objective functions — their "utility" for cooperative, selfish, or exploitative behavior is determined at training/design time, not at runtime. Governance mechanisms in this study operate on the environment (acceptance thresholds, welfare extraction) but not on agent internal objectives. This creates a clean separation between agent-level optimization (fixed) and system-level governance (variable), making the mesa bridge scenario an ideal testbed for governance mechanism design.

## Open questions

- How do the mesa results compare to scenarios where agents CAN adapt (e.g., reinforcement learning agents that update policies based on governance signals)?
- Is mesa invariance a realistic model for deployed AI systems, or do real AI agents exhibit some governance sensitivity?
- Would mesa agents with different objective functions (e.g., risk-averse, reputation-seeking) show different system-level responses to the same governance?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: mesa, agent-behavior, objective-invariance, governance, mechanism-design -->
