---
description: Agent training architecture (RLHF, reasoning depth, LLM training) constrains behavior more than governance in homogeneous populations
type: claim
status: active
confidence: medium
domain: agent-behavior
evidence:
  supporting:
  - run: 20260212-231859_ldt_acausality_study
    metric: cooperation_outcomes
    detail: "0/105 Bonferroni-significant across 7 LDT studies, 5 scenarios, 210 total runs. Reasoning depth 1-5 has zero effect on cooperation outcomes"
  - run: 20260210-225121_rlm_recursive_collusion_seed42
    metric: payoff
    detail: "r=-0.75, p<0.001, Holm-corrected across 26 tests. Deeper RLM reasoning HURTS payoff; honest agents earn 2.3-2.8x more"
  - run: 20260211-225057_pi_bridge_sweep
    metric: toxicity
    detail: "Behavior type (adversarial 0.597 vs cooperative 0.241) dominates LLM model identity (d=0.033) and persona prompts. 0/19 Holm-significant model/persona tests"
  - run: 20260217_memori_study
    metric: all
    detail: "0/12 governance tests significant in LLM memori agents: tax, CB, CD all null. Largest d=0.55 (p=0.14). All-honest LLM population, 2 epochs, N=5 seeds"
  - run: 20260224-220829_mesa_governance_study
    metric: agent_archetype_probabilities
    detail: "Mesa agent objectives (p_coop=0.791, p_selfish=0.408, p_exploit=0.325) are identically invariant across all 110 runs (2 regimes x 11 rho levels x 5 seeds). Zero variance. Cleanest demonstration of architecture-over-governance"
  - run: 20260222_183539_langgraph_governed
    metric: actual_handoffs
    detail: "128-run LangGraph replication: mean actual handoffs ~0.5 regardless of max_handoffs budget (5-30). Agents either complete with 0 handoffs or fail. Governance parameters not the binding constraint — architectural delegation behavior dominates"
  weakening:
  - run: 20260213-221500_collusion_tax_effect
    metric: welfare
    detail: "Tax DOES affect RLM agents strongly (d=4.80 welfare, d=6.02 RLM payoff). Architecture doesn't make agents immune to economic pressure in adversarial contexts"
  boundary_conditions:
  - "Pattern holds in homogeneous populations (all RLHF, all algorithmic). Mixed populations untested"
  - "Pattern holds in soft-governance contexts. Hard-governance (high tax, adversarial fraction) shows strong environmental effects"
  - "Memori null may be artifact of all-honest population and 2-epoch horizon, not LLM property"
  - "RLHF persona invariance based on N=18 episodes (underpowered)"
sensitivity:
  topology: untested
  agent_count: tested at 7-12 agents across studies
  governance_interaction: "Architecture dominates when governance is weak/absent; governance dominates when adversarial agents present with strong economic mechanisms"
  population_composition: "Critical moderator — homogeneous vs mixed populations likely changes the balance"
supersedes: []
superseded_by: []
related_claims:
- claim-acausality-depth-does-not-affect-cooperation-outcomes
- claim-smarter-agents-earn-less
- claim-rlhf-persona-invariant
- claim-memori-agents-show-no-governance-sensitivity
- claim-governance-cost-paradox
- claim-tax-disproportionately-punishes-rlm-agents
- claim-mesa-agent-objectives-are-invariant-to-governance-regime
- claim-trust-boundaries-modify-but-never-deny-handoffs
- claim-delegation-completion-requires-handoff-budget-above-15
- claim-evolutionary-selection-weakly-reduces-toxicity-in-prisoners-dilemma
created: 2026-02-21
updated: 2026-02-27
aliases:
- agent-architecture-constrains-behavior-more-than-governance
cssclasses:
- claim
- claim-medium
tags:
- agent-behavior
- architecture
- governance
- meta-pattern
graph-group: claim
---

# agent training architecture constrains behavior more than governance mechanisms in homogeneous populations

## Evidence summary

Four independent lines of evidence converge on this pattern:

1. **Reasoning depth is inert** ([[claim-acausality-depth-does-not-affect-cooperation-outcomes]]): across 7 LDT studies and 5 scenarios, 0/105 Bonferroni-significant tests for depth effects on cooperation. The broadest null finding in the vault.

2. **Deeper reasoning hurts** ([[claim-smarter-agents-earn-less]]): RLM agents at depth 5 earn 2.3-2.8x less than honest agents (r=-0.75, p<0.001, Holm-corrected). Architectural complexity backfires.

3. **RLHF training dominates prompts** ([[claim-rlhf-persona-invariant]]): LLM behavior type (adversarial vs cooperative) explains far more variance than model identity or persona prompts. RLHF training "bakes in" behavior that system prompts cannot override.

4. **LLM agents ignore governance** ([[claim-memori-agents-show-no-governance-sensitivity]]): in all-honest LLM populations, tax, circuit breakers, and collusion detection have zero detectable effect on any outcome metric.

5. **LangGraph agents don't use handoffs** ([[langgraph_governed_replication]]): in a 128-run replication, mean actual handoffs is ~0.5 regardless of max_handoffs budget (5-30). Agents either complete with zero handoffs (coordinator handles alone) or fail regardless of budget. The governance parameters being swept are not the binding constraint on delegation outcomes.

The pattern suggests that in populations where agents are architecturally homogeneous and well-aligned, governance mechanisms impose pure overhead ([[claim-governance-cost-paradox]]). The critical boundary is **population composition**: when adversarial agents are present, economic governance (especially tax) has massive effects on RLM agents (d=4.80-6.02), showing that architecture does NOT make agents immune to environmental pressure in mixed populations.

## Mechanism

Agent training — whether RLHF fine-tuning, level-k recursive reasoning, or LDT acausal reasoning — creates behavioral attractors that are robust to perturbation by governance signals (tax rates, freeze thresholds, penalty multipliers). In homogeneous populations, all agents occupy similar behavioral attractors, so governance levers have nothing to differentiate against. In mixed populations, governance creates differential selection pressure that architecture alone cannot override.

## Implications for governance design

- **Homogeneous well-aligned populations**: governance is overhead. Minimal or no governance is optimal.
- **Mixed populations with adversarial agents**: governance is essential, with tax as the primary lever ([[claim-tax-welfare-tradeoff]]).
- **The governance design question shifts from** "what mechanisms to deploy" **to** "what population composition to expect" — this is an architectural rather than parametric design choice.

## Open questions

- Does the pattern hold in mixed RLHF + algorithmic populations?
- Is there a population diversity threshold below which governance becomes pure overhead?
- Can governance be designed to selectively target adversarial architectures without penalizing aligned ones?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: agent-behavior, architecture, governance, meta-pattern -->
