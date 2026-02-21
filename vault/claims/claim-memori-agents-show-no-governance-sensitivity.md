---
description: Memori LLM agents show zero significant governance response across 12 tests (all honest, 2 epochs, N=5)
type: claim
status: active
confidence: low
domain: agent-behavior
evidence:
  supporting:
  - run: 20260217_memori_study
    metric: all
    detail: "12 pairwise tests, 0 significant after Bonferroni/Holm. Largest d=0.55 (CB on quality_gap, p=0.14). All adversarial/opportunistic/deceptive payoffs = 0"
  weakening: []
  boundary_conditions:
  - llm_memori_openrouter_v1 scenario, 5 agents (all honest), 2 epochs x 5 steps, 5 seeds
  - Agent homogeneity prevents governance stress-testing (no adversarial behavior to deter)
  - 2-epoch horizon may be too short for governance effects to manifest
  - Only 10.8 interactions per run vs 59.8 in kernel studies
sensitivity:
  topology: untested
  agent_count: 5 agents, all honest
  governance_interaction: neither tax nor CB show effects; untestable without adversarial agents
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-direction-is-scenario-dependent
- claim-rlhf-persona-invariant
- claim-cb-null-may-reflect-design-limitation
created: 2026-02-20
updated: 2026-02-20
aliases:
- memori-agents-show-no-governance-sensitivity
cssclasses:
- claim
- claim-low
tags:
- agent-behavior
- llm
- memori
- null-result
- methodology
graph-group: claim
---

# memori LLM agents show no governance sensitivity in short-horizon homogeneous study

## Evidence summary

In the [[20260217_memori_study]] (30 runs, 6 configs, 5 seeds), zero out of 12 pairwise governance tests reach significance after Bonferroni or Holm correction. The largest effect is CB on quality_gap (d=0.55, p=0.14). Tax comparisons show d<0.23 with p>0.60.

Critical limitation: all agents are honest (adversarial/opportunistic/deceptive payoffs = 0.0 across all 30 runs). The study cannot test governance deterrent effects because there is no adversarial behavior to deter. Combined with the 2-epoch horizon (only 10.8 interactions per run), this is likely underpowered by design.

This connects to [[claim-rlhf-persona-invariant]] — if LLM agents behave identically regardless of governance pressure (as RLHF models show identical behavior across adversarial prompts), governance mechanisms may be fundamentally unnecessary in LLM-only ecosystems.

## Open questions

- Repeat with adversarial/opportunistic LLM agent types injected
- Extend to 10+ epochs to allow governance effects to accumulate
- Is the null result a property of LLM agents or of the study design?

---

Topics:
- [[_index]]

<!-- topics: agent-behavior, llm, memori, null-result, methodology -->
