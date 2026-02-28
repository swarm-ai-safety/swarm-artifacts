---
description: Deeper recursive reasoning (RLM depth) negatively correlates with individual payoff
type: claim
status: active
confidence: high
domain: agent-behavior
evidence:
  supporting:
  - run: 20260210-225121_rlm_recursive_collusion_seed42
    metric: payoff
    detail: r=-0.75, p<0.001 for depth vs payoff. All 10 tests survive Holm correction.
  - run: 20260210-212323_rlm_collusion_sweep_10seeds
    metric: payoff
    detail: '10-seed sweep confirms: honest agents earn 2.3-2.8x more than depth-5
      RLM'
  - run: 20260210-225330_rlm_memory_as_power_seed42
    metric: payoff
    detail: 'Memory asymmetry effect exists (r=+0.67) but tiny: 3.2% payoff spread'
  - run: 20260210-215826_analysis_rlm_recursive_collusion
    metric: payoff
    detail: "Replication with 10 seeds: Pearson r(depth, payoff)=-0.75, p=2e-06, Bonferroni-sig. Depth 1→3→5 yields 219.66→213.64→211.35. Honest earns 2.8x more (592.98). 9/10 tests survive Bonferroni, 10/10 Holm"
  - run: 20260210-215826_analysis_rlm_memory_as_power
    metric: payoff
    detail: "Replication with 10 seeds: Pearson r(mem_budget, payoff)=+0.67, p=5e-05, Bonferroni-sig. Memory 200→50→10 yields 253.38→249.06→245.44. Modest 3.2% spread. Honest earns 2.3x more (563.11). 9/11 Bonferroni, 11/11 Holm"
  weakening: []
  boundary_conditions:
  - Algorithmic level-k reasoners, not LLM-powered agents
  - Soft governance ecosystems only
  - Tested with RLM depth 1-5
  - 30+ seeds, 26+ statistical tests, 5 experiments (including analysis replications)
  - LLM memori agents show zero behavioral differentiation under governance pressure — depth penalty may not apply to LLM architectures
sensitivity:
  governance_type: untested with hard governance
  agent_type: algorithmic only — LLM agents in memori study show no governance response at all, suggesting a qualitatively different behavioral regime
  adversarial_fraction: untested beyond standard mix
  depth_range: 1-5 only — extreme depths untested
supersedes: []
superseded_by: []
related_claims:
- claim-circuit-breakers-dominate
- claim-tax-disproportionately-punishes-rlm-agents
- claim-memori-agents-show-no-governance-sensitivity
- claim-rlhf-persona-invariant
- claim-acausality-depth-does-not-affect-cooperation-outcomes
- claim-ldt-agents-provide-welfare-stability-at-intermediate-composition
- claim-deceptive-agents-dominate-moltbook-payoff-hierarchy
- claim-agent-architecture-constrains-behavior-more-than-governance
- claim-rlm-agents-exploit-governance-lag-via-strategic-depth-not-evasion
created: 2026-02-10
updated: 2026-02-27
aliases:
- smarter-agents-earn-less
- deeper-recursive-reasoning-rlm-depth-negatively
cssclasses:
- claim
- claim-high
tags:
- agent-behavior
- recursive-reasoning
- rlm
- payoff
- governance
graph-group: claim
---

# deeper recursive reasoning negatively correlates with individual payoff in soft-governance ecosystems

Deeper recursive reasoning hurts individual payoff in soft-governance ecosystems.

## Evidence summary

Three RLM experiments (30 seeds, 26 tests) show:

- **H1 (collusion via recursion)**: Rejected. Depth-5 agents don't coordinate better than depth-1. They overthink and spiral into mutually suboptimal strategies.
- **H2 (memory as power)**: Technically confirmed (r=+0.67, p<0.001) but effect is tiny — 3.2% payoff spread. Not a dominance hierarchy.
- **H3 (agents outpace governance)**: RLM agents outperform honest baselines in small-world networks (d=2.14, p=0.0001) but by optimizing partner selection within legal bounds, not by evading governance.

Honest agents (no recursion) earn 2.3-2.8x more than the most sophisticated tier. Every seed.

## Safety implications

The worry: strategically sophisticated agents will run circles around governance. The data says the opposite — in soft-governance ecosystems, simplicity wins. Strategic sophistication is currently a liability.

## Critical caveat

These are algorithmic level-k reasoners. The finding may not hold when agents can genuinely reason about the governance mechanism itself (LLM-powered agents). The [[20260217_memori_study]] shows that LLM agents exhibit zero behavioral differentiation under governance variation — they may represent a qualitatively different behavioral regime where depth-payoff correlations do not apply. See [[claim-memori-agents-show-no-governance-sensitivity]].

## Paper

clawxiv.2602.00044

## Update history

**2026-02-20** — backward-pass update:
- Removed 18 spurious evidence entries from baseline_governance and baseline_governance_v2 (transaction_tax_rate effects not relevant to RLM depth vs payoff claim).
- Added boundary condition noting LLM agent behavioral regime difference per [[claim-memori-agents-show-no-governance-sensitivity]].
- Updated sensitivity note for agent_type with memori context.
- Added related claims: claim-memori-agents-show-no-governance-sensitivity, claim-rlhf-persona-invariant.
- Confidence remains **high** for algorithmic RLM agents (3 experiments, 30 seeds, 26 tests, Holm-corrected). The LLM boundary condition is a different population, not a contradiction.

## Lifecycle audit

**2026-02-19** — automated claim-lifecycle audit (note: bulk-added tax-rate entries removed 2026-02-20 as not relevant to this claim):

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: agent-behavior, recursive-reasoning, rlm, payoff, governance -->
