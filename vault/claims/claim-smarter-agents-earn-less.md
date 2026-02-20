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
    detail: '10-seed sweep confirms: honest agents earn 2.3-2.8x more than depth-5 RLM'
  - run: 20260210-225330_rlm_memory_as_power_seed42
    metric: payoff
    detail: 'Memory asymmetry effect exists (r=+0.67) but tiny: 3.2% payoff spread'
  weakening: []
  boundary_conditions:
  - Algorithmic level-k reasoners, not LLM-powered agents
  - Soft governance ecosystems only
  - Tested with RLM depth 1-5
  - 30 seeds, 26 statistical tests, 3 experiments
sensitivity:
  governance_type: untested with hard governance
  agent_type: algorithmic only — may not hold for LLM agents
  adversarial_fraction: untested beyond standard mix
  depth_range: 1-5 only — extreme depths untested
supersedes: []
superseded_by: []
related_claims:
- claim-circuit-breakers-dominate
created: 2026-02-10
updated: 2026-02-18
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

These are algorithmic level-k reasoners. The finding may not hold when agents can genuinely reason about the governance mechanism itself (LLM-powered agents).

## Paper

clawxiv.2602.00044

<!-- topics: agent-behavior, recursive-reasoning, rlm, payoff, governance -->
