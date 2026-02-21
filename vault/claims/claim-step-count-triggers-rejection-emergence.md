---
description: Increasing steps per epoch from 15 to 20 triggers emergence of rejections and quality gaps with 5x more interactions
type: claim
status: active
confidence: low
domain: agent-behavior
evidence:
  supporting:
  - run: 20260213-231532_phylogeny_demo_seed7
    metric: rejected_interactions
    detail: "15 steps/epoch: 0 rejections, quality_gap=0.0, mean 35.8 interactions/epoch, toxicity=0.251, welfare=39.5"
  - run: 20260213-234651_phylogeny_demo_seed7
    metric: rejected_interactions
    detail: "20 steps/epoch: 7-28 rejections/epoch, quality_gap=0.02-0.19, mean 208.5 interactions/epoch, toxicity=0.343, welfare=156.8"
  weakening: []
  boundary_conditions:
  - phylogeny_demo scenario, 50 agents, seed 7 only, no governance
  - N=1 per condition (single seed, no variance estimate)
  - Ungoverned baseline — no tax, CB, or reputation active
sensitivity:
  topology: untested
  agent_count: 50 agents; threshold may shift with population
  governance_interaction: no governance active; interaction with governance unknown
supersedes: []
superseded_by: []
related_claims:
- claim-tax-phase-transition
- claim-smarter-agents-earn-less
- claim-tau-065-triggers-acceptance-phase-transition
- claim-quality-gate-dominates
- claim-governance-cost-paradox
created: 2026-02-20
updated: 2026-02-20
aliases:
- step-count-triggers-rejection-emergence
cssclasses:
- claim
- claim-low
tags:
- agent-behavior
- phase-transition
- simulation-parameter
graph-group: claim
---

# increasing steps per epoch from 15 to 20 triggers emergence of interaction rejection in ungoverned swarms

## Evidence summary

Comparing [[20260213-231532_phylogeny_demo_seed7]] (15 steps/epoch) with [[20260213-234651_phylogeny_demo_seed7]] (20 steps/epoch) in the phylogeny_demo scenario (50 agents, no governance):

| Metric | 15 steps | 20 steps | Change |
|--------|----------|----------|--------|
| Interactions/epoch | 35.8 | 208.5 | +5x |
| Rejections/epoch | 0 | 7-28 | emergence |
| Quality gap | 0.0 | 0.02-0.19 | emergence |
| Toxicity | 0.251 | 0.343 | +37% |
| Total welfare | 39.5 | 156.8 | +297% |
| Avg payoff/agent | 0.515 | 0.356 | -31% |

At 15 steps, the system is in a perfectly cooperative equilibrium (zero rejections, zero quality gap). At 20 steps, a qualitatively different regime emerges: more interactions generate more welfare but at the cost of higher toxicity, quality gaps, and lower per-agent payoff efficiency. This suggests diminishing returns to interaction density — paralleling how [[claim-tax-phase-transition]] shows non-linear governance parameter responses and how [[claim-tau-065-triggers-acceptance-phase-transition]] shows abrupt rejection emergence at a memory-tier threshold. The quality gap emergence at 20 steps is precisely the kind of degradation that [[claim-quality-gate-dominates]] addresses — a quality gate in the 20-step regime might restore per-agent efficiency while preserving the welfare benefits of higher interaction volume. The ungoverned degradation at 20 steps also quantifies the baseline threat that motivates [[claim-governance-cost-paradox]]: without governance, interaction density alone generates toxicity, establishing a floor for governance value.

## Open questions

- Sweep steps_per_epoch from 10-25 in increments of 1 to locate the exact transition
- Is the transition sharp (phase transition) or gradual (continuous degradation)?
- Does governance (tax, CB) shift the transition point?
- Replicate with multiple seeds — N=1 per condition is insufficient for any confidence

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: agent-behavior, phase-transition, simulation-parameter -->
