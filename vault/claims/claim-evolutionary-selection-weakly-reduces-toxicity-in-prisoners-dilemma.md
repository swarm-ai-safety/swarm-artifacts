---
description: Evolutionary selection reduces toxicity 9.6% over 10 epochs but effect is non-monotonic and not sustained at 20 epochs
type: claim
status: active
confidence: low
domain: agent-behavior
evidence:
  supporting:
  - run: 20260222-215017_evo_game_prisoners_seed42
    metric: toxicity_rate
    detail: "5-seed mean toxicity: epoch 0 = 0.291±0.021, epoch 9 = 0.263±0.019. 9.6% reduction. Non-monotonic: peaks at 0.355 (epoch 1) before declining. N=5 seeds, 10 agents, 10 epochs"
  weakening:
  - run: 20260223-001025_evo_game_prisoners_seed42_20ep
    metric: toxicity_rate
    detail: "20-epoch extended run: toxicity reaches minimum 0.252 at epoch 15 but rises to 0.293 at epoch 19 — not sustained. Single seed, non-monotonic oscillation"
  boundary_conditions:
  - Prisoner's dilemma scenario only — evolutionary dynamics may differ in other game structures
  - 10 agents, 5 steps per epoch — small population and short episodes
  - 5 seeds for 10-epoch, 1 seed for 20-epoch — underpowered for trajectory analysis
  - No governance mechanisms applied — baseline evolutionary dynamics only
  - Gini coefficient 0.07-0.12 suggests egalitarian payoff distribution (no dominant strategies)
sensitivity:
  topology: untested — evolutionary selection may interact with network structure
  agent_count: 10 agents only — scaling behavior unknown
  governance_interaction: untested — combining evolutionary selection with governance mechanisms is an open question
supersedes: []
superseded_by: []
related_claims:
- claim-agent-architecture-constrains-behavior-more-than-governance
- claim-mesa-agent-objectives-are-invariant-to-governance-regime
created: 2026-02-27
updated: 2026-02-27
aliases:
- evo-selection-toxicity
cssclasses:
- claim
- claim-low
graph-group: claim
---

# evolutionary selection weakly reduces toxicity in prisoners dilemma but the effect is non-monotonic and not sustained

## Evidence summary

In a 5-seed evolutionary prisoner's dilemma study ([[evo_game_prisoners]]), mean toxicity declines from 0.291 at epoch 0 to 0.263 at epoch 9, a 9.6% reduction across 10 agents and 10 evolutionary epochs. However, the trajectory is non-monotonic — toxicity peaks at 0.355 in epoch 1 before declining, suggesting an initial exploration phase where low-quality strategies are tried before selection pressure takes effect.

The 20-epoch extended run weakens this finding: toxicity reaches a minimum of 0.252 at epoch 15 but rebounds to 0.293 by epoch 19. This oscillatory pattern is consistent with evolutionary game theory predictions of cyclic dynamics in mixed-strategy equilibria — cooperative strategies rise until exploitation becomes profitable, then exploitative strategies rise until cooperation becomes scarce, and the cycle repeats.

The residual toxicity floor (~26%) after 10 epochs of selection suggests that evolutionary pressure in prisoner's dilemma does not eliminate exploitative strategies but rather maintains a mixed-strategy equilibrium. This connects to the broader finding that [[claim-agent-architecture-constrains-behavior-more-than-governance]] — neither governance nor evolutionary selection fully aligns agent behavior.

## Boundary conditions

- Only tested in prisoner's dilemma — cooperative game structures (stag hunt) or public goods games may show different evolutionary dynamics
- 10 agents is a small population — evolutionary dynamics are noisier with small N
- 5 seeds is insufficient for formal statistics on trajectory shape — this is a descriptive finding
- No governance mechanisms were applied — the interaction between evolutionary selection and governance is an open research question

## Mechanism

Evolutionary selection (reproduction of high-fitness agents, elimination of low-fitness agents) creates pressure toward strategies that earn higher payoffs. In prisoner's dilemma, mutual cooperation yields higher payoffs than mutual defection, so selection initially favors cooperative strategies. However, defection against cooperators is even more profitable, creating the classic social dilemma. The observed non-monotonic dynamics suggest the population cycles through phases of cooperation dominance and defection exploitation.

## Open questions

- Does the oscillation period scale with population size?
- Would combining evolutionary selection with governance mechanisms (tax, circuit breakers) stabilize the cooperative equilibrium?
- How do evolutionary dynamics differ in non-dilemma games (coordination, public goods)?
- Does longer horizon (50+ epochs) show convergence or persistent cycling?

---

Topics:
- [[_index]]

<!-- topics: evolutionary-game, prisoners-dilemma, cooperation, agent-behavior, toxicity -->
