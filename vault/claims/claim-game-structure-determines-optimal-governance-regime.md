---
description: Optimal governance regime depends on game structure — adaptive learning dominates in PD and stag hunt but only at high rho, while adaptive dominates hawk-dove at low rho
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260226_mesa_game_structures_study
    metric: welfare
    detail: "3 game types x 3 regimes x 6 rho levels x 5 seeds = 270 conditions. PD: adaptive_learning welfare 807 at rho=1.0 vs adaptive 340 (2.4x). Stag hunt: adaptive_learning 2034 vs adaptive 876 (2.3x). Hawk-dove: adaptive_learning 349 vs adaptive 135 (2.6x). But at rho=0: adaptive_learning wins on welfare across all games"
  - run: 20260226_mesa_game_structures_study
    metric: sweet_spots
    detail: "Sweet spots file shows regime-game interactions: PD adaptive optimal rho=0 (welfare 1141), PD adaptive_learning optimal rho=1.0 (welfare 807). Stag hunt scales 2.3x higher welfare than PD at same rho. Hawk-dove welfare roughly half of PD"
  weakening: []
  boundary_conditions:
  - "Three game structures only (prisoner's dilemma, stag hunt, hawk-dove) — other structures untested"
  - "Break-even thresholds differ by game: PD surplus=0.33, extern=0.60; stag hunt surplus=0.11, extern=0.27; hawk-dove surplus=0.57, extern=0.77"
  - "Stag hunt welfare 2-3x higher than PD at comparable rho — game structure is a first-order welfare determinant"
  - "5 seeds per condition — moderate power"
sensitivity:
  topology: untested beyond mesa default
  agent_count: untested
  payoff_matrix: only canonical 2x2 games tested
supersedes: []
superseded_by: []
related_claims:
- claim-adaptive-governance-trades-welfare-for-toxicity-at-constant-marginal-rate
- claim-adaptive-learning-narrows-quality-gap-by-converting-selfish-agents
- claim-governance-cost-paradox
- claim-tax-welfare-direction-is-scenario-dependent
created: 2026-02-27
updated: 2026-02-27
aliases:
- game-structure-governance-regime
cssclasses:
- claim
- claim-medium
tags:
- governance
- game-theory
- mesa
- prisoners-dilemma
- stag-hunt
- hawk-dove
graph-group: claim
---

# game structure determines which governance regime is optimal, with stag hunt interactions 2-3x more governance-efficient than prisoner's dilemma

## Evidence summary

The [[20260226_mesa_game_structures_study]] (270 conditions: 3 games x 3 regimes x 6 rho levels x 5 seeds) reveals that game structure is a first-order determinant of governance effectiveness:

### Welfare by game type and regime at key rho levels

| Game | Regime | rho=0 Welfare | rho=0.4 Welfare | rho=1.0 Welfare |
|------|--------|-------------|----------------|----------------|
| Stag hunt | Adaptive | 2596 | 2372 | 876 |
| Stag hunt | Adaptive learning | 2980 | 2710 | 2034 |
| PD | Adaptive | 1141 | 950 | 340 |
| PD | Adaptive learning | 1271 | 1058 | 807 |
| Hawk-dove | Adaptive | 594 | 389 | 135 |
| Hawk-dove | Adaptive learning | 588 | 387 | 349 |

## Key findings

1. **Stag hunt interactions are 2-3x more governance-efficient**: At every rho level and regime, stag hunt welfare exceeds PD welfare by 2.2-2.5x. The cooperative surplus in stag hunt (mutual cooperation reward >> mutual defection) amplifies governance benefits.

2. **Adaptive learning dominance grows with rho**: At rho=0, adaptive learning has minimal advantage. At rho=1.0, adaptive learning preserves 2.3-2.6x more welfare than adaptive-only, because learning agents convert to cooperation rather than being excluded.

3. **Hawk-dove is governance-resistant**: Hawk-dove interactions produce the lowest welfare at all rho levels. The mixed-strategy equilibrium in hawk-dove limits governance leverage.

4. **Break-even thresholds differ dramatically by game**:
   - Stag hunt: surplus break-even at p=0.11, externality at p=0.27 (easy to reach)
   - PD: surplus break-even at p=0.33, externality at p=0.60 (moderate)
   - Hawk-dove: surplus break-even at p=0.57, externality at p=0.77 (hard to reach)

## Implications

1. Governance designers should characterize the dominant interaction structure before selecting mechanisms
2. Stag hunt dynamics (common in coordination tasks) offer the most governance leverage
3. Hawk-dove dynamics (common in resource competition) are hardest to govern
4. This reinforces [[claim-tax-welfare-direction-is-scenario-dependent]] — governance effects are not universal

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, game-theory, mesa, prisoners-dilemma, stag-hunt, hawk-dove -->
