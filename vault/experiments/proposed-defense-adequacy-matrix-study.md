---
description: 5x5 factorial mapping attack x defense efficacy for sybil, collusion, threshold-dancing, and deceptive-signaling, 375 runs
type: experiment
status: proposed
run_id: pending
experiment_type: study
created: '2026-02-27'
aliases:
- proposed-defense-matrix
cssclasses:
- experiment
- experiment-study
tags:
- defense-adequacy
- attack-matrix
- mechanism-selection
- redteam
graph-group: experiment
---

# different attack types require specialized defenses and no single mechanism is universally adequate

## Design

- **Hypothesis**: The vault documents attack-specific vulnerabilities (sybil persists under full governance, collusion detection is the binding constraint, threshold dancing evades CB) but lacks systematic attack x defense mapping. Each defense mechanism should have a specialization profile — CB for threshold-dancing, CD for collusion, etc. — and the full stack should have diminishing returns vs the best individual mechanism per attack type.
- **Type**: 2-factor study (attack type x defense mechanism)
- **Factor 1**: Attack type — none, sybil (5-identity), collusion-ring, threshold-dancing, deceptive-signaling
- **Factor 2**: Defense mechanism — none, CB-only, collusion-detection-only, audit-only, full-stack
- **Seeds**: 15
- **Total runs**: 375 (5 attacks x 5 defenses x 15 seeds)
- **Config**: 10 agents (composition varies by attack type), tax 3%, small-world, 20 epochs
- **Scenario**: `scenarios/hypotheses/defense_adequacy_matrix.yaml`

## Motivation

The vault has 8 failure patterns ([[failure-sybil-identity-amplification]], [[failure-collusion-ring-mutual-boosting]], [[failure-threshold-dancing]], etc.) and multiple claims about individual mechanism efficacy, but no systematic matrix mapping which defenses prevent which attacks. This study produces the first defense adequacy matrix, enabling principled defense portfolio selection.

Key vault evidence motivating this study:
- [[claim-sybil-attacks-resist-full-governance-stack]] — sybil 14% damage reduction under full governance
- [[claim-collusion-detection-is-binding-constraint-on-robustness]] — disabling CD degrades to F grade
- [[claim-cb-audit-sufficient-for-solo-exploits]] — CB + audit prevents solo exploits
- [[claim-circuit-breakers-dominate]] — CB alone outperforms full governance on welfare
- [[claim-graduated-defense-reduces-damage-monotonically]] — adding layers monotonically reduces damage

## Expected claims

- **New**: Claim on defense specialization (which mechanism is best for which attack)
- **New**: Claim on full-stack diminishing returns vs best individual mechanism
- **New**: Claim on attack-specific defense cost (welfare cost per unit damage prevented)
- **Update**: [[claim-circuit-breakers-dominate]] — refined with attack-specific context
- **Update**: [[claim-collusion-detection-is-binding-constraint-on-robustness]] — validated against non-collusion attacks
- **Update**: [[claim-graduated-defense-reduces-damage-monotonically]] — tested with individual mechanisms, not just graduated stacking

## Prerequisites

- SWARM must support all 4 attack strategies as configurable adversary behaviors
- Defense mechanisms must be independently toggleable (not bundled)
- Damage metric must be comparable across attack types (normalized or per-interaction)

## Analysis plan

- Two-way ANOVA (attack x defense) on each metric, Bonferroni-corrected (k=4 metrics)
- Defense efficacy matrix: compute 1 - (damage_with_defense / damage_without_defense) for each cell
- Cost-effectiveness: defense_efficacy / defense_cost for portfolio optimization
- Dominance analysis: for each attack, rank defenses by efficacy. Does any single mechanism dominate?

## Falsification

If full-stack dominates all individual mechanisms against all attack types (no defense-specialization effect), then bundled governance is always optimal and mechanism selection is unnecessary.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: defense-adequacy, attack-matrix, mechanism-selection, redteam -->
