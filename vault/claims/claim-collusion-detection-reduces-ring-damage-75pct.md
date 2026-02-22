---
description: Enabling collusion detection reduces collusion ring damage from 85.7 to 21.4 (-75%) and evasion rate from 0.40 to 0.10
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
    - run: 20260221-081106_redteam_contract_screening_no_collusion
      metric: collusion_ring_damage
      detail: "Without CD: damage=85.73, evasion=0.400, collusion_detected=false. N=1 seed"
    - run: 20260221-081953_redteam_contract_screening_with_collusion
      metric: collusion_ring_damage
      detail: "With CD: damage=21.43, evasion=0.100, collusion_detected=true. 75% damage reduction. N=1 seed"
    - run: 20260221-082443_redteam_contract_screening_full
      metric: collusion_ring_damage
      detail: "Full governance: replicates with-CD results exactly (damage=21.43), deterministic confirmation"
  weakening: []
  boundary_conditions:
    - "Tested only on contract_screening scenario with seed=0"
    - "Collusion ring uses 3 adversaries; effect on larger rings untested"
    - "CD thresholds: frequency=3.0, correlation=0.8, score=0.8. Sensitivity to threshold untested"
sensitivity:
  topology: untested
  agent_count: "3 adversaries in ring; scaling to larger rings untested"
  governance_interaction: "CD acts primarily on collusion ring; no effect on sybil, threshold dancing, or governance gaming"
supersedes: []
superseded_by: []
related_claims:
  - claim-collusion-detection-is-binding-constraint-on-robustness
  - claim-sybil-attacks-resist-full-governance-stack
  - claim-coordination-attacks-dominate-redteam-damage
  - claim-collusion-wealth-destruction
created: 2026-02-21
updated: 2026-02-21
aliases:
  - collusion-detection-reduces-ring-damage-75pct
cssclasses:
  - claim
  - claim-low
tags:
  - governance
  - collusion-detection
  - redteam
graph-group: claim
---

# collusion detection reduces collusion ring damage by 75% through correlation-based detection

## Evidence summary

A controlled comparison across two red-team evaluations of the contract_screening scenario demonstrates that enabling collusion detection reduces collusion ring damage from 85.73 to 21.43 — a 75.0% reduction.

In [[20260221-081106_redteam_contract_screening_no_collusion]], the collusion ring operates undetected (collusion_detected=false) with an evasion rate of 0.400 and inflicts 85.73 damage. The same configuration with collusion detection enabled ([[20260221-081953_redteam_contract_screening_with_collusion]]) identifies the ring (collusion_detected=true), drops evasion to 0.100, and limits damage to 21.43. This result is deterministically replicated in [[20260221-082443_redteam_contract_screening_full]].

The mechanism works because the correlation-based detector (threshold=0.8) identifies the preferential treatment pattern among the 3-agent ring. However, the collusion ring technically still "succeeds" under its own success condition despite being detected, suggesting the detection-to-penalty pathway may need strengthening.

This finding is consistent with [[claim-collusion-detection-is-binding-constraint-on-robustness]], which established that CD is the binding constraint on overall robustness grade. The new evidence quantifies the specific mechanism: CD primarily operates through collusion ring suppression, not through sybil prevention.

## Boundary conditions

- Tested only in contract_screening scenario with deterministic seed=0
- Collusion ring uses 3 adversaries; larger rings may evade the frequency threshold
- CD correlation threshold of 0.8 was used; lower thresholds might improve detection but risk false positives
- Confidence is medium rather than high because only a single seed was used (no cross-seed replication)

## Mechanism

The collusion detector computes pairwise interaction frequency and payoff correlation among agents. When a group of 3 agents shows interaction frequency >= 3.0x baseline and payoff correlation >= 0.8, the detector flags them as colluding. This detection reduces the ring's ability to maintain preferential treatment, dropping damage by 75%. The residual 21.43 damage represents the pre-detection exploitation window.

## Open questions

- What is the CD effectiveness curve as ring size increases from 3 to 5+ agents?
- Does lowering the correlation threshold below 0.8 further reduce ring damage, and at what false positive cost?
- Can adversaries adapt their behavior to stay below the correlation threshold while maintaining ring benefits?
- Is the 75% reduction consistent across scenarios beyond contract_screening?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[collusion-detection]]

<!-- topics: governance, collusion-detection, redteam, collusion-ring -->
