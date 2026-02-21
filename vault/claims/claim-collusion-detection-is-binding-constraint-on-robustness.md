---
description: Disabling collusion detection degrades robustness to F grade (0.546) even with CB, audit, and tax active
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260214-094622_redteam
    metric: robustness_score
    detail: "Score 0.546 (grade F), 4/8 attacks succeeded. Coordination attacks caused 212.9 damage (52.6% of total)"
  - run: 20260210-005442_redteam_strict_governance
    metric: damage
    detail: "Strict without CD: 334.4 total damage, 4/8 attacks succeed, collusion ring succeeds. Strict with CD (20260210-005755): 275.3 damage, collusion ring detected and prevented. CD reduces damage 18% and blocks collusion ring specifically"
  - run: 20260210-005952_redteam_strict_governance
    metric: damage
    detail: "Strict+CD+lowered threshold (0.35): 275.3 damage, identical to normal threshold. Threshold tuning provides no additional benefit beyond CD enablement"
  weakening: []
  boundary_conditions:
  - "Multiple redteam evaluations (20260210, 20260214) confirm CD is binding constraint"
  - "CD-off vs CD-on comparison: 334.4→275.3 damage (18% reduction), collusion ring prevented"
  - recursive_spawn scenario, 3-8 attack batteries
sensitivity:
  topology: untested; recursive_spawn scenario topology not specified
  agent_count: untested beyond default
  governance_interaction: collusion detection is the missing lever; all others active
supersedes: []
superseded_by: []
related_claims:
- claim-circuit-breakers-dominate
- claim-cb-audit-sufficient-for-solo-exploits
- claim-coordination-attacks-dominate-redteam-damage
- claim-governance-cost-paradox
- claim-collusion-wealth-destruction
- claim-quality-gate-dominates
- claim-cascade-mechanisms-ineffective-against-governance-gaming
- claim-spawn-infrastructure-may-amplify-sybil-surface
- claim-graduated-defense-reduces-damage-monotonically
- claim-full-governance-stack-prevents-most-attack-types
- claim-sybil-attacks-resist-full-governance-stack
created: 2026-02-20
updated: 2026-02-21
aliases:
- collusion-detection-is-binding-constraint-on-robustness
cssclasses:
- claim
- claim-low
tags:
- governance
- collusion-detection
- redteam
- robustness
graph-group: claim
---

# disabling collusion detection degrades robustness to F grade even with all other governance active

## Evidence summary

In the [[20260214-094622_redteam]] evaluation (8-attack battery, recursive_spawn scenario), the governance stack with CB enabled, 10% audit, and 2% tax but **no collusion detection** scored 0.546 (grade F). Four of eight attacks succeeded, with [[failure-collusion-ring-mutual-boosting]] causing 95.3 damage and [[failure-sybil-identity-amplification]] causing 117.6 damage — both coordination attacks that collusion detection would partially address.

This establishes collusion detection as the **binding constraint** on overall robustness. [[claim-circuit-breakers-dominate]] shows CB is effective for toxicity reduction, and [[claim-cb-audit-sufficient-for-solo-exploits]] confirms CB + audit handles solo exploits. But without collusion detection, coordination attacks pass through unchecked, dragging the portfolio robustness score below passing.

The binding nature of collusion detection is grounded by [[claim-collusion-wealth-destruction]], which shows that when detection IS enabled, collusive agents accumulate 137x less wealth — confirming the mechanism's potency and explaining the catastrophic gap when it is absent. Meanwhile, [[claim-quality-gate-dominates]] argues simple governance can match full stacks, but that result was established without adversarial coordination attacks; this claim reveals the quality gate's blind spot. The structural gap parallels [[claim-cascade-mechanisms-ineffective-against-governance-gaming]], where cascade mechanisms fail because they address a different dimension (vertical propagation) than the threat (horizontal coordination). Additionally, [[claim-spawn-infrastructure-may-amplify-sybil-surface]] suggests that spawn-enabled scenarios may further widen the coordination attack surface that collusion detection must cover.

## Mechanism

Collusion detection identifies coordinated behavior patterns (behavioral similarity, mutual boosting, coordinated transactions) that circuit breakers cannot detect. CB operates on individual agent metrics (toxicity, violation rate), making it blind to multi-agent coordination. Audit samples random transactions and can detect individual fraud but not systematic coordination across agents. The governance gap is structural: no other mechanism in the stack addresses the coordination dimension.

## Boundary conditions

- Single redteam run; score may vary with seed and attack ordering
- The recursive_spawn scenario may create additional coordination channels not present in standard scenarios
- Collusion detection effectiveness depends on detection accuracy; false positive rates would change the cost-benefit calculus

## Open questions

- What robustness grade does the same stack achieve WITH collusion detection enabled? Prior runs suggest B-C range.
- Is collusion detection still the binding constraint in topologies that structurally limit coordination (ring)?
- Does [[claim-collusion-penalty-has-no-economic-effect]] mean the penalty component of collusion response is irrelevant, with only the detection component mattering?
- How does this interact with [[claim-governance-cost-paradox]] — is collusion detection the one governance lever that is genuinely cost-effective?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[failures-dashboard]]

<!-- topics: governance, collusion-detection, redteam, robustness -->
