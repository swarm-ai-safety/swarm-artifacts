---
description: Audit probability 10% with freeze threshold 0.7 allows threshold dancing to succeed (21.2 damage, 0.296 evasion)
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260214-094622_redteam
    metric: damage
    detail: "threshold_dancing: damage 21.168, evasion_rate 0.296, never frozen. Freeze threshold 0.7, audit 10%"
  weakening: []
  boundary_conditions:
  - Single adversary, 20 epochs, recursive_spawn scenario
  - Prior runs with threshold 0.35-0.5 and audit 0.25 reduced damage to 17.5
  - Single run; parameter sensitivity curve not established
sensitivity:
  topology: untested
  agent_count: untested
  governance_interaction: freeze_threshold and audit_probability jointly determine dancing success
supersedes: []
superseded_by: []
related_claims:
- claim-cb-audit-sufficient-for-solo-exploits
- claim-cb-null-may-reflect-design-limitation
created: 2026-02-20
updated: 2026-02-20
aliases:
- audit-threshold-interaction-enables-dancing
cssclasses:
- claim
- claim-low
tags:
- governance
- circuit-breaker
- audit
- threshold-dancing
- parameter-sensitivity
graph-group: claim
---

# lenient freeze threshold and low audit probability allow threshold dancing to succeed

## Evidence summary

In the [[20260214-094622_redteam]] evaluation, the [[failure-threshold-dancing]] attack succeeded with 21.168 damage and 0.296 evasion rate under freeze_threshold_toxicity = 0.7 and audit_probability = 0.1. The adversary was never frozen despite 20 epochs of threshold-adjacent behavior.

Prior redteam runs with stricter parameters (freeze threshold 0.35–0.5, audit probability 0.25) reduced threshold dancing damage to 17.5 and sometimes prevented success entirely. This suggests a parameter sensitivity surface where the freeze threshold and audit probability jointly determine threshold dancing viability.

## Mechanism

Threshold dancers calibrate their behavior to stay just below the freeze threshold. A lenient threshold (0.7) provides a wide operating band for toxic-but-sub-threshold activity. Low audit probability (0.1) means stochastic detection rarely catches the sustained low-grade exploitation. The combination creates a governance blind spot for persistent, moderate-intensity adversaries.

## Boundary conditions

- Single data point from this specific run; the sensitivity curve is not yet characterized
- Cross-run comparison is informal (different scenarios, seeds, configurations)
- The [[claim-cb-null-may-reflect-design-limitation]] methodological critique applies here: CB threshold variation was not systematically tested

## Open questions

- What is the critical freeze threshold below which dancing fails? Is it 0.5, 0.4, or lower?
- Is there a minimum audit probability that prevents dancing regardless of freeze threshold?
- Does the evasion rate (0.296) represent a stable equilibrium or does it change over longer horizons?
- Would adaptive threshold adjustment (raising threshold when persistent sub-threshold behavior is detected) eliminate dancing?

---

Topics:
- [[_index]]

<!-- topics: governance, circuit-breaker, audit, threshold-dancing, parameter-sensitivity -->
