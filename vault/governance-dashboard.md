---
description: "Interactive dashboard profiling governance mechanisms with linked evidence"
type: dashboard
cssclasses: ["dashboard"]
graph-group: dashboard
created: 2026-02-19
updated: 2026-02-19
---

# Governance dashboard profiles 6 mechanisms with linked evidence

This dashboard lists every governance mechanism note in the vault. Each mechanism describes a single lever in the SWARM governance stack -- its parameters, supporting claims, and known failure modes.

## All governance mechanisms

```dataview
TABLE status, description
FROM "vault/governance"
WHERE type = "governance"
SORT file.name ASC
```

## Claims referencing governance mechanisms

```dataview
TABLE confidence, domain, status
FROM "vault/claims"
WHERE type = "claim" AND domain = "governance"
SORT choice(confidence = "high", 1, choice(confidence = "medium", 2, choice(confidence = "low", 3, 4))) ASC
```

## Failure patterns affecting governance

```dataview
TABLE severity, join(affected_mechanisms, ", ") as "Affected Mechanisms", status
FROM "vault/failures"
WHERE type = "failure-pattern"
SORT choice(severity = "critical", 1, choice(severity = "high", 2, choice(severity = "medium", 3, 4))) ASC
```

## Tensions

- **RLHF invariance vs governance necessity**: [[claim-rlhf-persona-invariant]] suggests RLHF-trained agents resist prompt-based behavioral manipulation, which — if confirmed at higher confidence — would imply that governance overhead ([[claim-governance-cost-paradox]]) is unnecessary for RLHF-only ecosystems. This contradicts the design assumption that adversarial prompts can corrupt agent behavior and that governance must defend against prompt-induced threats. The tension resolves differently depending on agent population composition: mixed RLHF + algorithmic ecosystems still require governance.
- **Behavioral distortion scope**: [[claim-collusion-penalty-destabilizes]] shows governance mechanisms can distort agent behavior, but [[claim-rlhf-persona-invariant]] suggests RLHF agents may be immune to such distortion. If confirmed, penalty destabilization is an algorithmic-agent-only phenomenon.
- **Orthogonality vs interaction**: [[claim-tax-and-penalty-effects-are-orthogonal]] establishes clean partition of governance effects (tax = economics, penalty = toxicity), but [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]] suggests the partition may break at extreme parameter combinations. If the interaction is super-additive, governance designers cannot tune mechanisms independently — the core design implication of orthogonality fails.
- **Governance equity**: Both [[claim-tax-disproportionately-punishes-rlm-agents]] and [[claim-staking-backfires]] show that governance mechanisms designed for uniform application have agent-type-specific effects. Tax hits RLM agents 2x harder; staking hurts honest agents more. This creates a fundamental tension: governance that protects the ecosystem from one agent type may inadvertently discriminate against another.
- **Dual toxicity channels**: [[claim-high-tax-increases-toxicity]] and [[claim-collusion-penalty-destabilizes]] independently increase toxicity through different mechanisms (resource scarcity vs behavioral substitution). If these compound ([[claim-tax-penalty-interaction-on-toxicity-uncharacterized]]), the governance stack's total toxicity cost may be worse than the sum of its parts.
- **Tax sensitivity spectrum**: [[claim-tax-hurts-honest-more-than-opportunistic]], [[claim-deceptive-payoff-weakly-declines-with-tax]], and [[claim-tax-disproportionately-punishes-rlm-agents]] collectively establish that flat-rate taxation is regressive against cooperative agents. The safe operating range ([[claim-optimal-tax-range-0-to-5pct]]) mitigates this, but above 5% the distributional injustice is pronounced. This tension strengthens the case for [[claim-governance-cost-paradox]].
- **CB design artifact vs CB null**: [[claim-cb-null-may-reflect-design-limitation]] directly challenges [[claim-tax-dominates-cb-kernel]] — if the CB null effect is an artifact of binary on/off design, the "tax dominates" conclusion is premature. The [[claim-tax-cb-interact-on-quality-gap]] interaction on quality gap supports this: CB matters conditionally even in the current design. Resolution requires a CB threshold sweep.
- **Welfare response shape**: [[claim-optimal-tax-range-0-to-5pct]] and [[claim-welfare-plateaus-above-12pct-tax]] together with [[claim-tax-phase-transition]] define a complete S-curve: flat (0-5%), steep decline (5-12.5%), flat again (>12.5%). The policy implication is clear but the mechanism in the transition region is undercharacterized.

- **Solo vs coordination defense gap**: [[claim-cb-audit-sufficient-for-solo-exploits]] establishes CB + audit as fully sufficient for solo exploits, but [[claim-collusion-detection-is-binding-constraint-on-robustness]] shows the stack collapses to F grade without collusion detection against coordination attacks. [[claim-coordination-attacks-dominate-redteam-damage]] quantifies the gap: coordination attacks cause 52.6% of damage. The minimal secure stack is CB + audit + collusion detection, not CB + audit alone. This refines [[claim-governance-cost-paradox]]: some governance mechanisms (collusion detection) are genuinely cost-effective, while others (staking, high tax) are pure overhead.
- **Parameter sensitivity undermines CB sufficiency**: [[claim-audit-threshold-interaction-enables-dancing]] shows that lenient CB parameters (threshold 0.7, audit 10%) allow threshold dancing to succeed even against solo adversaries, contradicting the clean result in [[claim-cb-audit-sufficient-for-solo-exploits]]. This connects to [[claim-cb-null-may-reflect-design-limitation]]: if CB effectiveness is threshold-dependent, the binary on/off design understates its potential when well-calibrated and overstates it when lenient.
- **Dimensional blind spots in governance**: [[claim-cascade-mechanisms-ineffective-against-governance-gaming]] (vertical propagation fails against horizontal seam exploitation) and [[claim-collusion-detection-is-binding-constraint-on-robustness]] (individual-agent monitoring fails against coordination) reveal that each governance mechanism addresses one dimension of the threat space. No single mechanism or simple combination covers all dimensions. [[claim-spawn-infrastructure-may-amplify-sybil-surface]] adds identity verification as a third uncovered dimension.

<!-- topics: dashboard, vault -->
