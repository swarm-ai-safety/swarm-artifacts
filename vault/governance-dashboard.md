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

<!-- topics: dashboard, vault -->
