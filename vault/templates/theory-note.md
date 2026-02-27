---
description: One sentence stating the theory as a testable proposition (~150 chars)
type: theory
status: proposed | supported | contested | superseded
scope: "Domain and conditions under which this theory applies"

constituent_claims:
  - claim: "claim-id-1"
    role: premise | prediction | boundary | evidence
  - claim: "claim-id-2"
    role: premise | prediction | boundary | evidence

open_predictions:
  - "prediction-id"

created: YYYY-MM-DD
updated: YYYY-MM-DD

_schema:
  required: [description, type, status, scope, constituent_claims, created]
  optional: [open_predictions, updated]
  enums:
    type: [theory]
    status: [proposed, supported, contested, superseded]
    role: [premise, prediction, boundary, evidence]
  constraints:
    description: "max 200 chars, states the theory as a proposition, no trailing period"
    constituent_claims: "minimum 2 entries, each with claim ID and role"
    scope: "must specify domain, topology, agent types, or other applicability conditions"
---

# prose-as-title stating the theory as a complete proposition

## Constituent claims

| Claim | Role | Confidence |
|-------|------|------------|
| [[claim-id-1]] | premise | high |
| [[claim-id-2]] | evidence | medium |

## Scope & boundary conditions

Under what conditions does this theory hold? Which topologies, agent counts,
governance configs, and agent types has it been validated for?

## Thesis

Why do these claims compose into a coherent theory? What's the unifying mechanism
or principle that connects them?

## Predictions

Testable consequences of this theory. Each should link to a prediction note
or become one.

1. If [condition], then [outcome] — [[prediction-id]]

## Falsification criteria

What evidence would refute this theory? Be specific about metrics, thresholds,
and experimental designs.

## Open questions

What would strengthen or extend this theory? Where are the gaps?

---

Topics:
- [[_index]]
