---
description: One sentence on what this governance mechanism does and when it matters (~150 chars)
type: governance
status: active | experimental | deprecated
mechanism: circuit-breaker | transaction-tax | staking | reputation-decay | audit | collusion-detection | rate-limit | vote-normalization

parameters:
  - name: "parameter_name"
    type: float | int | bool
    default: null
    range: "description of valid range"

created: YYYY-MM-DD
updated: YYYY-MM-DD

_schema:
  required: [description, type, status, mechanism, created]
  optional: [parameters, updated]
  enums:
    type: [governance]
    status: [active, experimental, deprecated]
    mechanism: [circuit-breaker, transaction-tax, staking, reputation-decay, audit, collusion-detection, rate-limit, vote-normalization]
  constraints:
    description: "max 200 chars, no trailing period"
---

# prose-as-title describing the mechanism's role in the governance stack

## How it works

Describe the mechanism: what it monitors, what triggers it, what it does.
Reference the SWARM implementation where relevant.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `param_name` | float | 0.05 | what changing it does |

## Evidence

What runs have tested this mechanism? What claims does it support?

- [[claim-id]] — relationship to the claim
- [[experiment-run-id]] — key experiment

## Interactions

How does this mechanism interact with others?
Which combinations are synergistic vs. antagonistic?

## Known failure modes

When does this mechanism fail? What adversarial strategies exploit it?

- [[failure-pattern-id]] — known vulnerability

## Open questions

What's untested? What parameter ranges need exploration?

---

Topics:
- [[_index]]
