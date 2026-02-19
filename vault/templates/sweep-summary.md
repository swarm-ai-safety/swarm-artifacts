---
description: One sentence summarizing the sweep series and its convergence status (~150 chars)
type: sweep-summary
status: active | superseded
parameter: "dotted.parameter.name"
values_tested: []

created: YYYY-MM-DD
updated: YYYY-MM-DD

_schema:
  required: [description, type, status, parameter, created]
  optional: [values_tested, updated]
  enums:
    type: [sweep-summary]
    status: [active, superseded]
  constraints:
    description: "max 200 chars, no trailing period"
    parameter: "dotted path matching SWARM config, e.g. governance.transaction_tax_rate"
---

# prose-as-title describing what this sweep series has established

## Runs in this sweep

| Run ID | Date | Seeds | Configs | Key finding |
|--------|------|-------|---------|-------------|
| [[experiment-run-id]] | YYYY-MM-DD | N | N | one-line result |

## Convergence

Has the finding stabilized across runs? Are confidence intervals narrowing?
Has the effect direction remained consistent?

## Phase transition surface

Where are the critical thresholds? What parameter values produce qualitative
changes in behavior?

## Claims supported

- [[claim-id]] — how the sweep series supports this claim

## Next decisive experiment

What parameter range, topology, or agent mix would most usefully extend
this sweep? What would falsify the current interpretation?

---

Topics:
- [[_index]]
