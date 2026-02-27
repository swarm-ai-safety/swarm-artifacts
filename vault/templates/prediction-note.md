---
description: One sentence summarizing the prediction (~150 chars)
type: prediction
status: open | confirmed | refuted | expired
source_claim: "claim-id or theory-id that generated this prediction"
hypothesis: "Precise testable statement: if X then Y"
test_protocol: "What experiment would confirm or refute this"

resolution:
  run: "run_id"
  outcome: confirmed | refuted | inconclusive
  detail: "effect size, p-value, interpretation"

created: YYYY-MM-DD
updated: YYYY-MM-DD

_schema:
  required: [description, type, status, source_claim, hypothesis, created]
  optional: [test_protocol, resolution, updated]
  enums:
    type: [prediction]
    status: [open, confirmed, refuted, expired]
    outcome: [confirmed, refuted, inconclusive]
  constraints:
    description: "max 200 chars, no trailing period"
    hypothesis: "must be a precise if-then statement"
    source_claim: "must reference a valid claim or theory ID"
---

# prose-as-title stating the prediction as a testable proposition

## Source

Derived from [[source-claim-or-theory]].

## Hypothesis

State the precise if-then prediction. What variable is manipulated?
What outcome is expected? What magnitude?

## Test protocol

What experiment would test this? Specify:
- Scenario and parameters
- Number of seeds needed for power
- Key metric and threshold
- Statistical test and correction method

## Resolution

_Fill this section when the prediction is tested._

| Field | Value |
|-------|-------|
| Run | `run_id` |
| Outcome | confirmed / refuted / inconclusive |
| Detail | effect size, p-value, interpretation |

## Implications

What does confirmation or refutation mean for the source claim or theory?

---

Topics:
- [[_index]]
