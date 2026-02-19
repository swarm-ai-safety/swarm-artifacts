---
description: One sentence stating the claim as a testable proposition (~150 chars)
type: claim
status: active | weakened | superseded | retracted
confidence: high | medium | low | contested
domain: governance | topology | agent-behavior | decision-theory | collusion | memory | market | calibration | methodology

evidence:
  supporting:
    - run: "run_id"
      metric: "metric name"
      detail: "effect size, p-value, N, correction method"
  weakening: []
  boundary_conditions:
    - "known limits of generalizability"

sensitivity:
  topology: "how sensitive to topology changes"
  agent_count: "how sensitive to population size"
  governance_interaction: "how governance mechanisms interact"

supersedes: []
superseded_by: []
related_claims:
  - "claim-id"

created: YYYY-MM-DD
updated: YYYY-MM-DD

_schema:
  required: [description, type, status, confidence, domain, evidence, created]
  optional: [sensitivity, supersedes, superseded_by, related_claims, updated]
  enums:
    type: [claim]
    status: [active, weakened, superseded, retracted]
    confidence: [high, medium, low, contested]
    domain: [governance, topology, agent-behavior, decision-theory, collusion, memory, market, calibration, methodology]
  constraints:
    description: "max 200 chars, states the claim as a proposition, no trailing period"
    confidence: >
      high = Bonferroni-significant, replicated across seeds/configs.
      medium = nominally significant or single-sweep support.
      low = suggestive but underpowered or unreplicated.
      contested = conflicting evidence from different runs.
    evidence.supporting: "must have at least one entry with a valid run_id"
---

# prose-as-title stating the claim as a complete proposition

## Evidence summary

Present the evidence with visible reasoning. Show effect sizes, sample sizes,
correction methods. Use connective words: because, therefore, this suggests.

Link to experiment notes: [[experiment-run-id]]

## Boundary conditions

Known limits of generalizability. What topologies, agent counts, governance
configs, and agent types has this been tested under?

## Mechanism

Why does this happen? Propose or cite the causal mechanism.

## Open questions

What would strengthen, weaken, or supersede this claim?
What's the most decisive next experiment?

## Paper

Reference to published paper if applicable.

---

Topics:
- [[_index]]
