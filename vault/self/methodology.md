---
description: How I process, connect, and maintain the SWARM knowledge graph
type: moc
---

# methodology

## Principles

- **Prose-as-title**: Every claim is a complete proposition. Test: "this claim argues that [title]"
- **Wiki-links as reasoning**: `since [[circuit breakers dominate]]...` — the link IS the argument
- **Topic maps as attention hubs**: _index.md → dashboards → claims. Navigation not search.
- **Pipeline discipline**: extract findings → cross-link evidence → validate provenance → update prior claims
- **Capture fast, synthesize slow**: run data goes to runs/; synthesis happens during processing

## Processing Pipeline

### 1. Extract Findings (`/extract`)
Read source (experiment summary, sweep results, red-team report). Hunt for:
- Governance claims with effect sizes
- Adversarial patterns with success rates
- Parameter sensitivity findings (phase transitions, welfare cliffs)
- Mechanism interaction effects
- Open research questions
- Failure modes with severity and evasion rates

Every extraction requires: run_id provenance, effect size with correction method, boundary conditions.

### 2. Cross-Link Evidence (`/cross-link`)
Find connections between new claims and existing vault content. Use dual discovery:
- Browse relevant topic maps (governance, topology, failures, etc.)
- Run semantic search (`/arscontexta:ask` or qmd) for conceptual neighbors

Every connection must pass the articulation test: "[[A]] connects to [[B]] because [specific reason]"

### 3. Update Prior Claims (`/update`)
When new evidence bears on existing claims:
- Strengthen supporting evidence entries
- Add boundary conditions that limit generalizability
- Escalate weakening evidence — update status if warranted
- Never silently delete; always document the lifecycle change

### 4. Validate Provenance (`/validate`)
Before a claim is considered complete:
- Every evidence entry has a real run_id in runs/
- Effect size reported with correction method
- Confidence level matches statistical criteria
- Boundary conditions documented
- Schema passes _schema block constraints

## Operational Memory (`/remember`)

Invoke `/remember` during processing sessions when:
- A judgment call is made (e.g., choosing between confidence levels, deciding to merge vs split claims)
- A tool or pipeline step behaves unexpectedly
- A pattern is noticed but not yet formalized as a claim
- A methodological friction point is encountered (e.g., schema doesn't fit a finding type)

This feeds the `/rethink` maintenance loop. Without `/remember` invocations, the observation pipeline has no input and system evolution stalls.

## Maintenance Triggers

- Pending observations ≥ 10 → run /rethink
- Pending tensions ≥ 5 → run /rethink
- Claim not updated in 30+ days → flag for /update pass
- `python scripts/vault-health.py` → comprehensive audit

---

Topics:
- [[identity]]
