---
description: "Dataview dashboard: governance mechanisms with linked claims and evidence"
type: dashboard
cssclasses:
  - dashboard
created: 2026-02-19
---

# Governance Mechanisms Dashboard

## All Mechanisms
```dataview
TABLE WITHOUT ID
  file.link AS "Mechanism",
  status AS "Status",
  description AS "Description"
FROM "vault/governance"
SORT file.name ASC
```

## Claims Linked to Governance
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  confidence AS "Confidence",
  status AS "Status"
FROM "vault/claims"
WHERE type = "claim" AND domain = "governance"
SORT choice(confidence, "high", 0, choice(confidence, "medium", 1, 2)) ASC
```

## Governance Failure Patterns
```dataview
TABLE WITHOUT ID
  file.link AS "Pattern",
  severity AS "Severity"
FROM "vault/failures"
WHERE type = "failure-pattern" AND contains(tags, "governance")
SORT file.name ASC
```
