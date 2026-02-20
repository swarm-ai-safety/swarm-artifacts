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

<!-- topics: dashboard, vault -->
