---
description: "Dataview dashboard: traces evidence chains from claims through experiments to runs"
type: dashboard
cssclasses:
  - dashboard
created: 2026-02-19
---

# Evidence Trail

Traces the chain: **Claim** → **Supporting Runs** → **Experiment Notes**

## Claims with Supporting Evidence
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  confidence AS "Confidence",
  length(evidence.supporting) AS "# Runs",
  map(evidence.supporting, (e) => e.run) AS "Run IDs"
FROM "vault/claims"
WHERE type = "claim" AND evidence.supporting
SORT choice(confidence, "high", 0, choice(confidence, "medium", 1, 2)) ASC
```

## Claims Missing Evidence
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  confidence AS "Confidence",
  domain AS "Domain"
FROM "vault/claims"
WHERE type = "claim" AND (!evidence.supporting OR length(evidence.supporting) = 0)
```

## Boundary Conditions
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  evidence.boundary_conditions AS "Known Limits"
FROM "vault/claims"
WHERE type = "claim" AND evidence.boundary_conditions
```

## Methods Used Across Claims
```dataview
TABLE WITHOUT ID
  file.link AS "Method",
  length(file.inlinks) AS "Referenced By"
FROM "vault/methods"
SORT length(file.inlinks) DESC
```
