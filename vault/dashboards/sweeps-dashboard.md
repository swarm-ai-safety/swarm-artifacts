---
description: "Dataview dashboard: parameter sweep series with convergence status"
type: dashboard
cssclasses:
  - dashboard
created: 2026-02-19
---

# Sweeps Dashboard

## All Sweep Series
```dataview
TABLE WITHOUT ID
  file.link AS "Sweep",
  parameter AS "Parameter",
  status AS "Status",
  description AS "Summary"
FROM "sweeps"
WHERE type = "sweep-summary"
SORT file.name ASC
```

## Active Sweeps
```dataview
TABLE WITHOUT ID
  file.link AS "Sweep",
  parameter AS "Parameter",
  values_tested AS "Values Tested"
FROM "sweeps"
WHERE type = "sweep-summary" AND status = "active"
SORT file.name ASC
```

## Governance Parameter Sweeps
```dataview
TABLE WITHOUT ID
  file.link AS "Sweep",
  parameter AS "Parameter",
  description AS "Finding"
FROM "sweeps"
WHERE type = "sweep-summary" AND contains(parameter, "governance")
SORT file.name ASC
```
