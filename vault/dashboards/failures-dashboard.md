---
description: "Dataview dashboard: vulnerability and failure patterns from red-team evaluations"
type: dashboard
cssclasses:
  - dashboard
created: 2026-02-19
---

# Failure Patterns Dashboard

## By Severity
```dataview
TABLE WITHOUT ID
  file.link AS "Pattern",
  severity AS "Severity",
  status AS "Status",
  description AS "Description"
FROM "failures"
WHERE type = "failure-pattern"
SORT choice(severity, "critical", 0, choice(severity, "high", 1, choice(severity, "medium", 2, 3))) ASC
```

## Critical Vulnerabilities
```dataview
LIST description
FROM "failures"
WHERE type = "failure-pattern" AND severity = "critical"
```

## Active vs Mitigated
```dataview
TABLE WITHOUT ID
  status AS "Status",
  length(rows) AS "Count"
FROM "failures"
WHERE type = "failure-pattern"
GROUP BY status
```
