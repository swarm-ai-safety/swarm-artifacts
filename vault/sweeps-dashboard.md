---
description: "Interactive dashboard aggregating parameter sweep series and convergence status"
type: dashboard
cssclasses: ["dashboard"]
graph-group: dashboard
created: 2026-02-19
updated: 2026-02-19
---

# Sweeps dashboard aggregates 7 parameter sweep series

Each sweep summary note tracks a single parameter dimension across multiple runs, recording the values tested, convergence status, and key findings. This dashboard provides an at-a-glance view of all sweep series ordered by most recently updated.

## All sweeps by last update

```dataview
TABLE parameter, status, length(values_tested) as "Values", created, updated
FROM "vault/sweeps"
WHERE type = "sweep-summary"
SORT updated DESC
```

## Sweeps by parameter

```dataview
TABLE WITHOUT ID
  parameter AS "Parameter",
  length(rows) AS "Count"
FROM "vault/sweeps"
WHERE type = "sweep-summary"
GROUP BY parameter
SORT length(rows) DESC
```

## Sweeps by status

```dataview
TABLE WITHOUT ID
  status AS "Status",
  length(rows) AS "Count"
FROM "vault/sweeps"
WHERE type = "sweep-summary"
GROUP BY status
SORT length(rows) DESC
```

<!-- topics: dashboard, vault -->
