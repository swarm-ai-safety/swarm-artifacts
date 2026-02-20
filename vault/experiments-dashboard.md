---
description: "Interactive dashboard indexing all experiment notes by type, run ID, and tags"
type: dashboard
cssclasses: ["dashboard"]
graph-group: dashboard
created: 2026-02-19
updated: 2026-02-19
---

# Experiments dashboard indexes 110 notes across 5 experiment types

This dashboard lists every auto-generated experiment note in the vault, grouped by experiment type. Each note corresponds to a single run in `runs/` and carries the run ID, creation date, and semantic tags mined from the run content.

## All experiments by date

```dataview
TABLE experiment_type, run_id, created, join(tags, ", ") as "Tags"
FROM "vault/experiments"
WHERE type = "experiment"
SORT created DESC
```

## Experiments by type

```dataview
TABLE WITHOUT ID
  experiment_type AS "Type",
  length(rows) AS "Count"
FROM "vault/experiments"
WHERE type = "experiment"
GROUP BY experiment_type
SORT length(rows) DESC
```

## Recent experiments (last 20)

```dataview
TABLE experiment_type, run_id, created
FROM "vault/experiments"
WHERE type = "experiment"
SORT created DESC
LIMIT 20
```

<!-- topics: dashboard, vault -->
