---
description: "Dataview dashboard: experiment notes by type, status, and tags"
type: dashboard
cssclasses:
  - dashboard
created: 2026-02-19
---

# Experiments Dashboard

## By Experiment Type

### Sweeps
```dataview
TABLE WITHOUT ID
  file.link AS "Experiment",
  description AS "Description",
  tags AS "Tags"
FROM "vault/experiments"
WHERE contains(cssclasses, "experiment-sweep")
SORT file.name DESC
LIMIT 20
```

### Studies
```dataview
TABLE WITHOUT ID
  file.link AS "Experiment",
  description AS "Description",
  tags AS "Tags"
FROM "vault/experiments"
WHERE contains(cssclasses, "experiment-study")
SORT file.name DESC
LIMIT 20
```

### Red Team
```dataview
TABLE WITHOUT ID
  file.link AS "Experiment",
  description AS "Description",
  tags AS "Tags"
FROM "vault/experiments"
WHERE contains(cssclasses, "experiment-redteam")
SORT file.name DESC
LIMIT 20
```

### Single Runs
```dataview
TABLE WITHOUT ID
  file.link AS "Experiment",
  description AS "Description",
  tags AS "Tags"
FROM "vault/experiments"
WHERE contains(cssclasses, "experiment-single")
SORT file.name DESC
LIMIT 20
```

## Recent Experiments (last 20)
```dataview
TABLE WITHOUT ID
  file.link AS "Experiment",
  type AS "Type",
  created AS "Date"
FROM "vault/experiments"
SORT created DESC
LIMIT 20
```

## Experiments by Tag
```dataview
TABLE WITHOUT ID
  tag AS "Tag",
  length(rows) AS "Count"
FROM "vault/experiments"
FLATTEN tags AS tag
GROUP BY tag
SORT length(rows) DESC
LIMIT 15
```
