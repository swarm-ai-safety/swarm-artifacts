---
description: "Dataview dashboard: vault-wide statistics and health metrics"
type: dashboard
cssclasses:
  - dashboard
created: 2026-02-19
---

# Vault Statistics

## Note Counts by Type
```dataview
TABLE WITHOUT ID
  type AS "Type",
  length(rows) AS "Count"
FROM "vault"
WHERE type
GROUP BY type
SORT length(rows) DESC
```

## Tag Frequency (Top 20)
```dataview
TABLE WITHOUT ID
  tag AS "Tag",
  length(rows) AS "Used In"
FROM "vault"
FLATTEN tags AS tag
WHERE tag
GROUP BY tag
SORT length(rows) DESC
LIMIT 20
```

## Orphan Notes (no inlinks or outlinks)
```dataview
TABLE WITHOUT ID
  file.link AS "Note",
  type AS "Type",
  file.folder AS "Folder"
FROM "vault"
WHERE length(file.inlinks) = 0 AND length(file.outlinks) = 0
  AND !contains(file.path, "templates")
  AND !contains(file.path, "dashboards")
SORT file.name ASC
```

## Recently Updated
```dataview
TABLE WITHOUT ID
  file.link AS "Note",
  type AS "Type",
  updated AS "Updated"
FROM "vault"
WHERE updated
SORT updated DESC
LIMIT 15
```
