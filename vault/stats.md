---
description: "Real-time vault health snapshot with counts, breakdowns, and quality checks"
type: dashboard
cssclasses: ["dashboard"]
graph-group: dashboard
created: 2026-02-19
updated: 2026-02-19
---

# Vault statistics provide a real-time health snapshot

This dashboard gives a bird's-eye view of vault contents: note counts by type, claim confidence distribution, recently created notes, and quality checks for missing metadata.

## Note counts by type

```dataviewjs
const types = ["claim", "experiment", "sweep-summary", "failure-pattern", "governance", "method", "topology", "moc", "dashboard"];
const rows = [];
for (const t of types) {
    const count = dv.pages('"vault"').where(p => p.type === t).length;
    if (count > 0) rows.push([t, count]);
}
rows.sort((a, b) => b[1] - a[1]);
dv.table(["Type", "Count"], rows);
```

## Claims by confidence breakdown

```dataviewjs
const levels = ["high", "medium", "low", "contested"];
const rows = levels.map(level => {
    const count = dv.pages('"vault/claims"').where(p => p.type === "claim" && p.confidence === level).length;
    return [level, count];
}).filter(r => r[1] > 0);
dv.table(["Confidence", "Count"], rows);
```

## 10 most recently created notes

```dataview
TABLE type, created
FROM "vault"
WHERE created AND !contains(file.path, "templates")
SORT created DESC
LIMIT 10
```

## Notes missing tags (quality check)

```dataview
TABLE type, file.folder as "Folder"
FROM "vault"
WHERE (!tags OR length(tags) = 0)
  AND !contains(file.path, "templates")
  AND !contains(file.path, "dashboards")
  AND type != "dashboard"
  AND type != "moc"
SORT file.name ASC
```

## Notes missing description

```dataview
TABLE type, file.folder as "Folder"
FROM "vault"
WHERE !description
  AND !contains(file.path, "templates")
  AND !contains(file.path, "dashboards")
SORT file.name ASC
```

<!-- topics: dashboard, vault -->
