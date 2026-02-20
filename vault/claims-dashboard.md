---
description: "Interactive dashboard of all claims by confidence, domain, and evidence status"
type: dashboard
cssclasses: ["dashboard"]
graph-group: dashboard
created: 2026-02-19
updated: 2026-02-19
---

# Claims dashboard tracks 12 active findings across 4 confidence levels

This dashboard surfaces every claim in the vault, sorted by confidence so the strongest findings appear first. Each row links to the claim card and shows how many supporting evidence entries back it.

## All claims by confidence

```dataview
TABLE confidence, domain, status, length(evidence.supporting) as "Evidence", created
FROM "vault/claims"
WHERE type = "claim"
SORT choice(confidence = "high", 1, choice(confidence = "medium", 2, choice(confidence = "low", 3, 4))) ASC
```

## Claims by domain

```dataview
TABLE WITHOUT ID
  domain AS "Domain",
  length(rows) AS "Count"
FROM "vault/claims"
WHERE type = "claim"
GROUP BY domain
SORT length(rows) DESC
```

## Confidence breakdown

```dataview
TABLE WITHOUT ID
  confidence AS "Confidence",
  length(rows) AS "Count"
FROM "vault/claims"
WHERE type = "claim"
GROUP BY confidence
SORT choice(confidence = "high", 1, choice(confidence = "medium", 2, choice(confidence = "low", 3, 4))) ASC
```

## Contested or weakened claims

```dataview
TABLE confidence, domain, status
FROM "vault/claims"
WHERE type = "claim" AND (status = "weakened" OR status = "contested" OR confidence = "contested")
SORT file.name ASC
```

<!-- topics: dashboard, vault -->
