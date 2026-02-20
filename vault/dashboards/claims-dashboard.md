---
description: "Dataview dashboard: all research claims by confidence and domain"
type: dashboard
cssclasses:
  - dashboard
created: 2026-02-19
---

# Claims Dashboard

## Active Claims by Confidence

### High Confidence
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  domain AS "Domain",
  status AS "Status",
  evidence.supporting.length AS "Evidence"
FROM "vault/claims"
WHERE type = "claim" AND confidence = "high" AND status = "active"
SORT file.name ASC
```

### Medium Confidence
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  domain AS "Domain",
  status AS "Status",
  evidence.supporting.length AS "Evidence"
FROM "vault/claims"
WHERE type = "claim" AND confidence = "medium" AND status = "active"
SORT file.name ASC
```

### Low Confidence
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  domain AS "Domain",
  status AS "Status",
  evidence.supporting.length AS "Evidence"
FROM "vault/claims"
WHERE type = "claim" AND confidence = "low" AND status = "active"
SORT file.name ASC
```

## Claims by Domain
```dataview
TABLE WITHOUT ID
  domain AS "Domain",
  length(rows) AS "Count"
FROM "vault/claims"
WHERE type = "claim"
GROUP BY domain
SORT length(rows) DESC
```

## Contested or Weakened
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  confidence AS "Confidence",
  domain AS "Domain"
FROM "vault/claims"
WHERE type = "claim" AND (status = "weakened" OR confidence = "contested")
SORT file.name ASC
```
