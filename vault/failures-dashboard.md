---
description: "Interactive dashboard cataloging attack patterns and failure modes by severity"
type: dashboard
cssclasses: ["dashboard"]
graph-group: dashboard
created: 2026-02-19
updated: 2026-02-19
---

# Failures dashboard catalogs 8 attack patterns by severity

This dashboard surfaces every named failure pattern from red-team evaluations, sorted by severity so critical vulnerabilities appear first. Each row shows the attack vector, affected governance mechanisms, and current mitigation status.

## All failure patterns by severity

```dataview
TABLE severity, attack_vector, join(affected_mechanisms, ", ") as "Affected", status
FROM "vault/failures"
WHERE type = "failure-pattern"
SORT choice(severity = "critical", 1, choice(severity = "high", 2, choice(severity = "medium", 3, 4))) ASC
```

## Failures by severity

```dataview
TABLE WITHOUT ID
  severity AS "Severity",
  length(rows) AS "Count"
FROM "vault/failures"
WHERE type = "failure-pattern"
GROUP BY severity
SORT choice(severity = "critical", 1, choice(severity = "high", 2, choice(severity = "medium", 3, 4))) ASC
```

## Unmitigated failures

```dataview
TABLE severity, attack_vector, join(affected_mechanisms, ", ") as "Affected"
FROM "vault/failures"
WHERE type = "failure-pattern" AND status != "mitigated"
SORT choice(severity = "critical", 1, choice(severity = "high", 2, choice(severity = "medium", 3, 4))) ASC
```

<!-- topics: dashboard, vault -->
