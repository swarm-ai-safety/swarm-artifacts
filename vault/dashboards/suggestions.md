---
description: "Dataview dashboard: surfaces research gaps, stale claims, unlinked experiments, and next steps"
type: dashboard
cssclasses:
  - dashboard
created: 2026-02-19
---

# Suggestions

What to work on next, surfaced automatically from vault state.

---

## Needs Replication

Claims with fewer than 2 supporting runs — single-source evidence is fragile.

```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  confidence AS "Confidence",
  domain AS "Domain",
  length(evidence.supporting) AS "Runs"
FROM "claims"
WHERE type = "claim"
  AND status = "active"
  AND (!evidence.supporting OR length(evidence.supporting) < 2)
SORT confidence ASC
```

> **Action**: Run additional seeds or scenarios to strengthen these claims.

---

## Stale Claims

Active claims not updated in the last 14 days — may need revisiting with new evidence.

```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  confidence AS "Confidence",
  updated AS "Last Updated",
  domain AS "Domain"
FROM "claims"
WHERE type = "claim"
  AND status = "active"
  AND updated
  AND date(updated) < date(today) - dur(14 days)
SORT updated ASC
```

> **Action**: Check if new runs have been added that support or weaken these claims.

---

## Untested Boundary Conditions

Claims that document boundary conditions — each is a candidate for a targeted experiment.

```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  evidence.boundary_conditions AS "Known Limits"
FROM "claims"
WHERE type = "claim"
  AND status = "active"
  AND evidence.boundary_conditions
  AND length(evidence.boundary_conditions) > 0
SORT confidence DESC
```

> **Action**: Design experiments that push beyond these known limits.

---

## Unlinked Experiments

Recent experiment notes that don't appear in any claim's supporting evidence — potential undiscovered findings.

```dataview
TABLE WITHOUT ID
  file.link AS "Experiment",
  experiment_type AS "Type",
  created AS "Date"
FROM "experiments"
WHERE type = "experiment"
  AND length(file.inlinks) = 0
SORT created DESC
LIMIT 20
```

> **Action**: Review these runs for findings worth promoting to claims.

---

## Low-Confidence Claims

Active claims marked low confidence — prime candidates for strengthening or retiring.

```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  domain AS "Domain",
  length(evidence.supporting) AS "Supporting Runs",
  length(evidence.weakening) AS "Weakening Runs"
FROM "claims"
WHERE type = "claim"
  AND status = "active"
  AND confidence = "low"
SORT file.name ASC
```

> **Action**: Either run targeted experiments to raise confidence, or mark as `retracted` if unsupported.

---

## Potential Contradictions

Claims in the same domain — review pairs for opposing conclusions.

### Governance Domain
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  confidence AS "Confidence",
  description AS "Finding"
FROM "claims"
WHERE type = "claim"
  AND domain = "governance"
  AND status = "active"
SORT confidence DESC
```

### Collusion Domain
```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  confidence AS "Confidence",
  description AS "Finding"
FROM "claims"
WHERE type = "claim"
  AND domain = "collusion"
  AND status = "active"
SORT confidence DESC
```

> **Action**: Look for pairs where one claim says X helps and another says X hurts. Design a study to resolve the contradiction.

---

## Weakened or Contested

Claims with weakening evidence or contested confidence — active debates needing resolution.

```dataview
TABLE WITHOUT ID
  file.link AS "Claim",
  confidence AS "Confidence",
  status AS "Status",
  length(evidence.weakening) AS "Weakening Runs"
FROM "claims"
WHERE type = "claim"
  AND (status = "weakened" OR confidence = "contested"
    OR (evidence.weakening AND length(evidence.weakening) > 0))
SORT file.name ASC
```

> **Action**: Design a decisive experiment to resolve the dispute.

---

## Orphan Notes

Notes with no incoming or outgoing links — disconnected from the knowledge graph.

```dataview
TABLE WITHOUT ID
  file.link AS "Note",
  type AS "Type",
  file.folder AS "Folder"
FROM ""
WHERE length(file.inlinks) = 0
  AND length(file.outlinks) = 0
  AND type != "dashboard"
  AND !contains(file.path, "templates")
SORT file.folder ASC
```

> **Action**: Add wikilinks to connect these to related claims, experiments, or governance notes.

---

## Sweep Series Without Claims

Sweep summaries that aren't referenced by any claim — findings may not have been written up.

```dataview
TABLE WITHOUT ID
  file.link AS "Sweep",
  parameter AS "Parameter",
  status AS "Status"
FROM "sweeps"
WHERE type = "sweep-summary"
  AND length(file.inlinks) = 0
SORT file.name ASC
```

> **Action**: Review sweep results and create claim cards for significant findings.

---

## Critical Failures Still Active

Unmitigated critical and high-severity vulnerabilities — highest priority for governance improvements.

```dataview
TABLE WITHOUT ID
  file.link AS "Pattern",
  severity AS "Severity",
  status AS "Status"
FROM "failures"
WHERE type = "failure-pattern"
  AND status = "active"
  AND (severity = "critical" OR severity = "high")
SORT choice(severity = "critical", 0, 1) ASC
```

> **Action**: Design governance interventions targeting these specific attack vectors.
