---
description: "Traces evidence chains from claims through run IDs to experiment notes"
type: dashboard
cssclasses: ["dashboard"]
graph-group: dashboard
created: 2026-02-19
updated: 2026-02-19
---

# Evidence trail traces chains from claims through runs to experiment notes

This dashboard iterates over every claim in the vault and extracts its supporting evidence entries. For each entry it displays the run ID, metric, and a detail snippet, making it easy to follow the provenance chain from finding back to raw experiment data.

## Claim evidence chains

```dataviewjs
const claims = dv.pages('"vault/claims"').where(p => p.type === "claim");
for (const claim of claims) {
    const supporting = claim.evidence?.supporting || [];
    if (supporting.length > 0) {
        dv.header(3, claim.file.link);
        dv.paragraph(`**Confidence:** ${claim.confidence} | **Domain:** ${claim.domain} | **Status:** ${claim.status}`);
        const rows = supporting.map(e => {
            const detail = e.detail ? (e.detail.length > 80 ? e.detail.substring(0, 80) + "..." : e.detail) : "—";
            return [e.run, e.metric, detail];
        });
        dv.table(["Run", "Metric", "Detail"], rows);
    }
}
```

## Claims without evidence

```dataview
TABLE confidence, domain, status
FROM "vault/claims"
WHERE type = "claim" AND (!evidence OR !evidence.supporting OR length(evidence.supporting) = 0)
SORT file.name ASC
```

<!-- topics: dashboard, vault -->
