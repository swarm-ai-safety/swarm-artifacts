---
description: One claim rated "high" confidence draws from a single run, violating the replication criterion
type: observation
status: pending
created: 2026-02-21
source: /rethink phase 0 drift check
---

# One high-confidence claim lacks independent replication

`claim-tax-disproportionately-punishes-rlm-agents` is marked `confidence: high` but references only one run (`20260213-221500_collusion_tax_effect`) twice -- once for the RLM payoff metric and once for the honest payoff metric. These are two measurements from the same sweep, not independent replications.

The confidence criteria require: "Bonferroni-significant AND replicated across 2+ independent runs/seeds." The claim is Bonferroni-significant (p<1e-30, N=80) but unreplicated. It should be `confidence: medium` ("Nominally significant OR single-sweep support with BH correction").

## Recommended action

Downgrade `claim-tax-disproportionately-punishes-rlm-agents` from `confidence: high` to `confidence: medium` and add a note explaining the downgrade. Alternatively, replicate the finding in the baseline governance v2 sweep (which has RLM agent data) to justify keeping it at "high."

---

Topics:
- [[methodology]]
