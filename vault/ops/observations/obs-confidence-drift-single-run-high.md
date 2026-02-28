---
description: One claim rated "high" confidence draws from a single run, violating the replication criterion
type: observation
status: active
created: 2026-02-21
source: /rethink phase 0 drift check
---

# One high-confidence claim lacks independent replication

`claim-tax-disproportionately-punishes-rlm-agents` is marked `confidence: high` but references only one run (`20260213-221500_collusion_tax_effect`) twice -- once for the RLM payoff metric and once for the honest payoff metric. These are two measurements from the same sweep, not independent replications.

The confidence criteria require: "Bonferroni-significant AND replicated across 2+ independent runs/seeds." The claim is Bonferroni-significant (p<1e-30, N=80) but unreplicated. It should be `confidence: medium` ("Nominally significant OR single-sweep support with BH correction").

## History

- 2026-02-21: Original finding. `claim-tax-disproportionately-punishes-rlm-agents` flagged.
- 2026-02-27: Original claim fixed (downgraded to medium). Two new violations of the same pattern found:
  - `claim-ldt-agents-dominate-all-agent-types-in-mixed-populations` — single run, high confidence
  - `claim-rlm-agents-exploit-governance-lag-via-strategic-depth-not-evasion` — single run, high confidence

## Recommended action

Downgrade the two newly flagged claims from `confidence: high` to `confidence: medium`. This is a recurring pattern — see Proposal 3 in [[obs-rethink-session-2026-02-27]] for a process-level fix.

---

Topics:
- [[methodology]]
