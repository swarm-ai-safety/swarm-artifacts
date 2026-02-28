---
description: Claims referencing only one run cannot exceed medium confidence
type: directive
status: active
created: 2026-02-27
rationale: Recurring confidence drift — 2 consecutive rethink sessions found single-run claims rated high
---

# Single-run claims cannot exceed medium confidence

## Directive

At extraction time, before assigning `confidence: high` to any claim, verify:

1. The claim references **2 or more independent runs** (different run_ids, not just different seeds within one sweep)
2. The effect is **Bonferroni-significant** across those runs

If either condition fails, the maximum confidence is `medium`.

## Rationale

The confidence criteria table requires "Bonferroni-significant AND replicated across ≥2 independent runs/seeds" for high confidence. However, strong effect sizes in single-run analyses (e.g., d > 2.0) tempt extractors to rate high without checking replication.

This pattern was detected in 2 consecutive rethink sessions (2026-02-21 and 2026-02-27), affecting 3 claims total:
- claim-tax-disproportionately-punishes-rlm-agents (downgraded 2026-02-21)
- claim-ldt-agents-dominate-all-agent-types-in-mixed-populations (downgraded 2026-02-27)
- claim-rlm-agents-exploit-governance-lag-via-strategic-depth-not-evasion (downgraded 2026-02-27)

## Checklist for extractors

Before writing `confidence: high`:
- [ ] Count distinct run_ids in evidence.supporting — is it ≥ 2?
- [ ] Are these truly independent runs (not seeds within the same sweep)?
- [ ] Is the effect Bonferroni-significant in each run independently?

If any box is unchecked → use `confidence: medium` at most.

---

Topics:
- [[_index]]
