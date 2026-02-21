---
description: Deep guide to /arscontexta:ask, /arscontexta:architect, /rethink, and /remember for SWARM vault evolution
type: manual
generated_from: "arscontexta-0.8.0"
---

# Meta-Skills

Meta-skills operate on the knowledge system itself, not on research content.

## /arscontexta:ask — Query Methodology

Queries two knowledge layers in parallel:
1. **Bundled research graph** (249 research claims about knowledge systems, cognitive science, agent cognition)
2. **Local vault/ops/methodology/** (SWARM-specific configuration rationale, operational learnings)

Use for:
- "Why does the vault use atomic claims instead of compound notes?"
- "How should I handle claims that span multiple domains?"
- "What should I do when confidence criteria aren't met?"
- "Why does the system require effect sizes with correction methods?"

Answers are grounded in specific research claims with direct application to SWARM context.

## /arscontexta:architect — Evolution Advice

Research-backed configuration advice when the system needs to change. Never auto-implements. Always proposes and explains.

Use when:
- The extraction pipeline consistently misses a type of finding
- The schema doesn't capture something important about SWARM experiments
- Navigation feels broken after the vault grows significantly
- You want to add a new extraction category

## /rethink — Challenge Assumptions

The scientific method applied to the SWARM Research OS itself. Triages accumulated observations and tensions, detects patterns, proposes methodology changes.

Triggers at: observations ≥ 10, tensions ≥ 5 (configured in ops/config.yaml).

Run modes:
- `/rethink` — full six-phase review
- `/rethink drift` — check behavioral drift only
- `/rethink triage` — triage observations only, no pattern detection
- `/rethink patterns` — pattern detection only (after existing triage)

## /remember — Capture Friction

Rule Zero: `vault/ops/methodology/` is the canonical spec. When something goes wrong, write it down immediately.

Use when:
- Extractor missed a category of findings it should have caught
- A claim was created with wrong confidence level
- You found a better way to cross-link governance claims to failure patterns
- Evidence provenance was incomplete and had to be reconstructed

Creates atomic notes in `vault/ops/observations/` (process) or `vault/ops/tensions/` (contradictions). These accumulate until `/rethink` reviews them.

---

See [[configuration]] for adjusting thresholds.

Topics:
- [[manual]]
