---
name: remember
description: Capture methodology friction, process corrections, and operational learnings for the SWARM vault. Rule Zero — methodology notes are the spec; when something goes wrong, write it down so the system learns. Triggers on "/remember", "capture friction", "log this correction", "the system did X wrong".
user-invocable: true
allowed-tools: Read, Write, Glob
context: fork
---

## EXECUTE NOW

**Target: $ARGUMENTS**

- If target describes a friction, mistake, or correction: capture it immediately
- If target is empty: ask "What happened? What should the system do differently?"

---

# Remember

Capture operational friction so the SWARM vault learns from experience.

## Rule Zero

`vault/ops/methodology/` is the canonical specification of how this system operates. When behavior diverges from methodology, or when methodology should change, write it down here. `/rethink` reviews these notes. `/arscontexta:architect` reasons about patterns. Together they prevent drift.

## What to Capture

- **Process mistakes**: claim created without run_id provenance, confidence assigned without statistical backing
- **Friction patterns**: extraction consistently missing a category of findings
- **Corrections**: a claim was wrong, here's why and what the correct interpretation is
- **Discovery**: found a better way to cross-link evidence, here's the pattern

## Observation Note Format

Create in `vault/ops/observations/`:

```markdown
---
description: [one sentence: what happened]
category: methodology | process | friction | surprise | quality
observed: YYYY-MM-DD
status: pending
---

# [prose-as-title: what the system did or failed to do]

[Body: what happened, what should have happened, what the gap is]

---

Topics:
- [[methodology]]
```

## Tension Note Format (when content contradicts existing claims)

Create in `vault/ops/tensions/`:

```markdown
---
description: [one sentence: what contradicts what]
observed: YYYY-MM-DD
involves:
  - "[[claim A]]"
  - "[[claim B]]"
status: pending
---

# [prose-as-title: the conflict]

[Body: what evidence supports each side, why this is unresolved]

---

Topics:
- [[methodology]]
```

After capturing, the note will be picked up by `/rethink` when observation count reaches threshold (currently 10).
