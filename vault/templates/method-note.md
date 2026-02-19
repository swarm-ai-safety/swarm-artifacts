---
description: One sentence explaining what this method does and when to use it (~150 chars)
type: method
status: active | experimental | deprecated
category: statistical | simulation | analysis | visualization | governance-design

created: YYYY-MM-DD
updated: YYYY-MM-DD

_schema:
  required: [description, type, status, category, created]
  optional: [updated]
  enums:
    type: [method]
    status: [active, experimental, deprecated]
    category: [statistical, simulation, analysis, visualization, governance-design]
  constraints:
    description: "max 200 chars, no trailing period"
---

# prose-as-title describing the method as a reusable practice

## What it does

Describe the method: inputs, outputs, when to apply it.

## Why it matters

What problem does this method solve? What goes wrong without it?
Reference cognitive science or statistical methodology where relevant.

## How to apply it

Step-by-step procedure. Reference scripts, schemas, or SWARM commands.

```bash
# example command or script invocation
```

## Assumptions and limitations

What does this method assume? When does it break down?

## Evidence of effectiveness

Which experiments have used this method? What outcomes validated it?

- [[experiment-run-id]] — where this method was applied
- [[claim-id]] — claim that depends on this method

---

Topics:
- [[_index]]
