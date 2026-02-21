---
description: Human-readable task board — pipeline tasks and maintenance items
type: tasks
updated: 2026-02-20
---

# Task Board

Machine-readable queue: `vault/ops/queue/queue.json`

## Active

(none yet — run /extract on a run folder to start)

## Pending

(none yet)

## Completed

(archived in vault/ops/queue/archive/)

---

### How tasks flow

1. `/extract [run-folder]` — extract findings from an experiment run → creates claim tasks
2. `/cross-link [claim]` — find connections between claims → advances phase
3. `/update [claim]` — update prior claims with new context → advances phase
4. `/validate [claim]` — validate provenance and schema → closes task
5. `/next` — surfaces highest-priority next action from queue

Topics:
- [[_index]]
