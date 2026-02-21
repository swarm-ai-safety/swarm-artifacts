---
description: Synthesis pipeline, maintenance cycle, and session rhythm for the SWARM Research OS
type: manual
generated_from: "arscontexta-0.8.0"
---

# Workflows

## Synthesis Pipeline

The full pipeline transforms raw run data into validated, connected claims:

```
runs/[run-folder]/
    ↓
/seed [run]                 — initialize, calculate claim numbers
    ↓
/extract [run]              — extract governance claims, adversarial patterns,
                              parameter sensitivity findings, failure modes
    ↓ (review extraction report, approve candidates)
/cross-link [claim]         — find connections, update topic maps
    ↓
/update [affected-claims]   — backward pass on prior claims
    ↓
/validate [claim]           — 6-gate quality check
    ↓
vault/claims/[claim].md ← published, evidence-linked claim
```

Track progress: `vault/ops/tasks.md` (human view), `vault/ops/queue/queue.json` (machine view).

## Session Rhythm: Orient → Work → Persist

**Orient** (always do this first)
- `vault/self/identity.md` — research identity
- `vault/self/goals.md` — active threads
- `vault/ops/reminders.md` — time-bound items
- `/next` — what the queue recommends

**Work**
- Process runs through the pipeline
- Cross-link new claims
- Update prior claims when new evidence arrives
- Capture friction immediately (`/remember`)

**Persist** (before session ends)
- Update `vault/self/goals.md` with thread status
- Any uncaptured insights → write to vault/claims/ or vault/ops/observations/
- Stop hook auto-captures session state

## Maintenance Cycle (condition-based)

The system triggers maintenance automatically when:

| Condition | Action |
|-----------|--------|
| Pending observations ≥ 10 | `/rethink` suggested at session start |
| Pending tensions ≥ 5 | `/rethink` suggested at session start |
| Claim not updated in 30+ days | Flagged by `/graph` |
| Orphan claims detected | `/graph orphans` surfaces them |
| `vault-health.py` run | Full audit across all vault files |

## Batch Processing

For large backlogs (110+ experiment runs):

```bash
# See all unprocessed runs
ls -d runs/*/ | while read r; do
  run_id=$(basename "$r")
  if ! grep -q "$run_id" vault/ops/queue/queue.json 2>/dev/null; then
    echo "$run_id"
  fi
done

# Process by priority: sweeps first (richest data)
/pipeline runs/[sweep-run]
# Then red-team runs (failure patterns)
/pipeline runs/[redteam-run]
# Then single runs (single-seed evidence)
/pipeline runs/[single-run]
```

---

See [[skills]] for command details.

Topics:
- [[manual]]
