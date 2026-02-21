---
name: pipeline
description: Run the full SWARM synthesis pipeline on one or more experiment runs — seed, extract, cross-link, update, validate in sequence. Triggers on "/pipeline", "/pipeline [run-folder]", "full pipeline", "process everything".
user-invocable: true
allowed-tools: Read, Write, Glob, Bash
context: fork
---

## EXECUTE NOW

**Target: $ARGUMENTS**

- If target is a run folder: run full pipeline on that run
- If target is "queue": process everything currently in the queue
- If empty: show queue state and ask

---

# Pipeline

Orchestrate the full SWARM synthesis pipeline: seed → extract → cross-link → update → validate.

## Pipeline Phases

```
runs/[run-folder]/
    ↓
/seed              → creates extract task in queue
    ↓
/extract [run]     → extracts claims, creates claim task files, updates queue
    ↓
/cross-link [claim] → finds connections, updates topic maps
    ↓
/update [claim]    → backward pass, updates prior claims
    ↓
/validate [claim]  → validates provenance and schema → marks done
```

## Orchestration Mode

Pipeline can run in three modes (from ops/config.yaml):

**manual**: Each phase outputs next command, user runs it manually
**suggested**: Each phase outputs next command AND queues it — user approves or skips
**automatic**: Phases chain without pauses — use only for well-understood run types

Default: suggested. For a 110-experiment backlog, use suggested mode to review each extraction report.

## Batch Processing

For multiple runs:

```bash
# See what's unprocessed
ls -d runs/*/ | while read r; do
  run_id=$(basename "$r")
  if ! grep -q "$run_id" vault/ops/queue/queue.json 2>/dev/null; then
    echo "$run_id"
  fi
done
```

Process highest-priority runs first:
- Runs with `sweep_results.csv` (richest data for parameter sensitivity claims)
- Runs with `report.json` (red-team findings for failure patterns)
- Single runs with `history.json` (single-seed evidence for initial claims)

## Progress Tracking

Check pipeline progress:

```bash
cat vault/ops/queue/queue.json | python3 -c "
import json, sys
q = json.load(sys.stdin)
tasks = q.get('tasks', [])
by_phase = {}
for t in tasks:
    phase = t.get('current_phase', 'unknown')
    by_phase[phase] = by_phase.get(phase, 0) + 1
for phase, count in sorted(by_phase.items()):
    print(f'  {phase}: {count}')
"
```
