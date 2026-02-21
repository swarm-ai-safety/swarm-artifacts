---
name: next
description: Surface the next highest-priority action from the SWARM synthesis pipeline queue and maintenance conditions. Recommends what to work on based on queue state, pending observations, stale claims, and research threads. Triggers on "/next", "what should I work on", "next action", "what's pending".
user-invocable: true
allowed-tools: Read, Glob, Grep, Bash
context: fork
---

## EXECUTE NOW

Read queue and vault state, then recommend.

---

# Next

Surface the next recommended action from the synthesis pipeline.

## Priority Order

1. **Queue tasks in current phase** — claims waiting for /cross-link, /update, or /validate
2. **Unprocessed recent runs** — new experiment folders in runs/ not yet in queue
3. **Maintenance triggers** — observations ≥ 10 or tensions ≥ 5 → /rethink
4. **Stale active claims** — claims not updated in 30+ days
5. **Orphan claims** — claims with no incoming links after initial creation window
6. **Open questions** — claims with status: open waiting for decisive experiments

## State Check

```bash
# Queue state
cat vault/ops/queue/queue.json | python3 -c "
import json, sys
q = json.load(sys.stdin)
tasks = q.get('tasks', [])
pending = [t for t in tasks if t.get('status') == 'pending']
print(f'Queue: {len(pending)} pending tasks')
for t in pending[:5]:
    print(f'  {t[\"id\"]}: {t[\"target\"]} (phase: {t[\"current_phase\"]})')
"

# Unprocessed runs
ls -d runs/*/  2>/dev/null | while read r; do
  run_id=$(basename "$r")
  if ! grep -q "$run_id" vault/ops/queue/queue.json 2>/dev/null; then
    echo "Unprocessed: $run_id"
  fi
done | head -5

# Maintenance triggers
obs=$(ls vault/ops/observations/*.md 2>/dev/null | wc -l | tr -d ' ')
tensions=$(ls vault/ops/tensions/*.md 2>/dev/null | wc -l | tr -d ' ')
echo "Observations: $obs (threshold: 10)"
echo "Tensions: $tensions (threshold: 5)"
```

## Output Format

```
Next recommended action:

  /[command] [target]

  Why: [specific reason this is the priority]

Also pending:
  - [second priority with why]
  - [third priority with why]
```
