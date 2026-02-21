---
name: seed
description: Initialize a batch processing job for one or more SWARM experiment runs. Sets up the queue, calculates claim numbering, creates the extract task. The entry point for pipeline processing of new runs. Triggers on "/seed", "/seed [run-folder]", "start processing", "queue this run".
user-invocable: true
allowed-tools: Read, Write, Glob, Bash
context: fork
---

## EXECUTE NOW

**Target: $ARGUMENTS**

- If target is a run folder path: seed that run for processing
- If target is "all": seed all unprocessed runs in runs/
- If empty: show unprocessed runs and ask which to seed

---

# Seed

Initialize pipeline processing for SWARM experiment runs.

## What Seeding Does

1. Reads the run folder (looks for summary.json, sweep_results.csv, report.json, history.json)
2. Calculates next_claim_start (highest existing claim number + 1)
3. Creates an extract task in ops/queue/ with metadata
4. Adds to queue.json as a pending task
5. Outputs: "Ready. Run /extract [run-folder] to begin extraction."

## Claim Numbering

Claim numbers are global and never reused:

```bash
# Find highest existing claim number
highest=$(ls vault/ops/queue/*.md vault/ops/queue/archive/*.md 2>/dev/null | \
  grep -oE '[0-9]+\.md$' | grep -oE '[0-9]+' | sort -n | tail -1)
next_start=$((highest + 1))
echo "next_claim_start: $next_start"
```

## Extract Task Format

```markdown
---
type: extract
run_id: [run folder name]
run_path: runs/[run-folder]/
next_claim_start: NNN
status: pending
created: YYYY-MM-DD
---

# Extract task: [run-folder]

Run: [[runs/[run-folder]]]

## Run metadata

Type: [single | sweep | redteam | study | calibration]
[Key parameters from run.yaml or summary.json]

## Notes for extraction

[Any flags for the extractor: what to look for, known findings, context]
```

## Queue Entry

After creating the task file, add to queue.json:

```json
{
  "id": "extract-[run-folder]",
  "type": "extract",
  "status": "pending",
  "target": "runs/[run-folder]/",
  "file": "[run-folder]-extract.md",
  "created": "[ISO timestamp]",
  "current_phase": "extract",
  "completed_phases": [],
  "next_claim_start": NNN
}
```
