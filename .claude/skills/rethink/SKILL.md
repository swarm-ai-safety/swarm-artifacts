---
name: rethink
description: Challenge SWARM vault assumptions against accumulated observations and tensions. Triages friction signals, detects patterns, proposes methodology updates. The scientific method applied to the research OS itself. Triggers on "/rethink", "review observations", "challenge assumptions", "system drift".
user-invocable: true
allowed-tools: Read, Write, Edit, Grep, Glob, Bash, AskUserQuestion
context: fork
---

## Runtime Configuration (Step 0)

Read `vault/ops/derivation-manifest.md`, `vault/ops/config.yaml`, and all files in `vault/ops/methodology/`.

Observation threshold: 10 (from config)
Tension threshold: 5 (from config)

---

## EXECUTE NOW

**Target: $ARGUMENTS**

- If empty: run full six-phase rethink on all pending observations and tensions
- If "triage": Phase 1 only (triage and methodology updates)
- If "patterns": Phases 3-5 only (pattern detection)
- If "drift": Phase 0 only (drift check)
- If a specific filename: triage that single item interactively

---

# Rethink

Challenge assumptions against accumulated evidence. The immune system against calcification.

## Phase 0: Drift Check

Rule Zero: `vault/ops/methodology/` is the canonical specification of how this system operates.

Check for behavioral drift:
- Are claims being created without run_id provenance? (violates kernel invariant)
- Are confidence levels being assigned without statistical criteria? (violates schema)
- Are topic maps being skipped during extraction? (violates processing pipeline)
- Are boundary conditions being omitted from new claims? (violates dense schema commitment)

```bash
# Check recent claims for missing provenance
rg -l 'run: ""' vault/claims/ 2>/dev/null

# Check for claims without boundary_conditions
rg -L 'boundary_conditions' vault/claims/ 2>/dev/null

# Count pending observations
ls vault/ops/observations/*.md 2>/dev/null | wc -l

# Count pending tensions
ls vault/ops/tensions/*.md 2>/dev/null | wc -l
```

## Phase 1: Triage Observations and Tensions

For each pending observation in `vault/ops/observations/`:
- Read the observation note
- Determine: promote to methodology note? archive? needs more data?
- Update status field

For each pending tension in `vault/ops/tensions/`:
- Read the tension note
- Determine: resolved by new evidence? dissolved by reframing? still pending?
- Update status field

## Phase 2: Pattern Detection

After triage, look for patterns across observations:
- Same friction appearing multiple times → structural issue
- Same type of missing evidence → process gap
- Same confidence downgrade pattern → criteria calibration needed

## Phase 3: Synthesis

Generate proposals (not automatic changes):
1. What patterns emerged?
2. What does this suggest about the processing pipeline or schema?
3. What specific changes to methodology would address it?

Present proposals clearly. Human approves before any changes to vault/ops/methodology/.

## Phase 4: Methodology Update

For approved proposals:
- Write new methodology note in vault/ops/methodology/ with category: configuration-state
- Update derivation-rationale.md if fundamental config changed
- Update vault/ops/config.yaml if thresholds or settings changed

## Phase 5: Session Capture

Document what was learned:
- What patterns were found
- What proposals were made
- What was approved and changed
- Archive processed observations (move to ops/observations/archive/)
