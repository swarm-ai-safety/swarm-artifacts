---
name: update
description: Update prior claims with new evidence, boundary conditions, or weakening findings. The backward-pass phase — after new claims are created and connected, go back and update what existing claims now know. Triggers on "/update", "/update [claim]", "update prior claims", "backward pass", "strengthen this claim".
user-invocable: true
allowed-tools: Read, Write, Edit, Grep, Glob, Bash, mcp__qmd__vector_search
context: fork
---

## Runtime Configuration (Step 0)

Read `vault/ops/derivation-manifest.md` and `vault/ops/config.yaml`.

---

## EXECUTE NOW

**Target: $ARGUMENTS**

- If target is a claim: update that specific claim with new context
- If target is "recent": update all claims that new evidence from today bears on
- If target is empty: check queue for claims in "update" phase

---

# Update Prior Claims

The backward-pass phase of the synthesis pipeline. New evidence changes what old claims know.

## Philosophy

Claims are not frozen at creation. A claim about transaction taxes written in week 2 may be weakened by a week 5 sweep finding a narrower boundary condition. That claim needs updating — not deletion, not silent retirement, but documented evolution with lifecycle tracking.

**The claim lifecycle:**
```
active → weakened (new contradicting evidence) → superseded (stronger claim replaces it) → retracted (evidence base collapsed)
```

Every status change must be visible, explained, and timestom-stamped.

## What Triggers an Update

1. **New supporting evidence**: Add to `evidence.supporting` with run_id and effect size
2. **Boundary condition discovered**: The claim holds under X but not Y — add to `boundary_conditions`
3. **Weakening evidence found**: Add to `evidence.weakening`, evaluate whether to downgrade confidence
4. **Superseding claim exists**: Set `superseded_by:` and update status to `superseded`
5. **Sensitivity finding**: Sweep reveals the claim is topology-sensitive — add to `sensitivity`

## Workflow

1. Read the target claim fully
2. Identify what new evidence or context is available
3. Determine which update type applies (strengthen, bound, weaken, supersede)
4. Edit the claim's YAML fields and body:
   - Add evidence entries with correct run_id
   - Update boundary_conditions
   - Update sensitivity fields
   - If weakening: add to evidence.weakening, evaluate confidence downgrade
   - If superseding: update status, set superseded_by field
5. Update the `updated:` date field
6. If status changed: document why in the claim body under an "Update history" section

## Quality Gates

- Never silently delete evidence entries
- Never downgrade confidence without documenting the specific contradicting evidence
- Never mark superseded without linking to the superseding claim
- Every update must preserve traceability from raw run data to current claim state

## Pipeline Chaining

After updates complete:
- Output "Next: /validate [updated claims]"
- In suggested mode: advance queue entries to current_phase: "validate"
