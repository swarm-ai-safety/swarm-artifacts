---
description: Common issues and resolution patterns for the SWARM Research OS
type: manual
generated_from: "arscontexta-0.8.0"
---

# Troubleshooting

## Common Issues

### Orphan Claims (no incoming links)

**Symptom**: Claims exist in vault/claims/ but nothing references them.

**Fix**: `/graph orphans` to surface them, then `/cross-link [claim]` to find connections. Every claim needs at least one topic map link in its Topics footer AND at least one incoming wiki-link from another claim or experiment note.

### Claim Confidence Mismatch

**Symptom**: `/validate` reports Gate 3 failure — confidence level doesn't match evidence.

**Fix**: Check the statistical criteria table in CLAUDE.md. `high` requires Bonferroni-significant AND replicated across ≥2 seeds. If you only have a single run, confidence must be `low` or `medium` at most.

### Missing Run Provenance

**Symptom**: `/validate` reports Gate 1 failure — run_id not found in runs/.

**Fix**: Check that the run folder exists: `ls runs/[run_id]`. If the run was archived or moved, update the evidence entry's `run:` field to the correct path.

### Raw P-Values Without Correction

**Symptom**: `/validate` reports Gate 2 failure — no correction method.

**Fix**: Add the correction method to the `detail:` field: `"p=0.022, Bonferroni-corrected, d=1.64, N=70 runs"`. Never leave raw p-values alone.

### Topic Map Not Updating

**Symptom**: New claim exists but dashboards don't show it.

**Fix**: Dashboards use Dataview queries — they update automatically in Obsidian. For CLI access, run `python scripts/vault-stats.py` instead.

### Pipeline Queue Stalled

**Symptom**: Tasks stuck in queue, `/next` always shows same pending task.

**Fix**: Check queue state: `cat vault/ops/queue/queue.json`. If a task is stuck at a phase, manually advance it via `/extract`, `/cross-link`, `/update`, or `/validate` on that specific target.

### Methodology Drift

**Symptom**: Claims being created without provenance, confidence assigned without evidence.

**Fix**: Run `/rethink drift` to check behavioral drift against methodology spec. Check `vault/ops/methodology/derivation-rationale.md` for the rules.

### High Observation Count

**Symptom**: Session start shows "Observation threshold reached: N pending".

**Fix**: Run `/rethink` to triage all pending observations. Some will become methodology notes, some will be archived, some will reveal patterns requiring config changes.

---

See [[meta-skills]] for /rethink and /remember details.

Topics:
- [[manual]]
