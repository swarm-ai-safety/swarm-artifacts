---
description: One sentence summarizing the experiment and its key finding (~150 chars)
type: experiment
status: completed | failed | partial
run_id: "YYYYMMDD-HHMMSS_slug"
experiment_type: single | sweep | redteam | study | calibration
created: YYYY-MM-DD

_schema:
  required: [description, type, status, run_id, experiment_type, created]
  optional: [swarm_version, git_sha, hypothesis]
  enums:
    type: [experiment]
    status: [completed, failed, partial]
    experiment_type: [single, sweep, redteam, study, calibration]
  constraints:
    description: "max 200 chars, must add info beyond title, no trailing period"
    run_id: "must match folder name in runs/"
---

# prose-as-title expressing the experiment's purpose and outcome

## Design

- **Hypothesis**: what the experiment tests
- **Type**: experiment type
- **Parameters swept**: list of swept parameters and their values (sweeps only)
- **Seeds**: seed count or list
- **Total runs**: number of individual runs
- **SWARM version**: version @ git SHA

## Key results

Summarize findings with effect sizes, p-values, and correction methods.
Use connective reasoning: because, therefore, this suggests, however.

## Claims affected

- Supports: [[claim-id]] — how this run supports the claim
- Weakens: [[claim-id]] — how this run contradicts the claim

## Artifacts

- Summary: `runs/<run_id>/summary.json`
- CSV: `runs/<run_id>/sweep_results.csv`
- Scripts: list of analysis scripts

## Reproduction

```bash
python -m swarm <command> <scenario> --seed <N>
```

---

Topics:
- [[_index]]
