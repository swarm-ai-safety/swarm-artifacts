---
description: Require /remember invocation during extraction sessions when judgment calls arise
type: directive
status: active
created: 2026-02-27
rationale: obs-remember-pipeline-never-exercised — 0 observations recorded across 138+ extraction tasks
---

# Extraction sessions must invoke /remember when judgment calls arise

## Directive

During any `/extract` or `/pipeline` session, if the extractor makes a judgment call — skipping a finding, choosing a confidence level, deciding between claim boundaries — invoke `/remember` to capture that decision and its rationale.

## Minimum requirement

At least one `/remember` invocation per extraction session that involves non-trivial judgment (e.g., study or sweep runs with multiple potential claims). Single-seed runs with no extractable findings are exempt.

## Rationale

The `/remember` pipeline exists to capture methodology friction and operational corrections. Without input, the observation threshold (10) for triggering `/rethink` is unreachable, leaving the system unable to self-correct.

This directive was created after the 2026-02-27 rethink session found that 0 observations had been recorded across 138+ pipeline tasks spanning 9 days of active processing.

## Examples of what to capture

- "Skipped finding X because it's a restatement of claim Y"
- "Rated confidence medium despite strong effect because only 1 run"
- "Merged two potential claims into one because they share the same mechanism"
- "This run's governance parameters differ from standard — boundary conditions may not generalize"

---

Topics:
- [[_index]]
