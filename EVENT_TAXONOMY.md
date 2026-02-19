# SWARM Research OS: Event Taxonomy

*Spec v0.1 — 2026-02-18*

This document defines the event types that drive the Research OS pipeline.
Events are the connective tissue between layers: SWARM emits them, Inngest
reacts to them, arscontexta consumes the results.

---

## Design Principles

1. **Past tense for completed actions** — `swarm.run.completed`, not `swarm.run.complete`
2. **Dot-namespaced** — `<system>.<resource>.<action>`
3. **Every event carries enough context to act on** — no secondary lookups needed for routing
4. **Idempotent handlers** — same event processed twice produces the same result
5. **Content-addressed artifacts** — SHA-256 hashes in payloads enable verification

---

## 1. SWARM Events (experiment engine)

### `swarm.run.started`

Emitted when a single run begins execution.

```jsonc
{
  "name": "swarm.run.started",
  "ts": "2026-02-13T20:20:50Z",
  "data": {
    "run_id": "20260213-202050_baseline_governance_v2",
    "experiment_type": "sweep",          // single | sweep | redteam | study | calibration
    "scenario_ref": "scenarios/sweeps/baseline_governance.yaml",
    "scenario_sha256": "e3b0c44...",
    "git_sha": "a1b2c3d",
    "swarm_version": "0.14.2",
    "seeds": [1, 2, 3],
    "total_configs": 14,
    "estimated_runs": 700
  }
}
```

**Triggered by**: `python -m swarm run` or `python -m swarm sweep`
**Consumed by**: Dashboard (progress tracking), Inngest (timeout watchdog)

---

### `swarm.run.completed`

Emitted when a single run (or all runs in a sweep) finishes successfully.

```jsonc
{
  "name": "swarm.run.completed",
  "ts": "2026-02-13T20:51:37Z",
  "data": {
    "run_id": "20260213-202050_baseline_governance_v2",
    "experiment_type": "sweep",
    "status": "completed",
    "wall_time_seconds": 1847,
    "total_runs": 700,
    "run_yaml_path": "runs/20260213-202050_baseline_governance_v2/run.yaml",
    "summary_path": "runs/20260213-202050_baseline_governance_v2/summary.json",
    "artifacts": {
      "summary": "summary.json",
      "sweep_csv": "sweep_results.csv",
      "scripts": ["analyze.py", "generate_plots.py", "run_sweep.py"]
    },
    "primary_metric": "welfare",
    "significant_findings": 18,
    "tags": ["governance", "sweep", "circuit-breaker", "transaction-tax"]
  }
}
```

**Triggered by**: SWARM run completing without error
**Consumed by**: Inngest → synthesis pipeline, notification

---

### `swarm.run.failed`

Emitted when a run fails or is killed.

```jsonc
{
  "name": "swarm.run.failed",
  "ts": "2026-02-13T20:35:12Z",
  "data": {
    "run_id": "20260213-202050_baseline_governance_v2",
    "experiment_type": "sweep",
    "status": "failed",
    "error": "OutOfMemoryError: agent graph exceeded 16GB",
    "partial_runs_completed": 342,
    "total_runs_expected": 700,
    "last_seed": 171,
    "run_yaml_path": "runs/20260213-202050_baseline_governance_v2/run.yaml"
  }
}
```

**Triggered by**: Unhandled exception, OOM, timeout, SIGKILL
**Consumed by**: Inngest → retry logic (same seeds), alerting

---

### `swarm.sweep.completed`

Emitted after all runs in a parameter sweep finish AND statistical analysis completes.
Distinct from `swarm.run.completed` — this fires only after the analysis step.

```jsonc
{
  "name": "swarm.sweep.completed",
  "ts": "2026-02-13T20:55:00Z",
  "data": {
    "run_id": "20260213-202050_baseline_governance_v2",
    "swept_parameters": {
      "governance.transaction_tax_rate": [0.0, 0.025, 0.05, 0.075, 0.1, 0.125, 0.15],
      "governance.circuit_breaker_enabled": [false, true]
    },
    "total_runs": 700,
    "total_hypotheses": 132,
    "bonferroni_significant": 18,
    "summary_path": "runs/20260213-202050_baseline_governance_v2/summary.json",
    "sweep_csv_path": "runs/20260213-202050_baseline_governance_v2/sweep_results.csv",
    "p_hacking_audit": {
      "pre_registered": true,
      "bonferroni_significant": 18,
      "holm_bonferroni_significant": 22
    }
  }
}
```

**Triggered by**: Analysis script completing after a sweep
**Consumed by**: Inngest → vault synthesis (experiment notes, claim updates, sweep summaries)

---

### `swarm.redteam.completed`

Emitted after a red-team evaluation finishes.

```jsonc
{
  "name": "swarm.redteam.completed",
  "ts": "2026-02-12T23:15:00Z",
  "data": {
    "run_id": "20260212-231123_redteam",
    "governance_config_hash": "abc123...",
    "attacks_tested": 8,
    "attacks_successful": 6,
    "robustness_score": 0.40,
    "grade": "F",
    "critical_vulnerabilities": 2,
    "report_path": "runs/20260212-231123_redteam/report.json"
  }
}
```

**Triggered by**: Red-team harness completing
**Consumed by**: Inngest → vulnerability tracking, governance regression alerts

---

### `swarm.canary.completed`

Emitted after a nightly/scheduled canary run finishes.

```jsonc
{
  "name": "swarm.canary.completed",
  "ts": "2026-02-18T04:00:00Z",
  "data": {
    "run_id": "20260218-040000_canary_nightly",
    "suite": "nightly",                // nightly | weekly | pre-merge
    "scenarios_run": 5,
    "scenarios_passed": 5,
    "scenarios_failed": 0,
    "drift_detected": false,
    "baseline_comparison": {
      "welfare_delta_pct": -0.3,
      "toxicity_delta_pct": 0.1,
      "within_tolerance": true
    }
  }
}
```

**Triggered by**: Scheduled cron or CI pipeline
**Consumed by**: Inngest → drift alerting, regression issue creation

---

## 2. Vault Events (arscontexta synthesis)

### `vault.note.created`

Emitted when arscontexta creates a new vault note (experiment, claim, sweep summary, etc.).

```jsonc
{
  "name": "vault.note.created",
  "ts": "2026-02-13T21:00:00Z",
  "data": {
    "note_path": "vault/experiments/20260213-202050_baseline_governance_v2.md",
    "note_type": "experiment",         // experiment | claim | sweep | governance | topology | failure
    "source_run_id": "20260213-202050_baseline_governance_v2",
    "linked_claims": ["claim-tax-welfare-tradeoff", "claim-circuit-breakers-dominate"],
    "auto_generated": true
  }
}
```

**Triggered by**: Synthesis pipeline processing a `swarm.*.completed` event
**Consumed by**: Git auto-commit, PR creation

---

### `vault.claim.updated`

Emitted when a claim card's status, confidence, or evidence changes.

```jsonc
{
  "name": "vault.claim.updated",
  "ts": "2026-02-13T21:05:00Z",
  "data": {
    "claim_id": "claim-circuit-breakers-dominate",
    "claim_path": "vault/claims/claim-circuit-breakers-dominate.md",
    "previous_status": "active",
    "new_status": "active",
    "previous_confidence": "medium",
    "new_confidence": "high",
    "trigger_run_id": "20260213-202050_baseline_governance_v2",
    "evidence_added": {
      "type": "supporting",
      "detail": "Replicated with 700 runs, d=1.64, Bonferroni p=0.022"
    },
    "change_summary": "Confidence upgraded medium→high: replicated across 700 runs with Bonferroni correction"
  }
}
```

**Triggered by**: Synthesis pipeline finding new evidence for an existing claim
**Consumed by**: PR creation (claim update PR), notification

---

### `vault.claim.weakened`

Emitted when new evidence contradicts an existing claim.

```jsonc
{
  "name": "vault.claim.weakened",
  "ts": "2026-02-14T10:00:00Z",
  "data": {
    "claim_id": "claim-staking-backfires",
    "claim_path": "vault/claims/claim-staking-backfires.md",
    "previous_confidence": "high",
    "new_confidence": "contested",
    "trigger_run_id": "20260214-100000_staking_ring_topology",
    "contradiction": "Staking improves welfare in ring topology (d=0.82, p=0.003) — opposite of small-world finding",
    "boundary_condition_added": "Effect reverses in ring topology"
  }
}
```

**Triggered by**: Synthesis pipeline finding contradictory evidence
**Consumed by**: High-priority alert, PR with investigation request

---

### `vault.synthesis.completed`

Emitted after a full synthesis pass (all notes generated, claims updated, index rebuilt).

```jsonc
{
  "name": "vault.synthesis.completed",
  "ts": "2026-02-13T21:10:00Z",
  "data": {
    "trigger_event": "swarm.sweep.completed",
    "trigger_run_id": "20260213-202050_baseline_governance_v2",
    "notes_created": 1,
    "claims_updated": 2,
    "claims_created": 0,
    "claims_weakened": 0,
    "index_rebuilt": true
  }
}
```

**Triggered by**: Synthesis pipeline finishing all steps
**Consumed by**: PR creation (bundles all vault changes into one PR)

---

## 3. GitHub Events (replication layer)

### `github.pr.created`

Emitted when the pipeline opens a PR with results.

```jsonc
{
  "name": "github.pr.created",
  "ts": "2026-02-13T21:12:00Z",
  "data": {
    "pr_number": 47,
    "pr_url": "https://github.com/swarm-ai-safety/swarm-artifacts/pull/47",
    "title": "Sweep results: tax sensitivity in baseline governance v2",
    "trigger_run_id": "20260213-202050_baseline_governance_v2",
    "files_changed": [
      "runs/20260213-202050_baseline_governance_v2/run.yaml",
      "vault/experiments/20260213-202050_baseline_governance_v2.md",
      "vault/claims/claim-tax-welfare-tradeoff.md",
      "vault/claims/claim-circuit-breakers-dominate.md",
      "run-index.yaml"
    ],
    "claims_affected": ["claim-tax-welfare-tradeoff", "claim-circuit-breakers-dominate"]
  }
}
```

**Triggered by**: Synthesis completion
**Consumed by**: Notification, review assignment

---

### `github.pr.merged`

Standard GitHub webhook. Used to trigger follow-up runs.

```jsonc
{
  "name": "github.pr.merged",
  "ts": "2026-02-13T22:00:00Z",
  "data": {
    "pr_number": 47,
    "merge_sha": "def456...",
    "labels": ["sweep-results", "governance"],
    "files_changed": ["scenarios/sweeps/new_mechanism.yaml"],
    "contains_new_scenario": true
  }
}
```

**Triggered by**: GitHub webhook on PR merge
**Consumed by**: Inngest → if new scenario merged, run benchmark suite against it

---

## 4. Orchestration Events (Inngest internal)

### `inngest.retry.requested`

Internal event when a failed run needs retry with the same seed.

```jsonc
{
  "name": "inngest.retry.requested",
  "ts": "2026-02-13T20:36:00Z",
  "data": {
    "original_run_id": "20260213-202050_baseline_governance_v2",
    "retry_attempt": 1,
    "max_retries": 3,
    "failed_seed": 171,
    "resume_from_config": 342,
    "reason": "OutOfMemoryError"
  }
}
```

---

### `inngest.regression.scheduled`

Internal event for scheduled regression suites.

```jsonc
{
  "name": "inngest.regression.scheduled",
  "ts": "2026-02-18T04:00:00Z",
  "data": {
    "suite": "nightly",
    "scenarios": [
      "scenarios/benchmarks/baseline.yaml",
      "scenarios/benchmarks/adversarial_basic.yaml",
      "scenarios/benchmarks/governance_smoke.yaml",
      "scenarios/benchmarks/ldt_canary.yaml",
      "scenarios/benchmarks/delegation_canary.yaml"
    ],
    "seeds": [42, 7, 123],
    "git_sha": "abc789..."
  }
}
```

---

## 5. Event Flow Diagrams

### Happy path: sweep → synthesis → PR

```
 swarm.run.started
       │
       ▼
 swarm.run.completed
       │
       ▼
 swarm.sweep.completed  ──────────────────────┐
       │                                       │
       ▼                                       ▼
 [arscontexta synthesis]              [validate run.yaml]
       │                                       │
       ├── vault.note.created                  │
       ├── vault.claim.updated                 │
       └── vault.synthesis.completed           │
                    │                          │
                    ▼                          │
              github.pr.created  ◄─────────────┘
                    │
                    ▼
              [human review]
                    │
                    ▼
              github.pr.merged
                    │
                    ▼
              [if new scenario: trigger benchmark suite]
```

### Failure path: run fails → retry → succeed

```
 swarm.run.started
       │
       ▼
 swarm.run.failed
       │
       ▼
 inngest.retry.requested
       │
       ▼
 swarm.run.started  (attempt 2, same seeds)
       │
       ▼
 swarm.run.completed
       │
       ▼
 [normal synthesis path]
```

### Nightly regression

```
 inngest.regression.scheduled  (cron: 0 4 * * *)
       │
       ▼
 swarm.run.started  ×5 (fan-out: one per canary scenario)
       │
       ▼
 swarm.canary.completed  ×5 (fan-in: wait for all)
       │
       ├── drift_detected: false  → log + done
       └── drift_detected: true   → create GitHub issue
```

### Claim weakening alert

```
 swarm.sweep.completed
       │
       ▼
 [arscontexta synthesis]
       │
       ▼
 vault.claim.weakened  ──► [high-priority notification]
       │
       ▼
 github.pr.created  (title: "⚠ Claim weakened: ...")
```

---

## 6. Event Payload Conventions

| Convention | Rule |
|-----------|------|
| Timestamps | ISO 8601 UTC, always `ts` field |
| Run references | Always `run_id` string matching folder name |
| File paths | Relative to repo root |
| Hashes | SHA-256, lowercase hex |
| Enums | Lowercase, hyphen-separated |
| Arrays | Always arrays, even for single values |
| Nullability | Omit optional fields rather than setting null |

---

## 7. Event-to-Handler Mapping

Summary of which Inngest function handles each event:

| Event | Handler | Action |
|-------|---------|--------|
| `swarm.run.completed` | `fn-validate-run` | Validate run.yaml against schema |
| `swarm.sweep.completed` | `fn-synthesize-sweep` | Generate vault notes, update claims, rebuild index |
| `swarm.redteam.completed` | `fn-synthesize-redteam` | Generate vulnerability notes, update governance pages |
| `swarm.run.failed` | `fn-retry-run` | Retry with same seeds (max 3 attempts) |
| `swarm.canary.completed` | `fn-check-drift` | Compare against baseline, alert if drift |
| `vault.synthesis.completed` | `fn-create-pr` | Bundle vault changes into a PR |
| `vault.claim.weakened` | `fn-alert-weakened` | High-priority notification + PR |
| `github.pr.merged` | `fn-post-merge` | If new scenario, trigger benchmark suite |
| `inngest.regression.scheduled` | `fn-nightly-regression` | Fan-out canary scenarios |
