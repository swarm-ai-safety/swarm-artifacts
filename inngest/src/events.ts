/**
 * SWARM Research OS — Event type definitions.
 *
 * Every event in the system is typed here. The Inngest client uses this
 * record to give full autocomplete on event names and typed payloads.
 *
 * See EVENT_TAXONOMY.md for prose descriptions and flow diagrams.
 */

// ── Shared types ──────────────────────────────────────────────────────

export type ExperimentType = "single" | "sweep" | "redteam" | "study" | "calibration";
export type RunStatus = "completed" | "failed" | "partial";
export type ClaimStatus = "active" | "weakened" | "superseded" | "retracted";
export type ClaimConfidence = "high" | "medium" | "low" | "contested";
export type RegressionSuite = "nightly" | "weekly" | "pre-merge";

export interface ArtifactManifest {
  summary?: string;
  sweep_csv?: string;
  epoch_csvs?: string[];
  scripts?: string[];
  traces?: string[];
  plots?: { path: string; description: string }[];
  external?: {
    path: string;
    sha256: string;
    size_bytes: number;
    storage: string;
  }[];
}

export interface PHackingAudit {
  pre_registered: boolean;
  bonferroni_significant: number;
  holm_bonferroni_significant: number;
}

// ── Event definitions ─────────────────────────────────────────────────

export type Events = {
  // ── SWARM layer ───────────────────────────────────────────────────

  "swarm/run.started": {
    data: {
      run_id: string;
      experiment_type: ExperimentType;
      scenario_ref: string;
      scenario_sha256: string;
      git_sha: string;
      swarm_version: string;
      seeds: number[];
      total_configs?: number;
      estimated_runs?: number;
    };
  };

  "swarm/run.completed": {
    data: {
      run_id: string;
      experiment_type: ExperimentType;
      status: "completed";
      wall_time_seconds: number;
      total_runs?: number;
      run_yaml_path: string;
      summary_path: string;
      artifacts: ArtifactManifest;
      primary_metric?: string;
      significant_findings?: number;
      tags: string[];
    };
  };

  "swarm/run.failed": {
    data: {
      run_id: string;
      experiment_type: ExperimentType;
      status: "failed";
      error: string;
      partial_runs_completed?: number;
      total_runs_expected?: number;
      last_seed?: number;
      run_yaml_path: string;
    };
  };

  "swarm/sweep.completed": {
    data: {
      run_id: string;
      swept_parameters: Record<string, (string | number | boolean)[]>;
      total_runs: number;
      total_hypotheses: number;
      bonferroni_significant: number;
      summary_path: string;
      sweep_csv_path: string;
      p_hacking_audit: PHackingAudit;
    };
  };

  "swarm/redteam.completed": {
    data: {
      run_id: string;
      governance_config_hash: string;
      attacks_tested: number;
      attacks_successful: number;
      robustness_score: number;
      grade: string;
      critical_vulnerabilities: number;
      report_path: string;
    };
  };

  "swarm/canary.completed": {
    data: {
      run_id: string;
      suite: RegressionSuite;
      scenarios_run: number;
      scenarios_passed: number;
      scenarios_failed: number;
      drift_detected: boolean;
      baseline_comparison: {
        welfare_delta_pct: number;
        toxicity_delta_pct: number;
        within_tolerance: boolean;
      };
    };
  };

  // ── Vault layer ───────────────────────────────────────────────────

  "vault/note.created": {
    data: {
      note_path: string;
      note_type: "experiment" | "claim" | "sweep" | "governance" | "topology" | "failure";
      source_run_id: string;
      linked_claims: string[];
      auto_generated: boolean;
    };
  };

  "vault/claim.updated": {
    data: {
      claim_id: string;
      claim_path: string;
      previous_status: ClaimStatus;
      new_status: ClaimStatus;
      previous_confidence: ClaimConfidence;
      new_confidence: ClaimConfidence;
      trigger_run_id: string;
      evidence_added: {
        type: "supporting" | "weakening";
        detail: string;
      };
      change_summary: string;
    };
  };

  "vault/claim.weakened": {
    data: {
      claim_id: string;
      claim_path: string;
      previous_confidence: ClaimConfidence;
      new_confidence: ClaimConfidence;
      trigger_run_id: string;
      contradiction: string;
      boundary_condition_added: string;
    };
  };

  "vault/synthesis.completed": {
    data: {
      trigger_event: string;
      trigger_run_id: string;
      notes_created: number;
      claims_updated: number;
      claims_created: number;
      claims_weakened: number;
      index_rebuilt: boolean;
    };
  };

  // ── GitHub layer ──────────────────────────────────────────────────

  "github/pr.created": {
    data: {
      pr_number: number;
      pr_url: string;
      title: string;
      trigger_run_id: string;
      files_changed: string[];
      claims_affected: string[];
    };
  };

  "github/pr.merged": {
    data: {
      pr_number: number;
      merge_sha: string;
      labels: string[];
      files_changed: string[];
      contains_new_scenario: boolean;
    };
  };

  // ── Inngest internal ──────────────────────────────────────────────

  "inngest/retry.requested": {
    data: {
      original_run_id: string;
      retry_attempt: number;
      max_retries: number;
      failed_seed?: number;
      resume_from_config?: number;
      reason: string;
    };
  };

  "inngest/regression.scheduled": {
    data: {
      suite: RegressionSuite;
      scenarios: string[];
      seeds: number[];
      git_sha: string;
    };
  };
};
