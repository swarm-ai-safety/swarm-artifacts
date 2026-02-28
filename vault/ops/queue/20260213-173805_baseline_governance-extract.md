---
type: extract
run_id: 20260213-173805_baseline_governance
run_path: runs/20260213-173805_baseline_governance/
next_claim_start: 13
status: pending
created: 2026-02-20
---

# Extract task: 20260213-173805_baseline_governance

Run: runs/20260213-173805_baseline_governance

## Run metadata

Type: sweep
Swept parameters: governance.transaction_tax_rate (0.0, 0.05, 0.1, 0.15), governance.circuit_breaker_enabled (false, true)
Total runs: 80
Total hypotheses tested: 42
Significant findings: 4
Artifacts: summary.json, sweep_results.csv, council_review.json

## Notes for extraction

Baseline governance sweep across tax rate and circuit breaker. 4 significant findings from 42 hypotheses — look for tax rate thresholds and circuit breaker interaction effects. Compare with v2 sweep (20260213-202050) which expanded the parameter grid.
