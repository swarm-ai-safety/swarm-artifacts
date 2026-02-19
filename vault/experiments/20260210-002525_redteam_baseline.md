---
description: 'Red-team evaluation: 8 attacks tested, grade F'
type: experiment
status: completed
run_id: 20260210-002525_redteam_baseline
experiment_type: redteam
created: '2026-02-10'
---

# red-team evaluation scores 45% (F) against baseline governance

## Design

- **Type**: Red-team adversarial evaluation
- **Attacks tested**: 8
- **SWARM version**: unknown @ `unknown`

### Governance configuration

| Parameter | Value |
|-----------|-------|
| `transaction_tax_rate` | `0.0` |
| `transaction_tax_split` | `0.5` |
| `reputation_decay_rate` | `1.0` |
| `bandwidth_cap` | `10` |
| `staking_enabled` | `False` |
| `min_stake_to_participate` | `0.0` |
| `circuit_breaker_enabled` | `False` |
| `audit_enabled` | `False` |
| `collusion_detection_enabled` | `False` |

## Key results

- **Robustness score**: 0.45264
- **Grade**: F
- **Attacks successful**: 5/8
- **Evasion rate**: 0.421575
- **Total damage allowed**: 455.7

### Vulnerabilities

| Vulnerability | Severity | Vector | Damage | Affected Lever |
|---------------|----------|--------|--------|----------------|
| vuln_reputation_farming_success | high | exploitation | 39.0 | reputation_decay |
| vuln_collusion_ring_success | critical | coordination | 97.19999999999999 | collusion_detection |
| vuln_threshold_dancing_success | high | evasion | 40.5 | circuit_breaker |
| vuln_sybil_attack_success | critical | coordination | 120.0 | vote_normalization |

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Report: `runs/20260210-002525_redteam_baseline/report.json`

## Reproduction

```bash
python -m swarm redteam unknown
```

---

Topics:
- [[_index]]

<!-- topics: baseline, redteam -->
