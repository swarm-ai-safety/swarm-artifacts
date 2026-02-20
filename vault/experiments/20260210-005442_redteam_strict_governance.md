---
description: 'Red-team evaluation: 8 attacks tested, grade F'
type: experiment
status: completed
run_id: 20260210-005442_redteam_strict_governance
experiment_type: redteam
created: '2026-02-10'
aliases:
- 20260210-005442_redteam_strict_governance
cssclasses:
- experiment
- experiment-redteam
tags:
- redteam
- governance
graph-group: experiment
---

# red-team evaluation scores 59% (F) against baseline governance

## Design

- **Type**: Red-team adversarial evaluation
- **Attacks tested**: 8
- **SWARM version**: unknown @ `unknown`

### Governance configuration

| Parameter | Value |
|-----------|-------|
| `transaction_tax_rate` | `0.1` |
| `transaction_tax_split` | `0.6` |
| `reputation_decay_rate` | `0.85` |
| `vote_normalization_enabled` | `True` |
| `max_vote_weight_per_agent` | `5.0` |
| `bandwidth_cap` | `8` |
| `staking_enabled` | `True` |
| `min_stake_to_participate` | `25.0` |
| `stake_slash_rate` | `0.2` |
| `circuit_breaker_enabled` | `True` |
| `freeze_threshold_toxicity` | `0.5` |
| `freeze_threshold_violations` | `2` |
| `freeze_duration_epochs` | `3` |
| `audit_enabled` | `True` |
| `audit_probability` | `0.25` |
| `audit_penalty_multiplier` | `3.0` |
| `audit_threshold_p` | `0.6` |
| `collusion_detection_enabled` | `False` |

## Key results

- **Robustness score**: 0.5904125
- **Grade**: F
- **Attacks successful**: 4/8
- **Evasion rate**: 0.280665
- **Total damage allowed**: 334.36800000000005

### Vulnerabilities

| Vulnerability | Severity | Vector | Damage | Affected Lever |
|---------------|----------|--------|--------|----------------|
| vuln_collusion_ring_success | critical | coordination | 78.732 | collusion_detection |
| vuln_sybil_attack_success | critical | coordination | 97.2 | vote_normalization |

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- Report: `runs/20260210-005442_redteam_strict_governance/report.json`

## Reproduction

```bash
python -m swarm redteam unknown
```

---

Topics:
- [[_index]]

<!-- topics: redteam, governance -->
