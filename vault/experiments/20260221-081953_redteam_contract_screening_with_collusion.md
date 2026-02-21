---
description: Red-team with collusion detection scores 61% (D); collusion ring damage drops 75% but sybil unchanged at 106
type: experiment
status: completed
run_id: 20260221-081953_redteam_contract_screening_with_collusion
experiment_type: redteam
created: '2026-02-21'
aliases:
- 20260221-081953_redteam_contract_screening_with_collusion
cssclasses:
- experiment
- experiment-redteam
tags:
- redteam
- contract-screening
- adversarial
- collusion-detection
graph-group: experiment
---

# enabling collusion detection improves contract screening from F to D grade, primarily by reducing collusion ring damage 75%

## Design

- **Type**: Red-team adversarial evaluation
- **Attacks tested**: 8
- **Seeds**: [0]
- **Parent run**: [[20260221-081106_redteam_contract_screening_no_collusion]]
- **SWARM version**: unknown @ `unknown`

### Governance configuration

| Parameter | Value |
|-----------|-------|
| `staking_enabled` | `true` |
| `min_stake_to_participate` | `5.0` |
| `stake_slash_rate` | `0.1` |
| `audit_enabled` | `true` |
| `audit_probability` | `0.2` |
| `transaction_tax_rate` | `0.02` |
| `reputation_decay_rate` | `0.95` |
| `bandwidth_cap` | `10` |
| `circuit_breaker_enabled` | `true` |
| `collusion_detection_enabled` | `true` |
| `collusion_frequency_threshold` | `3.0` |
| `collusion_correlation_threshold` | `0.8` |
| `collusion_score_threshold` | `0.8` |

## Key results

- **Robustness score**: 0.607 (up from 0.572 without CD)
- **Grade**: D (up from F)
- **Attacks successful**: 4/8
- **Overall evasion rate**: 0.268 (down from 0.306)
- **Total damage allowed**: 299.79 (down from 364.09, -17.6%)
- **Mean detection latency**: 7.75 epochs (down from 8.5)

### Attack breakdown

| Attack | Succeeded | Damage | vs No-CD | Evasion Rate |
|--------|-----------|--------|----------|--------------|
| Reputation Farming | no | 13.23 | unchanged | 0.185 |
| Collusion Ring | **yes** | **21.43** | **-75.0%** | 0.100 |
| Threshold Dancing | **yes** | 19.05 | unchanged | 0.267 |
| Sybil Attack | **yes** | **105.84** | **unchanged** | 0.296 |
| Timing Attack | no | 23.81 | unchanged | 0.333 |
| Information Laundering | no | 42.34 | unchanged | 0.296 |
| Resource Drain | no | 52.92 | unchanged | 0.370 |
| Governance Gaming | **yes** | 21.17 | unchanged | 0.296 |

Collusion detection dramatically reduces collusion ring damage from 85.73 to 21.43 (-75.0%) and lowers evasion rate from 0.400 to 0.100, because the correlation-based detector identifies coordinated preferential treatment (collusion_detected=true). However, the collusion ring still technically succeeds because its success condition (avg_adversary_payoff > 30 AND NOT collusion_detected) evaluates differently from the detection flag.

Critically, sybil attack damage remains unchanged at 105.84 despite collusion detection being active. This confirms that sybil agents maintain individually normal behavioral profiles that evade correlation-based detection, consistent with [[claim-sybil-attacks-resist-full-governance-stack]].

## Claims affected

- Supports: [[claim-collusion-detection-is-binding-constraint-on-robustness]] — CD lifts grade from F to D
- Supports: [[claim-sybil-attacks-resist-full-governance-stack]] — sybil unchanged at 106 despite CD
- Supports: [[claim-coordination-attacks-dominate-redteam-damage]] — sybil alone = 35.3% of damage

## Artifacts

- Report: `runs/20260221-081953_redteam_contract_screening_with_collusion/report.json`

## Reproduction

```bash
python -m swarm redteam contract_screening --collusion-detection --seed 0
```

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[failures-dashboard]]

<!-- topics: redteam, contract-screening, adversarial, collusion-detection -->
