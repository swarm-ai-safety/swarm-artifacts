---
description: Contract screening achieves perfect type separation, 6.7x honest payoff premium, and D-grade adversarial robustness across 5 runs
type: sweep-summary
status: active
parameter: contract_screening
values_tested:
  - seed_variation
  - collusion_detection_enabled
  - governance_stack_level
created: 2026-02-21
updated: 2026-02-21
aliases:
  - contract-screening-sweep-series
cssclasses:
  - sweep-summary
tags:
  - contract-screening
  - mechanism-design
  - screening-equilibrium
  - redteam
graph-group: sweep
---

# contract screening produces perfect type separation and 6.7x honest payoff premium but only D-grade adversarial robustness

## Runs in this sweep

| Run ID | Date | Type | Governance Config | Key Metrics |
|--------|------|------|-------------------|-------------|
| [[contract_screening_seed42]] | Feb 21 | single | baseline (2% tax, CB, audit) | Perfect separation at epoch 0; honest payoff 0.55-0.75/interaction |
| [[contract_screening_sweep]] | Feb 21 | sweep (10 seeds) | baseline (2% tax, CB, audit) | separation_quality=1.0, infiltration=0.0, honest/deceptive ratio=6.7x, d=2.42 |
| [[20260221-081106_redteam_contract_screening_no_collusion]] | Feb 21 | redteam | staking+audit+CB, CD off | Grade F (57%), 4/8 attacks succeed, damage=364 |
| [[20260221-081953_redteam_contract_screening_with_collusion]] | Feb 21 | redteam | staking+audit+CB+CD | Grade D (61%), collusion ring damage -75%, sybil unchanged |
| [[20260221-082443_redteam_contract_screening_full]] | Feb 21 | redteam | full governance stack | Grade D (61%), deterministic replication of with-CD results |

## Convergence

The contract screening series has converged on three findings with different confidence levels:

**Established (high confidence):**
- Perfect type separation (separation_quality=1.0, infiltration_rate=0.0) is deterministic across all 11 seeds (42-52). Zero variance means this is a mechanistic result, not stochastic. The screening contracts are incentive-compatible by construction, so the revelation principle guarantees separation in equilibrium.
- Honest agents earn 6.7x more than deceptive agents (28.52 vs 4.27) with Cohen's d=2.42 for honest-opportunistic gap, Bonferroni-corrected p<0.001. The payoff premium compounds through reputation dynamics (honest agents reach 0.27-0.46 reputation by step 4 vs 0.02-0.16 for opportunistic).

**Emerging (medium confidence):**
- Collusion detection reduces ring damage by 75% (85.73 to 21.43) and lifts robustness grade from F to D. However, this is based on a single seed (seed=0) with deterministic replication only. Cross-seed replication needed to reach high confidence.

**Unresolved:**
- Sybil attacks inflict 105.84 damage regardless of governance configuration, unchanged across all three red-team runs. The screening mechanism does not address sybil identity amplification.
- Toxicity rate averages 32.1% across the sweep, likely reflecting cross-pool interactions. Whether screening-specific mechanisms could reduce this is untested.
- All results are for N=10 agents with 5:3:2 type ratio. Scaling behavior is completely untested.

## Phase transition surface

No parameter sweep across contract screening values was performed — the series instead explores seed robustness and governance layering. The key qualitative transitions observed are:

- **Collusion detection toggle**: Binary transition from F to D grade. Enabling CD cuts collusion ring damage 75% but leaves sybil damage flat. There is no intermediate state.
- **Governance stack saturation**: Adding mechanisms beyond staking+audit+CB+CD produces zero marginal benefit. The full governance run replicates with-CD results exactly, indicating the governance stack is saturated for this scenario.
- **Type separation**: No transition — separation is perfect (1.0) at all tested configurations. The screening mechanism operates independently of the governance stack.

## Claims supported

- [[claim-contract-screening-achieves-perfect-type-separation]] — Perfect separation across 11 seeds (high confidence). Seed 42 provides single-run evidence; seeds 43-52 provide cross-seed replication with zero variance.
- [[claim-screening-equilibrium-generates-honest-payoff-premium]] — 6.7x honest/deceptive ratio, d=2.42 honest/opportunistic gap (high confidence). Bonferroni-corrected across 10 seeds.
- [[claim-collusion-detection-reduces-ring-damage-75pct]] — 75% damage reduction from CD toggle (medium confidence). Replicated deterministically but only at seed=0.

## Next decisive experiment

1. **Scaling test**: Run contract screening with N=20, 50, 100 agents to test whether perfect separation breaks with larger populations and whether the 6.7x payoff ratio is scale-invariant.
2. **Cross-seed red-team**: Red-team evaluation across seeds 1-10 to lift collusion detection claim from medium to high confidence.
3. **Adaptive adversary**: Test whether learning agents can mimic honest types and infiltrate the truthful_auction pool, which would break the mechanistic separation guarantee.
4. **Type ratio sensitivity**: Sweep agent type ratios (e.g., 2:5:3 or 1:1:8) to test whether separation and payoff premium are robust to population composition.
5. **Anti-sybil mechanisms**: Test identity-verification or proof-of-work mechanisms specific to screening pools, since sybil attacks are the dominant residual vulnerability.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: contract-screening, mechanism-design, screening-equilibrium, redteam, sweep-series -->
