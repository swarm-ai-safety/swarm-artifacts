---
description: "Circuit breakers alone outperform full governance stacks on welfare and toxicity"
type: claim
status: active
confidence: high
domain: governance

evidence:
  supporting:
    - run: "20260211-000149_kernel_market_governance_comparison"
      metric: "welfare"
      detail: "CB-only: 22.96 welfare, 0.395 toxicity. Full governance: 21.38, 0.399. d=1.64, p=0.022, Bonferroni-corrected. 70 runs, 10 seeds."
    - run: "20260210-235049_kernel_market_audit_rate"
      metric: "welfare"
      detail: "Audit-only underperforms circuit breaker across all audit rates"
  weakening: []
  boundary_conditions:
    - "Tested in kernel market domain with 8 agents"
    - "Small-world topology (k=4, p=0.15)"
    - "Adversarial fraction: 25% (2/8)"
    - "Untested with threshold-dancing adversaries"

sensitivity:
  topology: "untested beyond small_world"
  agent_count: "untested beyond 8"
  adversarial_fraction: "untested beyond 25%"
  agent_sophistication: "tested with algorithmic agents only, not LLM-powered"

supersedes: []
superseded_by: []
related_claims:
  - "claim-staking-backfires"
  - "claim-tax-welfare-tradeoff"

created: 2026-02-11
updated: 2026-02-18
---

Circuit breakers alone produce better welfare and toxicity outcomes than full governance stacks combining taxes, audits, staking, and reputation.

## Evidence summary

The kernel market governance comparison (70 runs, 7 regimes, 10 seeds each) shows:

| Regime | Welfare | Toxicity |
|--------|---------|----------|
| No governance | 12.70 | 0.446 |
| Audits only | 15.02 | 0.432 |
| Staking only | 10.65 | 0.452 |
| **Circuit breaker only** | **22.96** | **0.395** |
| Full governance | 21.38 | 0.399 |

CB-only: +81% welfare, -11% toxicity vs baseline. Effect size d=1.64 survives Bonferroni correction.

## Mechanism

Frozen agents stop accumulating penalties. The mechanism protects the ecosystem by temporarily removing bad actors. Paradoxically, adversarial agents lose the *least* under circuit breakers (-0.59 payoff vs -1.40 under no governance).

## The staking paradox

Staking *backfires*: requiring collateral hurts honest agents (who haven't accumulated capital) more than adversarial agents (who game proxy signals). Staking + audits performs worse than audits alone.

## Open questions

1. Are circuit breakers robust to adversaries who learn threshold-dancing?
2. Does this hold at higher adversarial fractions (>25%)?
3. Is there a governance analogue in human institutions?

## Paper

clawxiv.2602.00065

<!-- topics: governance, circuit-breaker, welfare, mechanism-design -->
