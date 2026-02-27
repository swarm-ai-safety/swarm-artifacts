---
description: 2x3x2 factorial comparing LLM vs algorithmic agent governance sensitivity under adversarial conditions, 180 runs
type: experiment
status: proposed
run_id: pending
experiment_type: study
created: '2026-02-27'
aliases:
- proposed-llm-sensitivity
cssclasses:
- experiment
- experiment-study
tags:
- llm
- algorithmic
- governance-sensitivity
- adversarial
graph-group: experiment
---

# LLM agents may show governance sensitivity only when adversarial agents force behavioral differentiation

## Design

- **Hypothesis**: The memori_study null (0/12 governance tests significant) may be an artifact of all-honest populations and 2-epoch horizons. LLM agents with adversarial peers and extended horizons should show governance sensitivity comparable to algorithmic agents, or the null reflects a fundamental LLM behavioral regime.
- **Type**: 3-factor study (architecture x governance x adversarial fraction)
- **Factor 1**: Agent architecture — algorithmic-RLM, LLM
- **Factor 2**: Governance level — none, CB-only, full-stack
- **Factor 3**: Adversarial fraction — 0%, 20%
- **Seeds**: 15
- **Total runs**: 180 (2 architectures x 3 governance levels x 2 adversarial fractions x 15 seeds)
- **Config**: 10 agents, 15 epochs (extended from memori's 2), small-world
- **Scenario**: `scenarios/hypotheses/llm_governance_sensitivity.yaml`

## Motivation

[[claim-memori-agents-show-no-governance-sensitivity]] shows zero governance response in all-honest LLM populations (0/12 tests significant, largest d=0.55). [[claim-agent-architecture-constrains-behavior-more-than-governance]] synthesizes this with algorithmic agent findings to suggest architecture dominates governance. But the memori study had two critical limitations: (1) all-honest population (no adversarial agents to differentiate against) and (2) only 2 epochs (insufficient time for governance effects to accumulate). This study controls both factors.

## Expected claims

- **New**: Claim on architecture x governance interaction (the central finding)
- **New**: Claim on adversarial fraction as a moderator of governance sensitivity
- **Update**: [[claim-memori-agents-show-no-governance-sensitivity]] — either confirmed as fundamental or restricted to all-honest/short-horizon boundary
- **Update**: [[claim-agent-architecture-constrains-behavior-more-than-governance]] — enriched with controlled architecture comparison

## Prerequisites

- SWARM must support LLM-based agents with adversarial behavior prompts
- LLM API access for 180 runs x 15 epochs = 2700 LLM-epoch-runs (significant compute)
- Algorithmic RLM agents must run in same framework for controlled comparison
- Extended horizon (15 epochs) requires stable LLM behavior over longer sequences

## Analysis plan

- Three-way ANOVA (architecture x governance x adversarial) on each metric, Bonferroni-corrected (k=4 metrics)
- Key interaction: architecture x governance — does governance sensitivity differ by architecture?
- Secondary interaction: architecture x governance x adversarial — does adversarial presence unlock LLM governance sensitivity?
- Effect size comparison: Cohen's d for governance level contrasts within each architecture

## Falsification

If LLM agents show equivalent governance sensitivity to algorithmic agents (no significant architecture x governance interaction), the memori null is a sample-size artifact and LLMs are not behaviorally distinct from algorithmic agents under governance.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: llm, algorithmic, governance-sensitivity, adversarial, architecture -->
