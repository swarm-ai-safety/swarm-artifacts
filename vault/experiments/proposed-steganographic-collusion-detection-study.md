---
description: 3x3 factorial testing content-analysis and leniency detection against steganographic and NL collusion, 180 runs
type: experiment
status: proposed
run_id: pending
experiment_type: study
created: '2026-02-27'
aliases:
- proposed-stego-collusion
cssclasses:
- experiment
- experiment-study
tags:
- collusion-detection
- steganographic
- leniency
- content-analysis
graph-group: experiment
---

# content-based detection and leniency programs should catch steganographic and natural-language collusion that behavioral correlation misses

## Design

- **Hypothesis**: Current behavioral correlation detection addresses only tacit coordination (1 of 3 collusion strategies). Content-based analysis can detect steganographic channels, and leniency programs can break natural-language cartels through defection incentives.
- **Type**: 2-factor study (collusion strategy x detection method)
- **Factor 1**: Collusion strategy — behavioral-only, steganographic-channel, NL-cartel
- **Factor 2**: Detection method — behavioral-correlation (current), content-analysis (new), leniency-program (new)
- **Seeds**: 20
- **Total runs**: 180 (3 strategies x 3 methods x 20 seeds)
- **Config**: 10 agents (6 honest + 2 colluding-adversarial + 2 opportunistic), tax 3%, CB enabled, small-world
- **Scenario**: `scenarios/hypotheses/steganographic_collusion_detection.yaml`

## Motivation

[[claim-steganographic-collusion-unaddressed-by-swarm-detection]] identifies that 2 of 3 collusion strategies are completely undefended. [[claim-leniency-whistleblowing-is-untested-governance-lever]] notes that leniency programs (a major anti-collusion tool in competition law) have never been tested in SWARM. [[claim-collusion-detection-is-binding-constraint-on-robustness]] shows collusion detection is the binding constraint on system robustness — improving it has the highest marginal safety return.

## Expected claims

- **New**: Claim on content-analysis detection efficacy against steganographic collusion
- **New**: Claim on leniency program effectiveness against NL cartels
- **New**: Claim on detection method x strategy interaction (method specialization)
- **Update**: [[claim-steganographic-collusion-unaddressed-by-swarm-detection]] — either resolved or confirmed unresolvable
- **Update**: [[claim-leniency-whistleblowing-is-untested-governance-lever]] — tested, moved from low to medium/high
- **Update**: [[claim-collusion-detection-is-binding-constraint-on-robustness]] — enriched with multi-method comparison

## Prerequisites

- SWARM must implement `steganographic_channel` and `nl_cartel` collusion strategies for adversarial agents
- Content-analysis detection requires semantic analysis module
- Leniency program requires whistleblower incentive mechanism (immunity + reward)
- ROC curve computation requires varying detection sensitivity parameters

## Analysis plan

- Two-way ANOVA (strategy x detection) on each metric, Bonferroni-corrected (k=5 metrics)
- ROC curves for each detection method across each collusion strategy
- Detection latency comparison: epochs to first detection by method and strategy
- Cost-benefit: false positive rate vs detection power per method

## Falsification

If content-analysis and leniency show no improvement over behavioral-correlation for steganographic/NL collusion, the detection gap may be fundamental rather than a missing tool.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: collusion-detection, steganographic, leniency, content-analysis -->
