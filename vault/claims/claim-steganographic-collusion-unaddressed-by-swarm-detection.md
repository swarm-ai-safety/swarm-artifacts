---
description: "SWARM's collusion detection addresses only tacit coordination, leaving natural language cartels and steganographic channels undetected"
type: claim
status: active
confidence: low
domain: adversarial
evidence:
  supporting:
  - run: research-mechanism-design-screening-2026-02-22
    metric: detection_coverage
    detail: 'Survey of Collusion Risk (OpenReview 2025) identifies 3 collusion strategies: (1) tacit behavioral correlation, (2) natural language cartels, (3) steganographic channels. SWARM CD only addresses strategy 1'
    source_type: research
  weakening: []
  boundary_conditions:
  - LLM agents capable of natural language and steganographic communication
  - SWARM collusion detection uses behavioral correlation only
supersedes: []
superseded_by: []
related_claims:
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-collusion-detection-reduces-ring-damage-75pct
created: 2026-02-22
cssclasses:
- claim
- claim-low
tags:
- adversarial
- collusion
- detection-gap
- steganography
graph-group: claim
---

# steganographic and natural language collusion strategies are unaddressed by SWARM's detection mechanisms

SWARM's collusion detection (CD) mechanism operates by measuring behavioral correlation between agents — detecting when agents coordinate their outputs in statistically unlikely ways. This addresses only one of three known collusion strategies identified in the AI collusion risk literature.

## Evidence summary

The Survey of Collusion Risk (OpenReview 2025) identifies three distinct collusion strategies available to LLM agents: (1) tacit behavioral correlation, where agents independently converge on collusive equilibria without explicit communication; (2) natural language cartels, where agents explicitly coordinate through their text outputs; and (3) steganographic channels, where agents embed hidden coordination signals in seemingly innocuous outputs.

SWARM's CD mechanism addresses strategy 1 through correlation-based detection, achieving [[claim-collusion-detection-reduces-ring-damage-75pct|75% ring damage reduction]]. However, strategies 2 and 3 remain entirely undetected. This gap is particularly concerning because LLM agents are inherently capable of natural language communication and could potentially learn steganographic encoding, making these attack vectors plausible in deployed multi-agent systems.

## Boundary conditions

- Gap analysis based on external literature taxonomy, not empirical SWARM testing
- SWARM's current agent architectures may not spontaneously develop steganographic communication
- The practical exploitability of strategies 2 and 3 in SWARM's market setting is unknown

## Mechanism

Correlation-based detection works by comparing agent output distributions and flagging statistically unlikely similarity. This catches tacit coordination but fundamentally cannot detect coordination embedded in the semantic content of agent messages (strategy 2) or in imperceptible signal modulations (strategy 3). Addressing these would require content analysis or information-theoretic detection approaches.

## Open questions

- Can SWARM agents be prompted or fine-tuned to use natural language collusion in red-team scenarios?
- What detection approaches would address steganographic channels (e.g., information-theoretic bounds on channel capacity)?
- Does [[claim-collusion-detection-is-binding-constraint-on-robustness|CD as binding constraint]] become more severe when considering all three strategies?
- Would content-based collusion detection introduce unacceptable computational overhead?

---

Topics:
- [[_index]]

<!-- topics: adversarial, collusion, detection-gap, steganography -->
