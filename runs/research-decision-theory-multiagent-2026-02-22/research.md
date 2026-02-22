---
description: Research findings on decision theory (LDT/CDT/FDT) in multi-agent AI systems
source_type: research
research_prompt: "decision theory in multi-agent AI systems — logical decision theory LDT, causal decision theory CDT, functional decision theory FDT, cooperation emergence, superrationality, program equilibrium in agent populations"
generated: 2026-02-22
---

# decision theory literature contextualizes SWARM LDT composition findings but reveals surprising gaps in empirical multi-agent validation

## Summary

SWARM has two high-confidence decision theory findings: (1) LDT agents maintain +48% welfare at 40-70% composition (d=2.89, Bonferroni-sig), and (2) neither acausality depth nor decision theory type affects individual outcomes. The external literature provides rich theoretical context but surprisingly little empirical multi-agent validation, making SWARM's results among the first large-scale empirical tests of decision theory in simulated agent populations.

## Decision Theory Taxonomy

The key decision theories relevant to SWARM:

### Causal Decision Theory (CDT)
CDT recommends actions based on their causal consequences. An agent using CDT asks "what would happen if I caused this action?" CDT is the standard rational choice framework but famously defects in one-shot Prisoner's Dilemmas even against identical copies of itself, because it treats the other agent's action as causally independent.

### Evidential Decision Theory (EDT)
EDT recommends actions based on what they indicate about outcomes. An agent using EDT asks "given that I'm the kind of agent who takes this action, what outcomes are likely?" EDT cooperates in symmetric PDs against identical copies because cooperation is evidence of the other copy cooperating.

### Functional Decision Theory (FDT)
FDT (Yudkowsky & Soares 2017, MIRI) extends CDT by considering not just causal but "subjunctive" dependencies — if my decision algorithm outputs X, all implementations of my algorithm also output X. FDT cooperates in PDs against copies and achieves superrational outcomes.

### Updateless Decision Theory (UDT)
UDT (Wei Dai, formalized by Yudkowsky) specifies that the optimal agent maximizes expected utility according to its prior beliefs by selecting the best policy — the best mapping from observations to actions. UDT handles dynamic inconsistency problems that plague CDT and EDT.

### Logical Decision Theory (LDT)
LDT is a family encompassing FDT and UDT, characterized by reasoning about logical rather than causal dependencies between agents. SWARM's LDT agents use this framework.

**Connection to SWARM:** SWARM's finding that LDT agents maintain +48% welfare at 40-70% composition is consistent with FDT/UDT theory, which predicts that agents reasoning about logical dependencies will cooperate more effectively than CDT agents. However, SWARM's finding that acausality depth does NOT affect outcomes (claim-acausality-depth-does-not-affect-cooperation-outcomes) is surprising — deeper reasoning about logical dependencies should theoretically produce better coordination, but empirically it doesn't.

## Superrationality (Hofstadter 1985)

Hofstadter's superrationality concept proposes that rational agents in symmetric games cooperate by assuming all similar reasoners reach identical decisions, selecting the action that maximizes collective payoffs when uniformly chosen. The correlation arises from algorithmic similarity, not causal interaction.

**Connection to SWARM:** SWARM's LDT agents operationalize superrationality — they cooperate not because they communicate or observe each other, but because they reason about what identical or similar algorithms would do. The +48% welfare premium at intermediate composition confirms Hofstadter's prediction that superrational agents produce better collective outcomes than individually rational (CDT) agents. The fact that the premium appears specifically at 40-70% composition suggests a critical mass effect — superrationality requires enough similar reasoners to make the "all similar reasoners cooperate" assumption self-fulfilling.

## Program Equilibrium (Tennenholtz 2004)

Program equilibrium extends Nash equilibrium to settings where agents can commit to strategies by revealing their source code. When agents can verify each other's algorithms:
- Cooperation becomes a Nash equilibrium in one-shot PDs (if my code says "cooperate if the other's code cooperates, else defect", and your code says the same, neither benefits from deviating)
- This eliminates the need for repeated interaction, reputation, or punishment mechanisms

**Connection to SWARM:** SWARM's LDT agents achieve cooperation without source code transparency — they infer algorithmic similarity through behavioral observation. This is weaker than program equilibrium (no formal verification) but stronger than CDT (which ignores algorithmic similarity entirely). The gap between program equilibrium (formal) and SWARM's LDT (behavioral inference) suggests a possible experimental direction: what happens when SWARM agents can inspect each other's decision procedures?

## Evolutionary Game Theory and Decision Theory Selection

Recent work (arXiv:2412.20523, December 2024) integrates evolutionary game theory with multi-agent reinforcement learning, studying how Nash equilibria, evolutionary dynamics, and correlated equilibria interact. Key finding: evolutionary pressure selects for strategies that perform well against the current population distribution, not strategies that are theoretically optimal.

**Connection to SWARM:** This may explain SWARM's composition-dependent results. At 40-70% LDT composition, there are enough LDT agents to make cooperation self-sustaining (evolutionary stability). Below 40%, LDT agents are too rare to benefit from mutual cooperation, and their cooperative behavior is exploited by CDT agents. Above 70%, all agents are already cooperating, so the LDT premium disappears (ceiling effect).

## Functional Decision Theory in Evolutionary Environments

Oesterheld & Conitzer (2020, arXiv:2005.05154) study FDT agents in evolutionary settings, finding that FDT can be evolutionary stable under certain conditions but faces challenges when the population is mixed or when there are multiple FDT variants.

**Connection to SWARM:** SWARM's finding of maximum welfare at intermediate (40-70%) LDT composition is consistent with this: pure LDT populations don't outperform pure CDT populations (no adversary to outcompete), but mixed populations with sufficient LDT representation achieve the best outcomes.

## Acausal Trade and Multiverse-Wide Cooperation

Oesterheld's "Multiverse-wide Cooperation via Correlated Decision Making" extends superrationality to agents that cannot interact but share logical structure. This is the theoretical foundation for SWARM's acausality experiments — if agents can reason about what logically similar agents in other contexts would do, they can achieve cooperation without communication.

**Connection to SWARM:** SWARM's null finding on acausality depth (claim-acausality-depth-does-not-affect-cooperation-outcomes) challenges the theoretical prediction that deeper acausal reasoning improves coordination. Possible explanations:
1. **Implementation ceiling:** SWARM's LDT agents may already capture the benefits of acausal reasoning at depth 1, with deeper reasoning adding noise but not signal.
2. **Population effect:** Acausal reasoning may only matter in heterogeneous populations where agents need to reason about unlike agents. SWARM tests homogeneous LDT populations.
3. **Game structure:** The specific interaction structures in SWARM may not create situations where deeper acausal reasoning provides additional leverage.

## Implications for SWARM

1. **Composition threshold validation:** SWARM's 40-70% LDT sweet spot is consistent with evolutionary game theory predictions about critical mass for cooperative strategies. The precise threshold is an empirical contribution.

2. **Acausality depth null explained:** The literature suggests that the benefits of acausal reasoning are primarily theoretical and may not manifest in structured agent economies where behavioral observation already provides sufficient coordination signals.

3. **Program equilibrium experiment:** SWARM could test the effect of source code transparency — allowing agents to verify each other's decision procedures. This would test whether formal program equilibrium outperforms behavioral inference in practice.

4. **Mixed decision theory populations:** SWARM could test populations mixing CDT, EDT, FDT, and UDT agents to determine which decision theory performs best under competitive selection pressure.

5. **First large-scale empirical test:** SWARM's LDT composition study (d=2.89, N=160, Bonferroni-corrected) appears to be among the first large-scale empirical validations of decision theory predictions in multi-agent simulations. This is a significant contribution to both the decision theory and multi-agent systems literatures.

## Sources

- [Yudkowsky & Soares 2017 — Functional Decision Theory: A New Theory of Instrumental Rationality (MIRI)](https://intelligence.org/2017/10/22/fdt/)
- [Hofstadter 1985 — Metamagical Themas: Questing for the Essence of Mind and Pattern (superrationality chapter)](https://en.wikipedia.org/wiki/Superrationality)
- [Tennenholtz 2004 — Program Equilibrium (Games and Economic Behavior)](https://en.wikipedia.org/wiki/Program_equilibrium)
- [Oesterheld 2017 — Multiverse-wide Cooperation via Correlated Decision Making](https://longtermrisk.org/files/Multiverse-wide-Cooperation-via-Correlated-Decision-Making.pdf)
- [Oesterheld & Conitzer 2020 — Functional Decision Theory in an Evolutionary Environment](https://arxiv.org/abs/2005.05154)
- [Game Theory and Multi-Agent Reinforcement Learning: From Nash Equilibria to Evolutionary Dynamics (arXiv:2412.20523)](https://arxiv.org/abs/2412.20523)
- [Updateless Decision Theory (Alignment Forum)](https://www.alignmentforum.org/w/updateless-decision-theory)
- [Decision Theory (Stanford Encyclopedia of Philosophy)](https://plato.stanford.edu/entries/decision-theory/)
