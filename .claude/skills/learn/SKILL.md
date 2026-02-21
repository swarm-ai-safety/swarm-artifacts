---
name: learn
description: Research a topic relevant to SWARM AI safety and grow the vault with findings. Queries external sources, synthesizes into claim candidates, follows the extraction pipeline. Triggers on "/learn", "/learn [topic]", "research this", "find papers on".
user-invocable: true
allowed-tools: Read, Write, Glob, Bash, mcp__qmd__vector_search
context: fork
---

## Runtime Configuration (Step 0)

Read `vault/ops/derivation-manifest.md` for research settings.
Default research depth: deep (AI safety domain, from config).

---

## EXECUTE NOW

**Target: $ARGUMENTS**

- If target is a topic: research that topic using available tools
- If target is empty: ask "What topic should I research?"

---

# Learn

Research a topic and grow the SWARM knowledge graph with findings.

## Research Priority Areas

Topics most likely to yield governance claims:
- Multi-agent mechanism design
- Distributional AI safety
- Collusion detection algorithms
- Adversarial robustness in cooperative systems
- Welfare economics in AI systems
- Network topology effects on agent behavior

## Workflow

1. **Formulate search queries** — what specific aspect, what evidence would be decisive
2. **Research using available tools** — web search, arXiv, semantic scholar
3. **Create inbox item** — save research findings to `runs/research-[topic]-[date].md`
4. **Run /extract on the file** — process research into claim candidates
5. **Run /cross-link** — connect new claims to existing vault

## Research File Format (in runs/)

```markdown
---
description: Research findings on [topic]
source_type: research
research_prompt: "[the query used]"
generated: YYYY-MM-DD
---

# [Topic] — research findings

[Synthesized findings from sources]

## Sources

- [Author et al. Year — title](url)
- ...
```

After creating the research file, run `/extract [path-to-file]` to process it into claims.

## Quality Gates for Research-Sourced Claims

Research-sourced claims have lower initial confidence until validated by SWARM experiments:
- Research finding → `confidence: low` until replicated in SWARM runs
- SWARM experiment confirms research → `confidence: medium` or `high` based on criteria
- Document the chain: external source → research note → claim → SWARM validation
