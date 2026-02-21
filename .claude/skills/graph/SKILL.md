---
name: graph
description: Explore and analyze the SWARM knowledge graph — detect orphan claims, find dense connection clusters, trace evidence chains, identify synthesis opportunities. Triggers on "/graph", "graph analysis", "find orphans", "what connects to X".
user-invocable: true
allowed-tools: Read, Glob, Grep, Bash, mcp__qmd__deep_search
context: fork
---

## EXECUTE NOW

**Target: $ARGUMENTS**

- If empty: run full graph health report
- If "orphans": detect claims with no incoming links
- If "clusters": find dense connection clusters (potential synthesis opportunities)
- If "trace [claim]": trace all evidence chains involving that claim
- If "backlinks [claim]": find everything that cites that claim

---

# Graph

Analyze the SWARM knowledge graph structure.

## Core Queries

### Orphan Detection

```bash
# Claims with no incoming wiki-links from other claims
for f in vault/claims/*.md; do
  name=$(basename "$f" .md)
  count=$(rg "\[\[$name\]\]" vault/claims/ vault/experiments/ vault/failures/ vault/governance/ vault/methods/ vault/sweeps/ --include="*.md" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$count" -eq 0 ]; then
    echo "ORPHAN: $name"
  fi
done
```

### Link Density

```bash
# Top 10 most-cited claims (knowledge hubs)
for f in vault/claims/*.md; do
  name=$(basename "$f" .md)
  count=$(rg "\[\[$name\]\]" vault/ --include="*.md" 2>/dev/null | wc -l | tr -d ' ')
  echo "$count $name"
done | sort -rn | head -10
```

### Evidence Chain Trace

For a given claim, trace the evidence chain:
1. Find the claim's run_id references
2. Check if those runs have experiment notes
3. Check what other claims cite the same run_id
4. Surface the full evidence provenance

### Cross-Domain Connections

```bash
# Find claims citing claims from different domains
# (governance claim citing topology claim, etc.)
rg '^domain: ' vault/claims/*.md
```

### Synthesis Opportunities

Using semantic search, find claim pairs that make complementary arguments not yet connected:

```
mcp__qmd__deep_search  query="[governance mechanism interaction not yet linked]"  collection="vault"  limit=10
```

## Output Format

```
Graph Report — SWARM Research OS

Orphans: N claims with no incoming links
  - [claim name] (no citations)
  ...

Top hubs (most cited):
  1. [claim] — N citations
  2. [claim] — N citations
  ...

Synthesis opportunities:
  - [[claim A]] + [[claim B]] — complementary mechanisms not yet connected
  ...

Evidence chain density:
  Claims with 0 supporting runs: N
  Claims with 1 supporting run:  N
  Claims with 2+ supporting runs: N
```
