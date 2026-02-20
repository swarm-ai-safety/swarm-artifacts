#!/usr/bin/env python3
"""
Claim dependency graph generator — visualize relationships between claims.

Parses YAML frontmatter from vault/claims/claim-*.md and builds a dependency
graph showing related_claims, supersedes/superseded_by edges, and optionally
shared evidence (run nodes).

Usage:
    python scripts/claim-graph.py                        # Mermaid to stdout
    python scripts/claim-graph.py --format dot           # Graphviz DOT
    python scripts/claim-graph.py --format mermaid       # Mermaid (default)
    python scripts/claim-graph.py --output vault/claims/claim-graph.md
    python scripts/claim-graph.py --include-runs         # Show run evidence nodes
"""

import argparse
import re
import sys
from datetime import date
from pathlib import Path

import yaml

ROOT = Path(__file__).parent.parent
CLAIMS_DIR = ROOT / "vault" / "claims"

# ---------------------------------------------------------------------------
# Styling maps
# ---------------------------------------------------------------------------

CONFIDENCE_COLORS = {
    "high": "green",
    "medium": "orange",
    "low": "red",
    "contested": "purple",
}

CONFIDENCE_MERMAID = {
    "high": "#2ecc71",
    "medium": "#f39c12",
    "low": "#e74c3c",
    "contested": "#9b59b6",
}

# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def parse_frontmatter(path: Path) -> dict | None:
    """Extract YAML frontmatter from a markdown file."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return None
    match = re.match(r"^---\n(.+?)\n---", text, re.DOTALL)
    if not match:
        return None
    try:
        data = yaml.safe_load(match.group(1))
    except yaml.YAMLError:
        return None
    if not isinstance(data, dict):
        return None
    return data


def load_claims() -> dict[str, dict]:
    """Load all claim files. Returns {claim_id: frontmatter}."""
    claims: dict[str, dict] = {}
    if not CLAIMS_DIR.exists():
        return claims
    for path in sorted(CLAIMS_DIR.glob("claim-*.md")):
        fm = parse_frontmatter(path)
        if fm is None:
            continue
        claim_id = path.stem
        fm["_id"] = claim_id
        claims[claim_id] = fm
    return claims


# ---------------------------------------------------------------------------
# Graph building
# ---------------------------------------------------------------------------

def extract_run_ids(evidence_list: list | None) -> list[str]:
    """Pull run IDs from an evidence list."""
    ids = []
    if not evidence_list:
        return ids
    for entry in evidence_list:
        if isinstance(entry, dict) and entry.get("run"):
            ids.append(str(entry["run"]))
    return ids


def build_graph(claims: dict[str, dict], include_runs: bool = False):
    """Build nodes and edges from parsed claims.

    Returns (nodes, edges) where:
      nodes = [{id, label, confidence, domain, kind}]
      edges = [{src, dst, style, label, directed}]
    """
    nodes: list[dict] = []
    edges: list[dict] = []
    seen_edges: set[tuple] = set()
    all_claim_ids = set(claims.keys())

    # Collect run->claims mapping for shared-evidence edges
    run_to_claims: dict[str, list[str]] = {}

    for cid, fm in claims.items():
        confidence = fm.get("confidence", "medium")
        domain = fm.get("domain", "unknown")
        status = fm.get("status", "active")
        label = cid.replace("claim-", "")
        nodes.append({
            "id": cid,
            "label": label,
            "confidence": confidence,
            "domain": domain,
            "status": status,
            "kind": "claim",
        })

        # related_claims -> bidirectional dashed
        for related in fm.get("related_claims", []) or []:
            related = str(related)
            key = tuple(sorted([cid, related]))
            if key not in seen_edges:
                seen_edges.add(key)
                edges.append({
                    "src": cid, "dst": related,
                    "style": "dashed", "label": "",
                    "directed": False,
                })

        # supersedes -> directed solid (cid supersedes target)
        for target in fm.get("supersedes", []) or []:
            target = str(target)
            edge_key = ("supersedes", cid, target)
            if edge_key not in seen_edges:
                seen_edges.add(edge_key)
                edges.append({
                    "src": cid, "dst": target,
                    "style": "solid", "label": "supersedes",
                    "directed": True,
                })

        # superseded_by -> directed solid (source supersedes cid)
        for source in fm.get("superseded_by", []) or []:
            source = str(source)
            edge_key = ("supersedes", source, cid)
            if edge_key not in seen_edges:
                seen_edges.add(edge_key)
                edges.append({
                    "src": source, "dst": cid,
                    "style": "solid", "label": "supersedes",
                    "directed": True,
                })

        # Collect evidence runs
        evidence = fm.get("evidence", {})
        if isinstance(evidence, dict):
            for run_id in extract_run_ids(evidence.get("supporting", [])):
                run_to_claims.setdefault(run_id, []).append(cid)
            for run_id in extract_run_ids(evidence.get("weakening", [])):
                run_to_claims.setdefault(run_id, []).append(cid)

    # Shared evidence edges (same run_id appears in multiple claims)
    for run_id, cids in run_to_claims.items():
        unique_cids = sorted(set(cids))
        if len(unique_cids) >= 2:
            for i in range(len(unique_cids)):
                for j in range(i + 1, len(unique_cids)):
                    key = ("shared", unique_cids[i], unique_cids[j], run_id)
                    if key not in seen_edges:
                        seen_edges.add(key)
                        edges.append({
                            "src": unique_cids[i], "dst": unique_cids[j],
                            "style": "dotted", "label": run_id,
                            "directed": False,
                        })

    # Optionally add run nodes
    if include_runs:
        for run_id, cids in run_to_claims.items():
            nodes.append({
                "id": run_id, "label": run_id,
                "confidence": "", "domain": "runs",
                "status": "", "kind": "run",
            })
            for cid in sorted(set(cids)):
                edges.append({
                    "src": run_id, "dst": cid,
                    "style": "dotted", "label": "evidence",
                    "directed": True,
                })

    return nodes, edges


# ---------------------------------------------------------------------------
# Mermaid output
# ---------------------------------------------------------------------------

def sanitize_mermaid_id(s: str) -> str:
    """Make a string safe for use as a Mermaid node ID."""
    return re.sub(r"[^a-zA-Z0-9_]", "_", s)


def render_mermaid(nodes: list[dict], edges: list[dict]) -> str:
    """Render the graph as a Mermaid diagram."""
    lines = ["graph LR"]

    # Group nodes by domain
    domains: dict[str, list[dict]] = {}
    for n in nodes:
        domains.setdefault(n["domain"], []).append(n)

    for domain, domain_nodes in sorted(domains.items()):
        lines.append(f"    subgraph {sanitize_mermaid_id(domain)}[\"{domain}\"]")
        for n in domain_nodes:
            nid = sanitize_mermaid_id(n["id"])
            label = n["label"]
            if n["kind"] == "run":
                lines.append(f"        {nid}[/\"{label}\"/]")
            else:
                lines.append(f"        {nid}[\"{label}\"]")
        lines.append("    end")

    lines.append("")

    # Edges
    for e in edges:
        src = sanitize_mermaid_id(e["src"])
        dst = sanitize_mermaid_id(e["dst"])
        label = e["label"]
        if e["style"] == "dashed" and not e["directed"]:
            if label:
                lines.append(f"    {src} -.-|{label}| {dst}")
            else:
                lines.append(f"    {src} -.- {dst}")
        elif e["style"] == "solid" and e["directed"]:
            if label:
                lines.append(f"    {src} -->|{label}| {dst}")
            else:
                lines.append(f"    {src} --> {dst}")
        elif e["style"] == "dotted":
            if label:
                lines.append(f"    {src} -..->|{label}| {dst}")
            else:
                lines.append(f"    {src} -..-> {dst}")
        else:
            lines.append(f"    {src} --- {dst}")

    lines.append("")

    # Style nodes by confidence
    for n in nodes:
        if n["kind"] != "claim":
            continue
        color = CONFIDENCE_MERMAID.get(n["confidence"])
        if color:
            nid = sanitize_mermaid_id(n["id"])
            lines.append(f"    style {nid} fill:{color},stroke:#333,color:#fff")

    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Graphviz DOT output
# ---------------------------------------------------------------------------

def render_dot(nodes: list[dict], edges: list[dict]) -> str:
    """Render the graph as Graphviz DOT."""
    lines = ["digraph claims {", "    rankdir=LR;", "    node [shape=box, style=filled];", ""]

    # Group by domain as subgraphs
    domains: dict[str, list[dict]] = {}
    for n in nodes:
        domains.setdefault(n["domain"], []).append(n)

    for idx, (domain, domain_nodes) in enumerate(sorted(domains.items())):
        lines.append(f"    subgraph cluster_{idx} {{")
        lines.append(f'        label="{domain}";')
        for n in domain_nodes:
            nid = sanitize_mermaid_id(n["id"])
            label = n["label"]
            color = CONFIDENCE_COLORS.get(n["confidence"], "gray")
            if n["kind"] == "run":
                lines.append(
                    f'        {nid} [label="{label}", shape=ellipse, '
                    f'fillcolor=lightblue];'
                )
            else:
                lines.append(
                    f'        {nid} [label="{label}", fillcolor={color}, '
                    f'fontcolor=white];'
                )
        lines.append("    }")

    lines.append("")

    # Edges
    for e in edges:
        src = sanitize_mermaid_id(e["src"])
        dst = sanitize_mermaid_id(e["dst"])
        attrs = []
        if e["label"]:
            attrs.append(f'label="{e["label"]}"')
        if e["style"] == "dashed":
            attrs.append('style=dashed')
            if not e["directed"]:
                attrs.append("dir=none")
        elif e["style"] == "dotted":
            attrs.append('style=dotted')
            if not e["directed"]:
                attrs.append("dir=none")
        elif not e["directed"]:
            attrs.append("dir=none")
        attr_str = f" [{', '.join(attrs)}]" if attrs else ""
        lines.append(f"    {src} -> {dst}{attr_str};")

    lines.append("}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Vault note wrapper
# ---------------------------------------------------------------------------

def wrap_vault_note(mermaid_text: str) -> str:
    """Wrap Mermaid diagram in a vault note with frontmatter."""
    today = date.today().isoformat()
    return (
        f"---\n"
        f'description: "Visual dependency graph of all claim relationships and evidence chains"\n'
        f"type: method\n"
        f"status: active\n"
        f"created: {today}\n"
        f"updated: {today}\n"
        f"---\n\n"
        f"# Claim relationship and evidence dependency graph\n\n"
        f"Auto-generated by `scripts/claim-graph.py`.\n\n"
        f"```mermaid\n{mermaid_text}```\n\n"
        f"<!-- topics: claims, evidence, graph, methods -->\n"
    )


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Generate a visual dependency graph of claim relationships"
    )
    parser.add_argument(
        "--format", choices=["mermaid", "dot"], default="mermaid",
        help="Output format (default: mermaid)",
    )
    parser.add_argument(
        "--output", type=str, default=None,
        help="Write output to file; if .md, wraps as vault note with embedded Mermaid",
    )
    parser.add_argument(
        "--include-runs", action="store_true", dest="include_runs",
        help="Also show run nodes connected to claims via evidence",
    )
    args = parser.parse_args()

    claims = load_claims()
    if not claims:
        print("No claim files found in", CLAIMS_DIR, file=sys.stderr)
        sys.exit(1)

    nodes, edges = build_graph(claims, include_runs=args.include_runs)

    if args.format == "dot":
        output = render_dot(nodes, edges)
    else:
        output = render_mermaid(nodes, edges)

    # Write to file or stdout
    if args.output:
        out_path = Path(args.output)
        if not out_path.is_absolute():
            out_path = ROOT / out_path
        out_path.parent.mkdir(parents=True, exist_ok=True)
        if out_path.suffix == ".md":
            # Vault note: always embed as Mermaid regardless of --format
            mermaid_text = render_mermaid(nodes, edges) if args.format != "mermaid" else output
            out_path.write_text(wrap_vault_note(mermaid_text), encoding="utf-8")
        else:
            out_path.write_text(output, encoding="utf-8")
        print(f"Wrote {out_path}", file=sys.stderr)
    else:
        sys.stdout.write(output)


if __name__ == "__main__":
    main()
