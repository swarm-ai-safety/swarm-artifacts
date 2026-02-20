#!/usr/bin/env python3
"""
Sync SWARM vault frontmatter into Dolt tables.

Reads all vault notes, extracts frontmatter, and upserts into
vault_claims and vault_suggestions tables in Dolt via MySQL protocol.

Usage:
    python scripts/vault-to-dolt.py                    # Sync to localhost:3306
    python scripts/vault-to-dolt.py --host 127.0.0.1   # Custom host
    python scripts/vault-to-dolt.py --dry-run           # Show SQL without executing
    python scripts/vault-to-dolt.py --commit            # Auto-commit after sync

Requires: pip install pymysql
"""

import argparse
import sys
from datetime import datetime
from pathlib import Path

import yaml

try:
    import pymysql
except ImportError:
    print("Install pymysql: pip install pymysql")
    sys.exit(1)

VAULT_DIR = Path(__file__).parent.parent / "vault"
STALE_DAYS = 14
DATABASE = "dolt_runs"


def load_notes(folder: str | None = None) -> list[dict]:
    """Load all markdown notes with YAML frontmatter."""
    root = VAULT_DIR / folder if folder else VAULT_DIR
    notes = []
    for md in root.rglob("*.md"):
        if ".obsidian" in md.parts or "templates" in md.parts:
            continue
        text = md.read_text(encoding="utf-8", errors="replace")
        if not text.startswith("---"):
            continue
        end = text.find("---", 3)
        if end == -1:
            continue
        try:
            fm = yaml.safe_load(text[3:end])
        except yaml.YAMLError:
            continue
        if not isinstance(fm, dict):
            continue
        fm["_name"] = md.stem
        fm["_folder"] = str(md.parent.relative_to(VAULT_DIR))
        fm["_file"] = md
        notes.append(fm)
    return notes


def count_inlinks(notes: list[dict]) -> dict[str, int]:
    """Count wikilink inlinks for each note."""
    counts: dict[str, int] = {n["_name"]: 0 for n in notes}
    for n in notes:
        text = n["_file"].read_text(encoding="utf-8", errors="replace")
        for target in counts:
            if f"[[{target}]]" in text and target != n["_name"]:
                counts[target] += 1
    return counts


def build_claims(notes: list[dict]) -> list[dict]:
    """Extract claim rows from vault notes."""
    rows = []
    for n in notes:
        if n.get("type") != "claim":
            continue
        rows.append({
            "name": n["_name"],
            "confidence": n.get("confidence", "unknown"),
            "domain": n.get("domain", "unknown"),
            "status": n.get("status", "unknown"),
            "supporting_runs": len(n.get("evidence", {}).get("supporting", [])),
            "weakening_runs": len(n.get("evidence", {}).get("weakening", [])),
            "boundary_conditions": len(n.get("evidence", {}).get("boundary_conditions", [])),
            "related_claims": len(n.get("related_claims", [])),
            "created": str(n.get("created", "")),
            "updated": str(n.get("updated", "")),
        })
    return rows


def build_suggestions(notes: list[dict], inlinks: dict[str, int]) -> list[dict]:
    """Build suggestion rows from vault analysis."""
    rows = []
    today = datetime.now().date()
    priority = 0

    claims = [n for n in notes if n.get("type") == "claim" and n.get("status") == "active"]
    experiments = [n for n in notes if n.get("type") == "experiment"]
    sweeps = [n for n in notes if n.get("type") == "sweep-summary"]
    failures = [n for n in notes if n.get("type") == "failure-pattern"]

    # Needs replication
    for c in claims:
        sup = c.get("evidence", {}).get("supporting", [])
        if len(sup) < 2:
            priority += 1
            rows.append({
                "category": "needs_replication",
                "name": c["_name"],
                "detail": f"{c.get('confidence', '?')} confidence, {len(sup)} run(s)",
                "priority": priority,
            })

    # Stale claims
    for c in claims:
        updated = c.get("updated")
        if updated:
            try:
                ud = datetime.strptime(str(updated), "%Y-%m-%d").date() if isinstance(updated, str) else updated
                if (today - ud).days > STALE_DAYS:
                    priority += 1
                    rows.append({
                        "category": "stale_claim",
                        "name": c["_name"],
                        "detail": f"{(today - ud).days} days since update",
                        "priority": priority,
                    })
            except (ValueError, TypeError):
                pass

    # Critical failures
    for f in failures:
        if f.get("status") == "active" and f.get("severity") in ("critical", "high"):
            priority += 1
            rows.append({
                "category": "critical_failure",
                "name": f["_name"],
                "detail": f.get("severity", "unknown"),
                "priority": priority,
            })

    # Low confidence
    for c in claims:
        if c.get("confidence") == "low":
            priority += 1
            rows.append({
                "category": "low_confidence",
                "name": c["_name"],
                "detail": c.get("domain", "unknown"),
                "priority": priority,
            })

    # Unlinked experiments
    for e in experiments:
        if inlinks.get(e["_name"], 0) == 0:
            priority += 1
            rows.append({
                "category": "unlinked_experiment",
                "name": e["_name"],
                "detail": e.get("experiment_type", "unknown"),
                "priority": priority,
            })

    # Sweeps without claims
    for s in sweeps:
        if inlinks.get(s["_name"], 0) == 0:
            priority += 1
            rows.append({
                "category": "sweep_no_claims",
                "name": s["_name"],
                "detail": s.get("parameter", ""),
                "priority": priority,
            })

    return rows


def build_vault_notes(notes: list[dict], inlinks: dict[str, int]) -> list[dict]:
    """Build a full note inventory table."""
    rows = []
    for n in notes:
        ntype = n.get("type", "unknown")
        if ntype == "dashboard":
            continue
        rows.append({
            "name": n["_name"],
            "folder": n.get("_folder", ""),
            "type": ntype,
            "status": n.get("status", ""),
            "created": str(n.get("created", "")),
            "updated": str(n.get("updated", "")),
            "inlinks": inlinks.get(n["_name"], 0),
            "tags": ",".join(n.get("tags", [])) if n.get("tags") else "",
        })
    return rows


def sync_to_dolt(host: str, port: int, user: str, dry_run: bool, commit: bool):
    """Connect to Dolt and sync vault data."""
    notes = load_notes()
    print(f"Loaded {len(notes)} notes from vault", file=sys.stderr)

    inlinks = count_inlinks(notes)
    claims = build_claims(notes)
    suggestions = build_suggestions(notes, inlinks)
    inventory = build_vault_notes(notes, inlinks)

    print(f"  {len(claims)} claims", file=sys.stderr)
    print(f"  {len(suggestions)} suggestions", file=sys.stderr)
    print(f"  {len(inventory)} inventory notes", file=sys.stderr)

    if dry_run:
        print("\n-- DRY RUN: SQL that would be executed --\n")
        print("DELETE FROM vault_claims;")
        for c in claims:
            print(f"INSERT INTO vault_claims VALUES ('{c['name']}', '{c['confidence']}', "
                  f"'{c['domain']}', '{c['status']}', {c['supporting_runs']}, "
                  f"{c['weakening_runs']}, {c['boundary_conditions']}, "
                  f"{c['related_claims']}, '{c['created']}', '{c['updated']}');")
        print(f"\n-- {len(suggestions)} suggestion rows --")
        print(f"-- {len(inventory)} inventory rows --")
        return

    conn = pymysql.connect(host=host, port=port, user=user, database=DATABASE)
    cur = conn.cursor()

    # Ensure tables exist with current schema
    cur.execute("""
        CREATE TABLE IF NOT EXISTS vault_claims (
            name VARCHAR(255) PRIMARY KEY,
            confidence VARCHAR(32),
            domain VARCHAR(64),
            status VARCHAR(32),
            supporting_runs INT,
            weakening_runs INT DEFAULT 0,
            boundary_conditions INT DEFAULT 0,
            related_claims INT DEFAULT 0,
            created VARCHAR(32),
            updated VARCHAR(32)
        )
    """)

    cur.execute("""
        CREATE TABLE IF NOT EXISTS vault_suggestions (
            id INT AUTO_INCREMENT PRIMARY KEY,
            category VARCHAR(64),
            name VARCHAR(255),
            detail VARCHAR(512),
            priority INT
        )
    """)

    cur.execute("""
        CREATE TABLE IF NOT EXISTS vault_notes (
            name VARCHAR(255) PRIMARY KEY,
            folder VARCHAR(128),
            type VARCHAR(64),
            status VARCHAR(32),
            created VARCHAR(32),
            updated VARCHAR(32),
            inlinks INT DEFAULT 0,
            tags TEXT
        )
    """)

    # Upsert claims
    cur.execute("DELETE FROM vault_claims")
    for c in claims:
        cur.execute(
            "INSERT INTO vault_claims (name, confidence, domain, status, "
            "supporting_runs, weakening_runs, boundary_conditions, related_claims, "
            "created, updated) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)",
            (c["name"], c["confidence"], c["domain"], c["status"],
             c["supporting_runs"], c["weakening_runs"], c["boundary_conditions"],
             c["related_claims"], c["created"], c["updated"]),
        )

    # Replace suggestions
    cur.execute("DELETE FROM vault_suggestions")
    for s in suggestions:
        cur.execute(
            "INSERT INTO vault_suggestions (category, name, detail, priority) "
            "VALUES (%s,%s,%s,%s)",
            (s["category"], s["name"], s["detail"], s["priority"]),
        )

    # Replace inventory
    cur.execute("DELETE FROM vault_notes")
    for n in inventory:
        cur.execute(
            "INSERT INTO vault_notes (name, folder, type, status, created, updated, inlinks, tags) "
            "VALUES (%s,%s,%s,%s,%s,%s,%s,%s)",
            (n["name"], n["folder"], n["type"], n["status"],
             n["created"], n["updated"], n["inlinks"], n["tags"]),
        )

    conn.commit()
    print(f"\nSynced to Dolt ({host}:{port}/{DATABASE}):", file=sys.stderr)
    print(f"  vault_claims:      {len(claims)} rows", file=sys.stderr)
    print(f"  vault_suggestions: {len(suggestions)} rows", file=sys.stderr)
    print(f"  vault_notes:       {len(inventory)} rows", file=sys.stderr)

    if commit:
        ts = datetime.now().strftime("%Y-%m-%d %H:%M")
        msg = f"vault-to-dolt sync: {len(claims)} claims, {len(suggestions)} suggestions, {len(inventory)} notes ({ts})"
        try:
            cur.execute("CALL DOLT_ADD('vault_claims', 'vault_suggestions', 'vault_notes')")
            cur.execute("CALL DOLT_COMMIT('-m', %s)", (msg,))
        except Exception:
            # Older Dolt versions use SELECT instead of CALL
            try:
                cur.execute("SELECT DOLT_ADD('vault_claims', 'vault_suggestions', 'vault_notes')")
                cur.execute("SELECT DOLT_COMMIT('-m', %s)", (msg,))
            except Exception as e:
                print(f"  Warning: auto-commit failed ({e}). Use MCP to commit manually.", file=sys.stderr)
        conn.commit()
        print("  Dolt commit created.", file=sys.stderr)

    cur.close()
    conn.close()


def main():
    parser = argparse.ArgumentParser(description="Sync SWARM vault to Dolt")
    parser.add_argument("--host", default="127.0.0.1", help="Dolt SQL server host")
    parser.add_argument("--port", type=int, default=3307, help="Dolt SQL server port")
    parser.add_argument("--user", default="root", help="Dolt SQL user")
    parser.add_argument("--dry-run", action="store_true", help="Print SQL without executing")
    parser.add_argument("--commit", action="store_true", help="Auto-commit to Dolt after sync")
    args = parser.parse_args()

    sync_to_dolt(args.host, args.port, args.user, args.dry_run, args.commit)


if __name__ == "__main__":
    main()
