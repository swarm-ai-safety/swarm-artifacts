#!/usr/bin/env bash
#
# SWARM Research OS — Post-commit hook
#
# Syncs vault frontmatter to Dolt after every commit that touches vault/.
# Runs in background so it doesn't block the commit flow.
#
# Install:
#   cp scripts/post-commit-hook.sh .git/hooks/post-commit && chmod +x .git/hooks/post-commit
#   # or:
#   ln -sf ../../scripts/post-commit-hook.sh .git/hooks/post-commit

ROOT="$(git rev-parse --show-toplevel)"

# Only sync if vault/ files were in this commit
VAULT_CHANGED=$(git diff-tree --no-commit-id --name-only -r HEAD -- 'vault/' 2>/dev/null | head -1)
if [ -z "$VAULT_CHANGED" ]; then
    exit 0
fi

# Run sync in background so commit returns immediately
(
    echo "[post-commit] Syncing vault to Dolt..."
    python "$ROOT/scripts/vault-to-dolt.py" --commit 2>&1 | while read -r line; do
        echo "[post-commit] $line"
    done
) &

exit 0
