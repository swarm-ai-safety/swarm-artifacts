#!/usr/bin/env bash
# session-orient.sh — Run at session start to orient the agent
# Fires on SessionStart hook event

# Only run if this is a SWARM vault session
if [ ! -f "vault/.arscontexta" ] && [ ! -f ".arscontexta" ]; then
  exit 0
fi

echo ""
echo "=== SWARM Research OS — Session Orientation ==="

# Load vault identity
echo ""
echo "Reading self..."
if [ -f "vault/self/goals.md" ]; then
  echo "Active threads loaded from vault/self/goals.md"
fi

# Check reminders
if [ -f "vault/ops/reminders.md" ]; then
  due=$(grep -E '^\- \[ \]' vault/ops/reminders.md | head -3 2>/dev/null)
  if [ -n "$due" ]; then
    echo ""
    echo "Reminders:"
    echo "$due"
  fi
fi

# Maintenance triggers
obs_count=$(ls vault/ops/observations/*.md 2>/dev/null | wc -l | tr -d ' ')
tension_count=$(ls vault/ops/tensions/*.md 2>/dev/null | wc -l | tr -d ' ')

if [ "$obs_count" -ge 10 ]; then
  echo ""
  echo "⚑ Observation threshold reached: $obs_count pending. Run /rethink to review."
fi

if [ "$tension_count" -ge 5 ]; then
  echo ""
  echo "⚑ Tension threshold reached: $tension_count pending. Run /rethink to resolve."
fi

# Queue state
if [ -f "vault/ops/queue/queue.json" ]; then
  pending=$(python3 -c "
import json, sys
try:
  q = json.load(open('vault/ops/queue/queue.json'))
  tasks = [t for t in q.get('tasks', []) if t.get('status') == 'pending']
  print(len(tasks))
except:
  print(0)
" 2>/dev/null)
  if [ "$pending" -gt 0 ]; then
    echo ""
    echo "Pipeline queue: $pending tasks pending. Run /next for recommendations."
  fi
fi

# File tree
echo ""
echo "Vault structure:"
ls vault/claims/ 2>/dev/null | wc -l | xargs -I{} echo "  Claims: {} files"
ls vault/experiments/ 2>/dev/null | wc -l | xargs -I{} echo "  Experiments: {} files"
ls vault/failures/ 2>/dev/null | wc -l | xargs -I{} echo "  Failures: {} files"
ls -d runs/*/ 2>/dev/null | wc -l | xargs -I{} echo "  Runs: {} folders"

echo ""
echo "Session start complete. Orient → Work → Persist."
echo "================================================"
