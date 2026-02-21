#!/usr/bin/env bash
# session-capture.sh — Run at session end to save state
# Fires on Stop hook event

if [ ! -f "vault/.arscontexta" ] && [ ! -f ".arscontexta" ]; then
  exit 0
fi

TIMESTAMP=$(date +%Y%m%d-%H%M%S)
SESSION_FILE="vault/ops/sessions/session-${TIMESTAMP}.json"

# Create session record
python3 -c "
import json, os, datetime

session = {
  'session_id': '${TIMESTAMP}',
  'end_time': datetime.datetime.utcnow().isoformat() + 'Z',
  'notes_created': [],
  'notes_modified': []
}

# Check for recent git changes
import subprocess
try:
  result = subprocess.run(['git', 'diff', '--name-only', 'HEAD~1', 'HEAD'],
    capture_output=True, text=True, cwd='.')
  changed = result.stdout.strip().split('\n')
  session['notes_modified'] = [f for f in changed if f.startswith('vault/') and f.endswith('.md')]
except:
  pass

os.makedirs('vault/ops/sessions', exist_ok=True)
with open('${SESSION_FILE}', 'w') as f:
  json.dump(session, f, indent=2)
print(f'Session captured: ${SESSION_FILE}')
" 2>/dev/null || true
