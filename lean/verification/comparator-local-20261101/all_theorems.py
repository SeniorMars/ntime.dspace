"""Replay all 1603 audited project theorem roots using Comparator's lake check backend."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
WORK = Path(__file__).resolve().parent
REPORT = ROOT / 'lean/verification/comparator-local-20261101'
sys.path.insert(0, str(ROOT / 'scripts'))
from check_pinned_module import pinned_environment

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

compiler, env, _ = pinned_environment(ROOT)
prior = json.loads((ROOT / 'lean/verification/pinned/check.json').read_text())
inputs = {}
for name, entry in prior['modules'].items():
    for path, key in [(ROOT / f'lean/NtimeDspace/{name}.lean', 'source_sha256'),
                      (ROOT / f'lean/.lake/pinned-check/NtimeDspace/{name}.olean', 'olean_sha256')]:
        actual = digest(path)
        if actual != entry[key]:
            raise SystemExit(f'Existing check no longer matches: {path}')
        inputs[str(path.relative_to(ROOT))] = actual
for path, key in [(ROOT / 'lean/NtimeDspace.lean', 'source_sha256'),
                  (ROOT / 'lean/.lake/pinned-check/NtimeDspace.olean', 'olean_sha256')]:
    actual = digest(path)
    if actual != prior['root_aggregate'][key]:
        raise SystemExit(f'Aggregate changed: {path}')
    inputs[str(path.relative_to(ROOT))] = actual

audit = ROOT / 'lean/.lake/pinned-check/PinnedAudit.lean'
targets = re.findall(r'^#print axioms (\S+)$', audit.read_text(), re.MULTILINE)
assert len(targets) == prior['theorems_inspected'] == 1603
assert len(set(targets)) == len(targets)
source_targets = []
for name in prior['modules']:
    text = (ROOT / f'lean/NtimeDspace/{name}.lean').read_text()
    namespaces = re.findall(r'^namespace\s+(\S+)', text, re.MULTILINE)
    assert len(namespaces) == 1, name
    declarations = re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+([^\s({:]+)',
                              text, re.MULTILINE)
    source_targets.extend(f'{namespaces[0]}.{declaration}' for declaration in declarations)
assert targets == source_targets, 'Audit targets do not match hash-checked source declarations'
target_file = REPORT / 'all-theorem-targets.json'
target_file.write_text(json.dumps(targets, indent=2) + '\n')
record = {'started_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'mode': 'user-authorized local export-based lake check --paranoid; no tool sandbox',
    'scope': 'All 1603 top-level theorem roots in the prior axiom audit, plus transitive proof dependencies; no statement comparison',
    'inputs': inputs, 'theorem_count': len(targets), 'stages': [], 'success': False,
    'audit_sha256': digest(audit), 'target_list_sha256': digest(target_file)}

def save():
    (REPORT / 'all-theorems.json').write_text(json.dumps(record, indent=2) + '\n')

def run(label, args, export=None):
    print(label, flush=True)
    log = REPORT / (label + '.log')
    start = time.monotonic()
    with log.open('w') as err:
        if export:
            with export.open('wb') as out:
                proc = subprocess.run(args, cwd=WORK, env=env, stdout=out, stderr=err)
        else:
            proc = subprocess.run(args, cwd=WORK, env=env, stdout=err, stderr=subprocess.STDOUT)
    entry = {'label': label, 'command': args, 'exit_code': proc.returncode,
             'elapsed_seconds': round(time.monotonic()-start,2), 'log': str(log.relative_to(ROOT)),
             'log_sha256': digest(log)}
    if export:
        entry.update(export=str(export.relative_to(ROOT)), export_sha256=digest(export),
                     export_bytes=export.stat().st_size)
    record['stages'].append(entry)
    save()
    print(f'{label}: exit {proc.returncode}, {entry["elapsed_seconds"]}s', flush=True)
    if proc.returncode:
        print(log.read_text()[-6000:], flush=True)
    return proc.returncode

export = WORK / 'all-theorems.ndjson'
rc = run('all-theorems-export', [str(compiler.parent / 'leanexport'), 'NtimeDspace', '--', *targets], export)
if rc == 0:
    rc = run('all-theorems-check', [str(compiler.parent / 'lake'), 'check', '--paranoid',
        '--inadvisably-no-sandbox', '--from-export=' + str(export)])
record['changed_after_check'] = [name for name, value in inputs.items() if digest(ROOT / name) != value]
record['success'] = rc == 0 and not record['changed_after_check']
record['finished_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
save()
print('SUCCESS' if record['success'] else 'CHECK DID NOT PASS', flush=True)
