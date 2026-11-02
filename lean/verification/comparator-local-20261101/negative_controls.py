"""Require Comparator to reject a changed statement and an admitted proof."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
WORK = Path(__file__).resolve().parent
REPORT = ROOT / 'lean/verification/comparator-local-20261101'
sys.path.insert(0, str(ROOT / 'scripts'))
from check_pinned_module import pinned_environment
compiler, env, _ = pinned_environment(ROOT)
env['LEAN_PATH'] = str(WORK) + os.pathsep + env['LEAN_PATH']
target = 'NtimeDspace.ModularCounting.countModP_correct'
wrong = WORK / 'WrongStatement.lean'
wrong.write_text(f'theorem {target} : True := True.intro\n')
subprocess.run([str(compiler), '-o', str(wrong.with_suffix('.olean')), str(wrong)],
               cwd=WORK, env=env, check=True)
wrong_export = WORK / 'wrong-statement.ndjson'
with wrong_export.open('wb') as out:
    subprocess.run([str(compiler.parent / 'leanexport'), 'WrongStatement', '--', target],
                   cwd=WORK, env=env, stdout=out, check=True)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

controls = {}
cases = [
    ('wrong-statement', WORK / 'counting-challenge.ndjson', wrong_export,
     f"Challenge and solution theorem statement do not match: '{target}'"),
    ('admitted-proof', WORK / 'counting-challenge.ndjson', WORK / 'counting-challenge.ndjson',
     "sorryAx"),
]
for name, challenge, solution, expected in cases:
    args = [str(compiler.parent / 'lake'), 'comparator', '--paranoid',
            '--inadvisably-no-sandbox', '--config=' + str(REPORT / 'counting.json'),
            '--challenge-from-export=' + str(challenge), '--solution-from-export=' + str(solution)]
    proc = subprocess.run(args, cwd=WORK, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True)
    log = REPORT / (name + '.log')
    log.write_text(proc.stdout)
    accepted = proc.returncode == 1 and expected in proc.stdout
    controls[name] = {'passed': accepted, 'exit_code': proc.returncode,
        'expected_diagnostic': expected, 'command': args, 'log_sha256': digest(log),
        'challenge_export_sha256': digest(challenge), 'solution_export_sha256': digest(solution)}
    print(name, 'PASS' if accepted else 'FAIL', proc.stdout, flush=True)
(REPORT / 'negative-controls.json').write_text(json.dumps(controls, indent=2) + '\n')
if not all(x['passed'] for x in controls.values()):
    raise SystemExit(1)
