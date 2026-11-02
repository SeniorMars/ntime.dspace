"""Authorized local export-based Comparator run; no project proofs are edited."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / 'lean/verification/comparator-local-20261101'
WORK = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
from check_pinned_module import pinned_environment

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

compiler, env, _ = pinned_environment(ROOT)
BIN = compiler.parent
env['LEAN_PATH'] = str(WORK) + os.pathsep + env['LEAN_PATH']
AXIOMS = ['propext', 'Quot.sound', 'Classical.choice']
PRIMITIVES = ['Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div',
    'Nat.mod', 'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor',
    'Nat.shiftLeft', 'Nat.shiftRight', 'String.ofList', 'Char.ofNat', 'List',
    'eagerReduce', 'Nat', 'String', 'String.mk', 'Char', 'optParam', 'autoParam',
    'semiOutParam', 'outParam', 'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind']

SUITES = {
    'counting': ('ModularCounting', 'countModP_correct', '''import NtimeDspace.UniformCountingLoop

namespace NtimeDspace.ModularCounting
variable {n : ℕ}

def fallback (p : ℕ) (formula : Formula n) : ZMod p :=
  AssignmentLoop.sumAssignments n (fun assignment =>
    if formula.eval assignment then (1 : ZMod p) else 0) 0

def countModP (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) : ZMod p :=
  if eligible : ParameterChoice.cost 6 ≤ n.log2 ∧ 4 * n ^ 2 < p then
    UniformCountingLoop.countModP p formula bounded eligible.1
  else fallback p formula

theorem countModP_correct (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) :
    countModP p formula bounded = (satisfyingCount formula : ZMod p) := by
  sorry
end NtimeDspace.ModularCounting
'''),
    'coefficient': ('HermiteCoefficientCorrectness', 'weightCoefficient_simultaneous_bounds', '''import NtimeDspace.HermiteCoefficientMachine
import NtimeDspace.SelectedCounter

namespace NtimeDspace.HermiteCoefficientCorrectness
open Turing Turing.MultiTapeTM HermiteRecovery

noncomputable def weightPolynomial (input : HermiteCoefficientMachine.Input) :
    Polynomial (ZMod input.val.1) := by
  let : Fact input.val.1.Prime := ⟨input.property.1⟩
  exact nodeWeight
    (Finset.univ.image (SelectedCounter.nodeValue (p := input.val.1) (nodes := input.val.2.1)))
    (SelectedCounter.nodeValue (p := input.val.1)
      (⟨input.val.2.2.1, input.property.2⟩ : Fin input.val.2.1)) input.val.2.2.2.1

def WeightValid (input : HermiteCoefficientMachine.BoundedInput) : Prop :=
  input.val.val.2.1 < input.val.val.1 ∧ 0 < input.val.val.2.2.2.1 ∧
    input.val.val.2.2.2.2 < input.val.val.2.2.2.1

abbrev WeightInput := {input : HermiteCoefficientMachine.BoundedInput // WeightValid input}

def encWeightInput : WeightInput ↪ List Bool :=
  (⟨Subtype.val, Subtype.val_injective⟩ : WeightInput ↪ HermiteCoefficientMachine.BoundedInput).trans
    HermiteCoefficientMachine.encBoundedInput

noncomputable def weightCoefficient (input : WeightInput) : ℕ :=
  ((weightPolynomial input.val.val).coeff input.val.val.val.2.2.2.2).val

theorem weightCoefficient_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace weightCoefficient encWeightInput encNat
      (fun input => 2 ^ (C * HermiteCoefficientMachine.bitBudget input.val))
      (fun input => C * HermiteCoefficientMachine.bitBudget input.val) := by
  sorry
end NtimeDspace.HermiteCoefficientCorrectness
'''),
    'weight': ('HermiteWeightMachine', 'polynomialWeight_simultaneous_bounds', '''import NtimeDspace.HermiteWeightSpace

namespace NtimeDspace.HermiteWeightMachine
open Turing Turing.MultiTapeTM HermiteWeightLoop HermiteWeightBudget

abbrev PositiveHeader := {header : Header // 0 < order header}

def encPositiveHeader : PositiveHeader ↪ List Bool :=
  (⟨Subtype.val, Subtype.val_injective⟩ : PositiveHeader ↪ Header).trans encHeader

theorem polynomialWeight_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace (fun header : PositiveHeader => polynomialWeight header.val)
      encPositiveHeader encNat (fun header => 2 ^ (C * bitBudget header.val))
      (fun header => C * bitBudget header.val) := by
  sorry
end NtimeDspace.HermiteWeightMachine
'''),
}

prior_path = ROOT / 'lean/verification/pinned/check.json'
prior = json.loads(prior_path.read_text())
inputs = {}
for name, entry in prior['modules'].items():
    for path, key in [(ROOT / f'lean/NtimeDspace/{name}.lean', 'source_sha256'),
                      (ROOT / f'lean/.lake/pinned-check/NtimeDspace/{name}.olean', 'olean_sha256')]:
        actual = digest(path)
        if actual != entry[key]:
            raise SystemExit(f'Existing check no longer matches: {path}')
        inputs[str(path.relative_to(ROOT))] = actual

record = {
    'started_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'mode': 'user-authorized local exports; Comparator sandbox disabled on macOS',
    'standard_sandbox_attempt': {'exit_code': 2, 'diagnostic': 'bwrap needs Linux namespaces'},
    'scope': 'Three completed endpoints, frozen source-based contracts; not an independent formalization of the paper',
    'permitted_axioms': AXIOMS,
    'compiler_githash': subprocess.check_output([str(compiler), '--githash'], env=env, text=True).strip(),
    'previous_validation_record_sha256': digest(prior_path),
    'inputs': inputs,
    'suites': {},
    'stages': [],
    'success': False,
}

def save():
    (REPORT / 'check.json').write_text(json.dumps(record, indent=2) + '\n')

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
    entry = {'label': label, 'command': [str(x) for x in args], 'cwd': str(WORK),
             'exit_code': proc.returncode, 'elapsed_seconds': round(time.monotonic()-start, 2),
             'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log)}
    if export:
        entry.update(export=str(export.relative_to(ROOT)), export_sha256=digest(export),
                     export_bytes=export.stat().st_size)
    record['stages'].append(entry)
    save()
    print(f'{label}: exit {proc.returncode}, {entry["elapsed_seconds"]}s', flush=True)
    if proc.returncode != 0:
        print(log.read_text()[-6000:], flush=True)
    return proc.returncode

for key, (module, theorem, content) in SUITES.items():
    challenge_module = 'Challenge' + module
    source = REPORT / (challenge_module + '.lean')
    source.write_text('-- Frozen source-based contract. The sorry is an intentional challenge hole.\n' + content)
    target = f'NtimeDspace.{module}.{theorem}'
    config = {'challenge_module': challenge_module, 'solution_module': f'NtimeDspace.{module}',
              'theorem_names': [target], 'permitted_axioms': AXIOMS}
    config_path = REPORT / (key + '.json')
    config_path.write_text(json.dumps(config, indent=2) + '\n')
    record['suites'][key] = {'target': target, 'challenge_source_sha256': digest(source),
                           'config_sha256': digest(config_path)}
    local_source = WORK / source.name
    local_source.write_text(source.read_text())
    if run(key + '-challenge-build', [str(compiler), '-o', str(WORK / (challenge_module + '.olean')), str(local_source)]):
        continue
    challenge_export, solution_export = WORK / (key + '-challenge.ndjson'), WORK / (key + '-solution.ndjson')
    names = [target, *AXIOMS, *PRIMITIVES]
    if run(key + '-challenge-export', [str(BIN / 'leanexport'), challenge_module, '--', *names], challenge_export):
        continue
    if run(key + '-solution-export', [str(BIN / 'leanexport'), f'NtimeDspace.{module}', '--', *names], solution_export):
        continue
    rc = run(key + '-comparator', [str(BIN / 'lake'), 'comparator', '--paranoid',
        '--inadvisably-no-sandbox', '--config=' + str(config_path),
        '--challenge-from-export=' + str(challenge_export),
        '--solution-from-export=' + str(solution_export)])
    record['suites'][key]['exit_code'] = rc
    save()

record['changed_after_check'] = [name for name, hash_ in inputs.items() if digest(ROOT / name) != hash_]
record['success'] = all(suite.get('exit_code') == 0 for suite in record['suites'].values()) and not record['changed_after_check']
record['finished_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
save()
print('SUCCESS' if record['success'] else 'NOT ALL CHECKS PASSED', flush=True)
