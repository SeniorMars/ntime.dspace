# Lean formalization

The current endpoint is [Final.lean](NtimeDspace/Final.lean). It proves, for the
binary encoding `encBits` and the imported multitape complexity-class definitions:

```lean
NtimeDspace.ntime_subset_dspace :
  Cslib.Complexity.NTIME encBits (fun n => n) ⊆
    Cslib.Complexity.DSPACE encBits NtimeDspace.Budget.S

NtimeDspace.ntime_ssubset_dspace :
  Cslib.Complexity.NTIME encBits (fun n => n) ⊂
    Cslib.Complexity.DSPACE encBits (fun n => n)
```

`Budget.S` is one fixed sublinear function. The construction reduces a machine's
computations to local counting networks, evaluates their counts modulo primes,
compiles the scalar program with a workspace bound, and applies the deterministic
space hierarchy. The finite exceptional input lengths are handled by a fixed
lookup table. The root `NtimeDspace` import now includes this endpoint.

This is not a formalization of every statement in [the paper](../paper.tex).
The final exported theorems do not state the general-time simulation with the
analytic rate `κ(T)`, its simultaneous time bound, the almost-everywhere time lower
bound, or the probabilistic and parity extensions. The proposed
`O(T/√log T)` tensor implementation in the research notes is not a theorem here.

The [November 2 paper rewrite](../notes/paper-rewrite-20261102/README.md) makes
weighted interval tables and a bounded-index evaluator the main presentation.
Appendix C of [paper.pdf](../paper.pdf) maps its statements to Lean declarations
and records the remaining differences, including the machine conventions,
natural versus signed weights, and support encodings. That rewrite changes no
Lean source or theorem and reuses the existing validation records.

## Current implementation improvement

The [November 2 milestone](../notes/improvements-20261102/README.md) replaces the
weighted counter's coefficient-tuple enumeration with factorwise truncated
Hermite weights. The integration is checked through the final theorem; consult
that record for exact source hashes, replay status, and remaining work.

[FlatHermite.lean](NtimeDspace/FlatHermite.lean) proves agreement below the Taylor
order and scalar recovery under the stronger degree condition that prevents
aliasing. [FlatHorner.lean](NtimeDspace/FlatHorner.lean) evaluates each reciprocal
factor with a descending scalar accumulator. The old and new weights generally
differ at field points; their projected recovery sums agree under the stated
hypotheses. The manuscript gives `O(QJ)` field operations, counting inversion as
one field operation. The compiled natural-number arithmetic implements those
operations explicitly; this is not an `O(QJ)` machine-step theorem.

The leading support and measurement storage budgets are unchanged.
`SupportOrdinalMeaning.lean`, which failed the earlier whole-tree audit, has also
been repaired without changing its statements or definitions.

## Finding the proof

| Component | Entry points |
| --- | --- |
| Machine computations and local counting networks | `SemanticReduction`, `LocalIntervalCount`, `NetFacts` |
| Taylor cancellation and grouped counting | `DeformationTaylor`, `WGroupedCounter`, `WConcreteCountingLoop` |
| Flat recovery algebra and scalar evaluator | `FlatHermite`, `FlatHorner`, `WeightTerm`, `RecoverTerm` |
| Counter correctness | `CounterAssemblyEq`, `NetworkCounter`, `DeciderCorrect` |
| Program and machine workspace | `TameCounter`, `FinalBounds`, `ProgLength`, `ComplexityReuse` |
| Uniform sublinear bound and separation | `BudgetAsymptotics`, `UniformSpace`, `Final` |

The separate unweighted formula counter and earlier coefficient/weight machine
modules remain available. They use their own globally truncated weight routines;
they are not evidence that the new flat evaluator has a separate exported machine
time theorem.

## Validation and reproduction

For interactive diagnostics and goal inspection, the local Lean MCP server is
configured against the same pinned compiler and checked artifact cache. See
[the setup instructions](../scripts/LEAN_MCP.md). It does not run builds or
Comparator automatically.

The pinned toolchain is Lean `v4.36.0-rc2`. The immutable dependency revisions are
recorded in [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json).
The local checker uses the workspace's pinned compiler and dependency artifacts,
with isolated project outputs. From the repository root:

```sh
python3 scripts/check_flat_recovery.py
python3 notes/improvements-20261102/validate.py
```

The [earlier audit](../notes/audit-20261102/README.md) checked the then-current final
closure, audited axioms, compared two final statements, and replayed the exported
proofs through Comparator's six bundled kernels. Its source hashes identify that
snapshot. It excluded the failing auxiliary module and does not certify later
edits. The new milestone keeps its evidence separate: all 301 project modules and the
root import passed its pinned check (191 rebuilt and 111 identity-checked
reuses). The new axiom sweep permits only the three standard axioms. See the
milestone for the fresh Comparator pass: both final statement comparisons and all
six bundled replay kernels succeeded. Comparator's local export
mode was explicitly authorized because its Linux sandbox is unavailable here;
that mode does not provide sandbox security guarantees.

Comparator is user-requested only. Ordinary edits and validation do not authorize
another Comparator run; the user decides when it is needed.

The historical [148-module check](verification/pinned/check.json) and its
[51 executable examples](verification/pinned/counting-examples.json) cover an
earlier revision. They must not be described as a current whole-project build.
The finite-field regression script above checks the new scalar loop, including
the degree-bound counterexample; it does not test the complete asymptotic machine
on large inputs.

The shared `AGENTS.md` describes Complexitylib's integration gates. This
standalone package has no `mk_all`, `lint-style`, or `checkInitImports` executable;
the explicit all-module checker is recorded as such, rather than reported as
those six gates. The all-module check retains existing deprecation and unused-variable
warnings; it is not a warning-free integration build. Existing dependency artifacts and imported foundational
libraries remain part of the trusted build environment.

External comparison sources are documented in [the ETH source inventory](../references/eth/README.md)
and [the Zhuang source inventory](../references/zhuang/README.md).
They are research references, not imports of the final theorem.
