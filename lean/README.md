# Lean formalization

This development proves Theorem 1.1, Corollary 1.2, Theorem 7.1, Corollary 7.2, Propositions 8.1
and 8.2 and Remark 8.3 of [the paper](../separating-ntime-from-space.tex) for every `t(n) ≥ n`. Machines and
complexity classes are [Complexitylib](https://github.com/cslib-community/complexitylib)'s, on
Mathlib and CSLib. The proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The proof is the paper's: networks (§2), the formula and its evaluation (§3), label codes and the
first clique (§4), pieces from walks on the cube (§5), and the merge, the formula's index lengths
and the explicit machine (§6). The machine of Lemma 6.4 is a program whose intermediate values
are below `2^{O(F)}`, which gives space `O(F)` and time `2^{O(F)}`.

## Main statements

Machines are Complexitylib's multitape Turing machines over the binary encoding `encBits`.
`t/√log t` is written `t / ⌊√⌊log₂ t⌋⌋ + 1`. Theorem 1.1, where `t` need not be constructible:

```lean
theorem NtimeDspace.Crossing.ntime_decidable_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n)
    {A : Set (List Bool)} (hA : A ∈ Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits t) :
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace A Turing.MultiTapeTM.encBits
      (fun a => 2 ^ (C * (t a.length / Nat.sqrt (t a.length).log2 + 1)))
      (fun a => C * (t a.length / Nat.sqrt (t a.length).log2 + 1))
```

Corollary 1.2 (i) at `t(n) = n`:

```lean
theorem NtimeDspace.Crossing.ntime_ssubset_dspace :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => n) ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n)
```

[NtimeChallengeGeneral.lean](NtimeChallengeGeneral.lean) and
[NtimeChallengeCross.lean](NtimeChallengeCross.lean) restate the endpoints with only Complexitylib
imports. Comparator checks the proofs against them.

## Paper to Lean

[NtimeDspace.lean](NtimeDspace.lean) indexes the main results. The one-bit example and its
matrix ranks over `ℚ` are in [Cube/Examples.lean](NtimeDspace/Cube/Examples.lean#L355).

| Paper | Lean |
| --- | --- |
| Theorem 1.1 | `Crossing.ntime_decidable_sqrtLog_general`, `Crossing.ntime_subset_dspace_sqrtLog_general` |
| Corollary 1.2 | `Crossing.ntime_ssubset_dspace_general`, `Crossing.ntime_ssubset_nspace_general`, `Crossing.ntime_mul_sqrtLog_subset_dspace_general`, `Crossing.exists_dspace_linear_ntime_lower_bound_general`, `Crossing.pptime_ssubset_dspace_general` |
| Definition 2.1 | `Cross.LogspaceNetFamily` |
| Theorem 2.3 | `Cross.cubeCounting`, `Cross.cubeBlockBits` |
| Theorem 2.4 | `Cross.Exact.clockedBits_of_blockBits`, `Cross.generalSimulation_of_clocked` |
| Proposition 3.2 | `SumProduct.GenProg.main_spec` |
| Lemmas 4.1, 4.3 | `Cube.decode_labelCode`, `Cube.firstClique_value`, `Cube.firstClique_potential` |
| Lemmas 5.1–5.3 | `Cube.walk_coeff`, `Cube.piece_eval_one`, `Cube.piece_transpose` |
| Lemma 5.4 | `Cube.rowCut_finsum` (every coefficient, summed over all messages), `Cube.nUp_lower`, `Cube.nDown_lower` |
| Corollary 5.5 | `Cube.rowCut`, `Cube.colCut` |
| Lemma 5.6 | `Cube.transportL_pivot` |
| Lemmas 6.1, 6.2 | `Cube.energy_le`, `Cube.merge` |
| Lemmas 6.3, 6.4 | `Cube.formula_cost`, `Cube.cubeProg`, `Cube.Num.cube_bit` |
| Theorem 7.1 | `Crossing.pptime_subset_dspace_sqrtLog_general`, `Crossing.bptime_subset_dspace_sqrtLog_general`, `Crossing.parityTIME_subset_dspace_sqrtLog_general`, `Crossing.modTIME_subset_dspace_sqrtLog_general`, `Crossing.ceqTIME_subset_dspace_sqrtLog_general` |
| Corollary 7.2 | `Cross.ThreeSat.cor_9_4_unconditional`, `Cross.ThreeSat.cor_9_4_bits_unconditional` |
| Propositions 8.1, 8.2 | `Cube.prop_boolean`, `Cube.prop_barrier` |
| Remark 8.3 | `Cross.Relativization.separation_does_not_relativize_bsa` |
| §8, counting and 3-SAT | `Cross.ThreeSat.smallBits_of_scale`, `smallBits_nlog`, `smallBits_rpow` |
| §8, counting and PPTIME | `Cross.ntime_subset_dspace_of_blockBitsAt`, `Cross.pptime_subset_dspace_of_blockBitsAt`, `Crossing.pptime_subset_dspace_divLog_of_blockBitsAt` |
| §8, after Propositions 8.1, 8.2 | `Cube.prop_boolean_sq`, `Cube.prop_barrier_sq`, `Cube.equalWidth_sum` |
| §5, full one-bit routing formula | [Cube.oneBit_piece](NtimeDspace/Cube/Examples.lean#L365) |
| §5, one-bit coefficients and support | [Cube.oneBit_coeff_zero](NtimeDspace/Cube/Examples.lean#L377), [Cube.oneBit_coeff_two](NtimeDspace/Cube/Examples.lean#L386), [Cube.oneBit_coeff_neg_two](NtimeDspace/Cube/Examples.lean#L394), [Cube.oneBit_coeff_eq_zero](NtimeDspace/Cube/Examples.lean#L402) |
| §5, transpose of encoded one-bit views | [Cube.oneBitViews_transpose](NtimeDspace/Cube/Examples.lean#L412), [Cube.oneBitViews_true_transpose](NtimeDspace/Cube/Examples.lean#L430) |
| §5, `Π₂` row/column ranks `(4, 1)` | [Cube.oneBitRow_two_rank](NtimeDspace/Cube/Examples.lean#L502), [Cube.oneBitCol_two_rank](NtimeDspace/Cube/Examples.lean#L510) |
| §5, `Π₀` row/column ranks `(3, 3)` | [Cube.oneBitRow_zero_rank](NtimeDspace/Cube/Examples.lean#L546), [Cube.oneBitCol_zero_rank](NtimeDspace/Cube/Examples.lean#L555) |
| §5, `Π₋₂` row/column ranks `(1, 4)` | [Cube.oneBitRow_neg_two_rank](NtimeDspace/Cube/Examples.lean#L521), [Cube.oneBitCol_neg_two_rank](NtimeDspace/Cube/Examples.lean#L532) |
| §5, one-bit crossing ranks `(4, 4)` | [Cube.oneBitCrossingRow_rank](NtimeDspace/Cube/Examples.lean#L583), [Cube.oneBitCrossingCol_rank](NtimeDspace/Cube/Examples.lean#L593) |
| §5, specialized examples and split contributions | `Cube.ex_piece`, `Cube.ex_rowSplit`, `Cube.ex_colSplit`, `Cube.ex_mixed` |
| §5.1, the Walsh–Hadamard remark | `Cube.C_eq_prod`, `Cube.cMat_mul_self`, `Cube.hadamard_mul_self`, `Cube.hadamard_diagonalizes` |

Two statements differ in form from the paper:

- Corollary 7.2: one machine decides, given a formula and `j ≤ 3m`, bit `j` of the number of
  satisfying assignments. The count is below `2^{3m}`, so this computes it.
- Remark 8.3: `NTIME^A[n] ⊆ SPACE^A[n]` is proved for oracles decidable in linear space, not for
  every oracle. The remark's oracle is decidable in linear space.

The claims of §8 are implications, and so are their Lean forms. If every network with logspace
access is counted in space `D(s)`, then 3-SAT is counted in time `2^{O(D(m))}`; at `D = s/log s`
this is `2^{O(m/log m)}`, and at `D = s^{1-ε}` it is `2^{O(m^{1-ε})}`. If Theorem 2.3 holds for the
block networks at a scale `D`, then `NTIME[t]`, `PPTIME[t]` and `BPTIME[t]` are in `DSPACE[D(t)]`;
the sum over schedules makes this route need `D = Ω(t/log t)`. The squared bounds after
Propositions 8.1 and 8.2 are stated exactly, for every `N`, with `max(·, 0)`; under the paper's
assumption `log N = o(λ)` this is its asymptotic form.


## Layout

- `NtimeDspace/Cube/`: §§4–6 and the explicit machine of Lemma 6.4.
- `NtimeDspace/Cross/`: networks and logspace access, Theorem 2.4, the endpoints, the counting
  classes, Corollary 7.2 (`ThreeSat/`) and Remark 8.3.
- `NtimeDspace/SumProduct/`: the evaluator of Proposition 3.2.
- `NtimeDspace/Oracle/`: oracle machines for Remark 8.3.
- `NtimeDspace/*.lean`: the program language (`ProgLang`, `ProgTerm`), its space calculus
  (`Tame*`) and the machine infrastructure used by the network terms.
- `NtimeDspace/Checks/CubeAxioms.lean`: the axiom audit. Each check is a `#guard_msgs`, so the
  build fails if a listed declaration depends on any axiom beyond the three standard ones.
- `Vendor/Ant26Ring/ThreeSatStatement.lean`: Anthropic's definition of 3-SAT and its tape
  encoding, used by Corollary 7.2 ([README](Vendor/Ant26Ring/README.md)).

## Building

Lean `v4.36.0-rc2`. Dependencies are pinned in [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json).

```sh
cd lean
lake exe cache get
lake build
```

The default target includes the axiom audit.

## Comparator

[Comparator](https://github.com/leanprover/comparator) checks that the proved endpoints have the
challenge statements and use only the standard axioms. The configs are
`comparator-{cross,general}.json`. Each has two negative controls that must fail: `-wrong`
changes a statement and `-sorry` replaces a proof by `sorry`. The runs need more memory than a
laptop and were done on a computing cluster.

A run on 9 November 2026 passed: both main checks succeeded, with Lean's
paranoid kernel, and all four controls failed as they should (the changed statements as mismatches,
the `sorry` proofs for `sorryAx`). Later commits changed only comments and
`Cube/Examples.lean`, which the checked statements do not import.
