/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.Cross.Theorem
import NtimeDspace.Cross.GeneralFinal
import NtimeDspace.Cross.CountingFinal
import NtimeDspace.Cross.ThreeSatFinal
import NtimeDspace.Cross.ThreeSat.Unconditional
import NtimeDspace.Cross.ThreeSat.Check
import NtimeDspace.Cross.PPLowerBound
import NtimeDspace.Cross.PrimeBoundExact
import NtimeDspace.Cross.Relativization
import NtimeDspace.Oracle.Machine
import NtimeDspace.Oracle.Classes
import NtimeDspace.Oracle.BSA
import NtimeDspace.Oracle.OneQuery
import NtimeDspace.Oracle.SimStep
import NtimeDspace.Oracle.SimComp
import NtimeDspace.Oracle.SimSize
import NtimeDspace.Oracle.Simulation
import NtimeDspace.Oracle.BSADecide
import NtimeDspace.Oracle.BSAComp
import NtimeDspace.Oracle.Choice
import NtimeDspace.Oracle.NSimStep
import NtimeDspace.Oracle.NSimComp
import NtimeDspace.Cross.PPSeparation
import NtimeDspace.Cross.ColumnAdder
import NtimeDspace.Cube.ArgWidth
import NtimeDspace.Cube.Basic
import NtimeDspace.Cube.BitEval
import NtimeDspace.Cube.BudgetForm
import NtimeDspace.Cube.BudgetNum
import NtimeDspace.Cube.BudgetTerm
import NtimeDspace.Cube.Chain
import NtimeDspace.Cube.Clique
import NtimeDspace.Cube.CodeNum
import NtimeDspace.Cube.CodeTerm
import NtimeDspace.Cube.Codes
import NtimeDspace.Cube.EntryNum
import NtimeDspace.Cube.EntryTerm
import NtimeDspace.Cube.EntryTerm2
import NtimeDspace.Cube.EntryTerm3
import NtimeDspace.Cube.FirstClique
import NtimeDspace.Cube.FirstNum
import NtimeDspace.Cube.FirstTerm
import NtimeDspace.Cube.Formula
import NtimeDspace.Cube.Gen
import NtimeDspace.Cube.GenBits
import NtimeDspace.Cube.GenNum
import NtimeDspace.Cube.GenPar
import NtimeDspace.Cube.GenSize
import NtimeDspace.Cube.GenTerm
import NtimeDspace.Cube.GenTier
import NtimeDspace.Cube.Limits
import NtimeDspace.Cube.Merge
import NtimeDspace.Cube.MergeAux
import NtimeDspace.Cube.NetInst
import NtimeDspace.Cube.NetInstBlock
import NtimeDspace.Cube.NetTerms
import NtimeDspace.Cube.NumBasic
import NtimeDspace.Cube.Paths
import NtimeDspace.Cube.PathsAux
import NtimeDspace.Cube.PieceFacts
import NtimeDspace.Cube.Pieces
import NtimeDspace.Cube.RowCut
import NtimeDspace.Cube.Sound
import NtimeDspace.Cube.SoundBase
import NtimeDspace.Cube.SoundCodes
import NtimeDspace.Cube.SoundCopies
import NtimeDspace.Cube.SoundEnt
import NtimeDspace.Cube.SoundTr
import NtimeDspace.Cube.StCode
import NtimeDspace.Cube.StSize
import NtimeDspace.Cube.TransNum
import NtimeDspace.Cube.TransTerm
import NtimeDspace.Cube.Transport
import NtimeDspace.Cube.Walk
import NtimeDspace.Cross.NetFamily
import NtimeDspace.Cross.CubeStatement
import NtimeDspace.Cross.CubeCounting
import NtimeDspace.Cross.CubeFinal
import NtimeDspace.Cross.CountingScale
import NtimeDspace.Cross.ThreeSat.AtScale
import NtimeDspace.Cross.ColumnAdderAt
import NtimeDspace.Cross.CountingAt
import NtimeDspace.Cross.DivLogScale
import NtimeDspace.Cross.CountingAtFinal
import NtimeDspace.Cube.Examples
import NtimeDspace.Cube.Walsh
import NtimeDspace.Cube.LimitsCor
import NtimeDspace.Checks.CubeAxioms
import NtimeDspace.Checks.SolutionCrossTheorem
import NtimeDspace.Checks.SolutionCountingFinal

/-!
# NTIME(t) ⊆ SPACE(t / √log t) and its Separations

This is the top-level aggregator module for the `ntimeDspace` Lean 4 library. It formalizes the
current `separating-ntime-from-space.tex` (crossing pieces from walks on the cube, the merge of §6, the explicit formula
and the transfer); `Checks/CubeAxioms.lean` audits each statement for the standard axioms only.

* **Theorem 1.1**: `Crossing.ntime_decidable_sqrtLog_general`, `Crossing.ntime_subset_dspace_sqrtLog_general`
  (linear time: `Crossing.ntime_decidable_sqrtLog`, `Crossing.ntime_subset_dspace_sqrtLog`)
* **Corollary 1.2**: (i) `Crossing.ntime_ssubset_dspace_general`, `Crossing.ntime_ssubset_nspace_general`,
  `Crossing.ntime_ssubset_dspace`; (ii) `Crossing.ntime_mul_sqrtLog_subset_dspace_general`; (iii)
  `Crossing.exists_dspace_linear_ntime_lower_bound_general`; (iv) `Crossing.pptime_ssubset_dspace_general`,
  `Crossing.bptime_ssubset_dspace`, `Cross.exists_dspace_linear_pptime_lower_bound`
* **Definition 2.1**: `Cross.LogspaceNetFamily` (`Cross/NetFamily.lean`)
* **Lemma 2.2**: Complexitylib's block networks, `sum_contraction_blockNetworkOf`; as integer networks
  read by programs, `Cube.Num.blockNet`, `blockNet_value`, `blockNetT`
* **Theorem 2.3**: `Cross.cubeCounting : Cross.CubeCounting` (bit form, every logspace family);
  `Cross.cubeBlockBits : Cross.Exact.BlockBits` (the block networks, schedule as data)
* **Theorem 2.4**: `Cross.Exact.clockedBits_of_blockBits` (column adder over schedules),
  `Cross.Exact.clockedCounting_of_clockedBits`, `Cross.generalSimulation_of_clocked`
* **Lemma 2.5**: `Cross.spaceDiagonal_ae_lower_bound`
* **Proposition 3.2**: `SumProduct.GenProg.main_spec` (`SumProduct.Eval`)
* **Lemma 4.1**: `Cube.decode_labelCode`, `Cube.labelCode_decode`, `Cube.sum_codes`
* **Lemma 4.3**: `Cube.firstClique_value`, `Cube.firstClique_potential`; (c) in `Cube/FirstTerm.lean`
* **Lemmas 5.1–5.3**: `Cube.walk_coeff`, `Cube.piece_eval_one`, `Cube.piece_transpose`
* **Lemma 5.4, Corollary 5.5**: `Cube.rowCut_finsum`, `Cube.rowCut_coeff`, `Cube.nUp_lower`,
  `Cube.nDown_lower`; `Cube.rowCut`, `Cube.colCut`
* **Lemma 5.6**: `Cube.transportL_pivot`; its machine in `Cube/TransNum.lean`, `Cube/TransTerm.lean`
* **Lemma 6.1**: `Cube.energy_le`; **Lemma 6.2**: `Cube.merge`, `Cube.value_childAt`
* **The formula**: `Cube.Setup.gen`, `Cube.Setup.formula_value`; **Lemma 6.3**: `Cube.formula_cost`
* **Lemma 6.4**: `Cube.Num.cube_agrees`, `Cube.cubeProg`, `Cube.state_size`, `Cube.Num.cube_bit`
* **Theorem 7.1**: `Crossing.pptime_subset_dspace_sqrtLog_general`, `Crossing.bptime_subset_dspace_sqrtLog_general`,
  `Crossing.parityTIME_subset_dspace_sqrtLog_general`, `Crossing.modTIME_subset_dspace_sqrtLog_general`,
  `Crossing.ceqTIME_subset_dspace_sqrtLog_general`
* **Corollary 7.2**: `Cross.ThreeSat.cor_9_4_unconditional`, `Cross.ThreeSat.cor_9_4_bits_unconditional`
* **Propositions 8.1, 8.2**: `Cube.prop_boolean`, `Cube.prop_barrier`
* **§8, the limits of counting**: `Cross.ThreeSat.smallBits_of_scale` (counting every network with logspace
  access in space `D(s)` counts 3-SAT in time `2^{O(D(m))}`), with `smallBits_nlog` (`2^{O(m/log m)}`) and
  `smallBits_rpow` (`2^{O(m^{1-ε})}`); `Cross.ntime_subset_dspace_of_blockBitsAt`,
  `Cross.pptime_subset_dspace_of_blockBitsAt` (Theorem 2.3 at a scale `D` puts `NTIME[t]` and `PPTIME[t]` in
  `DSPACE[D(t)]`), at `t/log t`: `Crossing.*_subset_dspace_divLog_of_blockBitsAt`; the route needs
  `D = Ω(t/log t)` (`Cross.Exact.CarryFits.div_log_le`)
* **Consequences of Propositions 8.1, 8.2**: `Cube.prop_boolean_sq`, `Cube.prop_barrier_sq`,
  `Cube.equalWidth_barrier`, `Cube.equalWidth_sum`
* **Examples and remarks of §5**: `Cube.ex_piece`, `Cube.ex_rowSplit`, `Cube.ex_colSplit`, `Cube.ex_mixed`
  (the worked examples); `Cube.C_eq_prod`, `Cube.cMat_mul_self`, `Cube.hadamard_mul_self`,
  `Cube.hadamard_diagonalizes` (the Walsh–Hadamard remark)
* **Remark 8.3**: `Cross.Relativization.separation_does_not_relativize_bsa`,
  `Cross.Relativization.relativization_equalities_bsa`, `Cross.Relativization.relativization_collapse_bsa`
-/
