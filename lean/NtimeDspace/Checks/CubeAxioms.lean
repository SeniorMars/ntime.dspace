/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/
import NtimeDspace.Cross.Theorem
import NtimeDspace.Cross.CountingFinal
import NtimeDspace.Cross.ThreeSat.Unconditional
import NtimeDspace.Cube.Limits
import NtimeDspace.Cube.GenBits
import NtimeDspace.Cube.StSize
import NtimeDspace.Cube.BitEval
import NtimeDspace.Cross.PPSeparation
import NtimeDspace.Cross.PPLowerBound
import NtimeDspace.Cross.Relativization
import NtimeDspace.Cross.Hierarchy
import NtimeDspace.Cross.ThreeSat.AtScale
import NtimeDspace.Cross.CountingAtFinal
import NtimeDspace.Cube.Examples
import NtimeDspace.Cube.Walsh
import NtimeDspace.Cube.LimitsCor

-- upstream: local-only (project scaffolding: axiom audit of the route of separating-ntime-from-space.tex)

/-!
# Axiom audit of the current paper

For each statement of `separating-ntime-from-space.tex` (the route of §§2–8: crossing pieces from walks on the cube, the
merge, the explicit formula, and the transfer), the declarations that formalize it, with a check that
each depends only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. Each check
is a `#guard_msgs`, so the build fails if a declaration is missing or picks up any other axiom
(including `sorryAx`). The endpoints are those of the comparator challenges `NtimeChallengeCross` and
`NtimeChallengeGeneral`.
-/

/-! ## Theorem 1.1 and Corollary 1.2 (general and linear time) -/

/-- info: 'NtimeDspace.Crossing.ntime_decidable_sqrtLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_decidable_sqrtLog

/-- info: 'NtimeDspace.Crossing.ntime_subset_dspace_sqrtLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_subset_dspace_sqrtLog

/-- info: 'NtimeDspace.Crossing.ntime_ssubset_dspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_ssubset_dspace

/-- info: 'NtimeDspace.Crossing.generalSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.generalSimulation

/-- info: 'NtimeDspace.Crossing.ntime_decidable_sqrtLog_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_decidable_sqrtLog_general

/-- info: 'NtimeDspace.Crossing.ntime_subset_dspace_sqrtLog_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_subset_dspace_sqrtLog_general

/-- info: 'NtimeDspace.Crossing.ntime_ssubset_dspace_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_ssubset_dspace_general

/-- info: 'NtimeDspace.Crossing.ntime_ssubset_nspace_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_ssubset_nspace_general

/-- info: 'NtimeDspace.Crossing.ntime_mul_sqrtLog_subset_dspace_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_mul_sqrtLog_subset_dspace_general

/-- info: 'NtimeDspace.Crossing.exists_dspace_linear_ntime_lower_bound_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.exists_dspace_linear_ntime_lower_bound_general

/-! ## Corollary 1.2 (iv) -/

/-- info: 'NtimeDspace.Crossing.pptime_ssubset_dspace_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.pptime_ssubset_dspace_general

/-- info: 'NtimeDspace.Crossing.bptime_ssubset_dspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.bptime_ssubset_dspace

/-- info: 'NtimeDspace.Cross.exists_dspace_linear_pptime_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.exists_dspace_linear_pptime_lower_bound

/-! ## Lemma 2.2 (block networks) and Lemma 2.5 (hierarchy) -/

/-- info: 'Cslib.Complexity.CountingSimulation.sum_contraction_blockNetworkOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Cslib.Complexity.CountingSimulation.sum_contraction_blockNetworkOf

/-- info: 'NtimeDspace.Cross.spaceDiagonal_ae_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.spaceDiagonal_ae_lower_bound

/-! ## Remark 8.3 (relativization) -/

/-- info: 'NtimeDspace.Cross.Relativization.separation_does_not_relativize_bsa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.Relativization.separation_does_not_relativize_bsa

/-- info: 'NtimeDspace.Cross.Relativization.relativization_equalities_bsa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.Relativization.relativization_equalities_bsa

/-- info: 'NtimeDspace.Cross.Relativization.relativization_collapse_bsa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.Relativization.relativization_collapse_bsa

/-! ## Theorems 2.3 and 2.4 -/

/-- info: 'NtimeDspace.Cross.cubeCounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.cubeCounting

/-- info: 'NtimeDspace.Cross.cubeBlockBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.cubeBlockBits

/-- info: 'NtimeDspace.Cross.Exact.clockedBits_of_blockBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.Exact.clockedBits_of_blockBits

/-- info: 'NtimeDspace.Cross.Exact.clockedCounting_of_clockedBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.Exact.clockedCounting_of_clockedBits

/-! ## Proposition 3.2 and Lemma 6.4: the explicit formula and its bits -/

/-- info: 'NtimeDspace.SumProduct.GenProg.main_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.SumProduct.GenProg.main_spec

/-- info: 'NtimeDspace.Cube.Num.cube_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.Num.cube_bit

/-- info: 'NtimeDspace.Cube.state_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.state_size

/-! ## Lemmas 4.1 and 4.3: codes and the first clique -/

/-- info: 'NtimeDspace.Cube.decode_labelCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.decode_labelCode

/-- info: 'NtimeDspace.Cube.labelCode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.labelCode_decode

/-- info: 'NtimeDspace.Cube.sum_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.sum_codes

/-- info: 'NtimeDspace.Cube.firstClique_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.firstClique_value

/-- info: 'NtimeDspace.Cube.firstClique_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.firstClique_potential

/-! ## Lemmas 5.1–5.6 and Corollary 5.5: crossing pieces -/

/-- info: 'NtimeDspace.Cube.walk_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.walk_coeff

/-- info: 'NtimeDspace.Cube.piece_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.piece_eval_one

/-- info: 'NtimeDspace.Cube.piece_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.piece_transpose

/-- info: 'NtimeDspace.Cube.rowCut_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.rowCut_coeff

/-- info: 'NtimeDspace.Cube.rowCut_finsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.rowCut_finsum

/-- info: 'NtimeDspace.Cube.rowCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.rowCut

/-- info: 'NtimeDspace.Cube.colCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.colCut

/-- info: 'NtimeDspace.Cube.transportL_pivot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.transportL_pivot

/-! ## Lemmas 6.1–6.3: potential, merge, the formula and its index lengths -/

/-- info: 'NtimeDspace.Cube.energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.energy_le

/-- info: 'NtimeDspace.Cube.merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.merge

/-- info: 'NtimeDspace.Cube.value_childAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.value_childAt

/-- info: 'NtimeDspace.Cube.Setup.formula_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.Setup.formula_value

/-- info: 'NtimeDspace.Cube.formula_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.formula_cost

/-! ## Theorem 7.1 and Corollary 7.2 -/

/-- info: 'NtimeDspace.Crossing.pptime_subset_dspace_sqrtLog_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.pptime_subset_dspace_sqrtLog_general

/-- info: 'NtimeDspace.Crossing.bptime_subset_dspace_sqrtLog_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.bptime_subset_dspace_sqrtLog_general

/-- info: 'NtimeDspace.Crossing.parityTIME_subset_dspace_sqrtLog_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.parityTIME_subset_dspace_sqrtLog_general

/-- info: 'NtimeDspace.Crossing.modTIME_subset_dspace_sqrtLog_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.modTIME_subset_dspace_sqrtLog_general

/-- info: 'NtimeDspace.Crossing.ceqTIME_subset_dspace_sqrtLog_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ceqTIME_subset_dspace_sqrtLog_general

/-- info: 'NtimeDspace.Cross.ThreeSat.cor_9_4_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.ThreeSat.cor_9_4_unconditional

/-- info: 'NtimeDspace.Cross.ThreeSat.cor_9_4_bits_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.ThreeSat.cor_9_4_bits_unconditional

/-! ## Propositions 8.1 and 8.2 -/

/-- info: 'NtimeDspace.Cube.prop_boolean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.prop_boolean

/-- info: 'NtimeDspace.Cube.prop_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.prop_barrier

/-! ## §8, first paragraph: counting every network in space D(s) counts 3-SAT in time 2^{O(D(m))} -/

/-- info: 'NtimeDspace.Cross.cubeCountingAt_sqrtLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.cubeCountingAt_sqrtLog

/-- info: 'NtimeDspace.Cross.ThreeSat.smallBits_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.ThreeSat.smallBits_at

/-- info: 'NtimeDspace.Cross.ThreeSat.smallBits_of_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.ThreeSat.smallBits_of_scale

/-- info: 'NtimeDspace.Cross.ThreeSat.smallBits_nlog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.ThreeSat.smallBits_nlog

/-- info: 'NtimeDspace.Cross.ThreeSat.smallBits_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.ThreeSat.smallBits_rpow

/-! ## §8, second paragraph: Theorem 2.3 at a scale D puts NTIME[t], PPTIME[t] and BPTIME[t] in DSPACE[D(t)] -/

/-- info: 'NtimeDspace.Cross.Exact.clockedBitsAt_of_blockBitsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.Exact.clockedBitsAt_of_blockBitsAt

/-- info: 'NtimeDspace.Cross.Exact.clockedCountingAt_of_clockedBitsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.Exact.clockedCountingAt_of_clockedBitsAt

/-- info: 'NtimeDspace.Cross.Exact.CarryFits.div_log_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.Exact.CarryFits.div_log_le

/-- info: 'NtimeDspace.Cross.generalSimulationAt_of_blockBitsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.generalSimulationAt_of_blockBitsAt

/-- info: 'NtimeDspace.Cross.ntime_subset_dspace_of_blockBitsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.ntime_subset_dspace_of_blockBitsAt

/-- info: 'NtimeDspace.Cross.pptime_subset_dspace_of_blockBitsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.pptime_subset_dspace_of_blockBitsAt

/-- info: 'NtimeDspace.Cross.bptime_subset_dspace_of_blockBitsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cross.bptime_subset_dspace_of_blockBitsAt

/-- info: 'NtimeDspace.Crossing.ntime_subset_dspace_divLog_of_blockBitsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_subset_dspace_divLog_of_blockBitsAt

/-- info: 'NtimeDspace.Crossing.pptime_subset_dspace_divLog_of_blockBitsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.pptime_subset_dspace_divLog_of_blockBitsAt

/-- info: 'NtimeDspace.Crossing.bptime_subset_dspace_divLog_of_blockBitsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.bptime_subset_dspace_divLog_of_blockBitsAt

/-- info: 'NtimeDspace.Crossing.ntime_subset_dspace_sqrtLog_viaAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.ntime_subset_dspace_sqrtLog_viaAt

/-- info: 'NtimeDspace.Crossing.pptime_subset_dspace_sqrtLog_viaAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.pptime_subset_dspace_sqrtLog_viaAt

/-- info: 'NtimeDspace.Crossing.bptime_subset_dspace_sqrtLog_viaAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Crossing.bptime_subset_dspace_sqrtLog_viaAt

/-! ## The examples of §5 (after Lemma 5.3 and after Corollary 5.5) -/

/-- info: 'NtimeDspace.Cube.ex_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.ex_piece

/-- info: 'NtimeDspace.Cube.ex_piece_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.ex_piece_transpose

/-- info: 'NtimeDspace.Cube.rowCut_splits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.rowCut_splits

/-- info: 'NtimeDspace.Cube.colCut_splits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.colCut_splits

/-- info: 'NtimeDspace.Cube.ex_rowSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.ex_rowSplit

/-- info: 'NtimeDspace.Cube.ex_colSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.ex_colSplit

/-- info: 'NtimeDspace.Cube.ex_rowCut_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.ex_rowCut_total

/-- info: 'NtimeDspace.Cube.ex_colCut_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.ex_colCut_total

/-- info: 'NtimeDspace.Cube.ex_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.ex_mixed

/-! ## The Walsh–Hadamard remark after Lemma 5.1 -/

/-- info: 'NtimeDspace.Cube.C_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.C_eq_prod

/-- info: 'NtimeDspace.Cube.cMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.cMat_mul_self

/-- info: 'NtimeDspace.Cube.sum_C_mul_C_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.sum_C_mul_C_eq_prod

/-- info: 'NtimeDspace.Cube.hadamard_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.hadamard_mul_self

/-- info: 'NtimeDspace.Cube.C_eq_hadamard_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.C_eq_hadamard_mul

/-- info: 'NtimeDspace.Cube.dyadic_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.dyadic_eigen

/-- info: 'NtimeDspace.Cube.hadamard_diagonalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.hadamard_diagonalizes

/-! ## §8: the consequences of Propositions 8.1 and 8.2 -/

/-- info: 'NtimeDspace.Cube.prop_boolean_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.prop_boolean_sq

/-- info: 'NtimeDspace.Cube.prop_barrier_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.prop_barrier_sq

/-- info: 'NtimeDspace.Cube.equalWidth_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.equalWidth_barrier

/-- info: 'NtimeDspace.Cube.equalWidth_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.equalWidth_sum

/-- info: 'NtimeDspace.Cube.equalWidth_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NtimeDspace.Cube.equalWidth_rho
