/-
Copyright (c) 2026 The NtimeDspace Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The NtimeDspace Authors
-/

import NtimeDspace.HermiteTuple
import NtimeDspace.HermiteGlobal

/-!
# Hermite recovery with factorwise truncated weights

The product of the separately truncated reciprocal factors agrees below the
truncation order with the reciprocal of their product. Its degree can be larger
than the order, so scalar recovery requires an explicit no-alias bound on the
degree of the product with the Taylor polynomial. This is the flat-weight
variant of the scalar recovery argument; it does not assert machine resources.
-/

namespace NtimeDspace.FlatHermite

open scoped BigOperators
open HermiteRecovery

variable {p : ℕ} [Fact p.Prime]

/-- Multiply the truncated reciprocal of each supplied factor, without
truncating their product. -/
noncomputable def flatWeight (factor : IntervalCoefficients.Factors p)
    (count order : ℕ) : Polynomial (ZMod p) :=
  ∏ slot ∈ Finset.range count,
    truncatedInverse ((Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2) order

/-- Truncating the flat product recovers the reciprocal of the whole denominator. -/
theorem trunc_flatWeight (factor : IntervalCoefficients.Factors p) (count order : ℕ) :
    PowerSeries.trunc order (flatWeight factor count order : PowerSeries (ZMod p)) =
      truncatedInverse (∏ slot ∈ Finset.range count,
        (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2) order := by
  simp only [flatWeight, truncatedInverse, HermiteTuple.coe_prod']
  rw [HermiteTuple.trunc_prod_trunc, HermiteTuple.inv_prod]

/-- The flat product has one degree bound for each factor. -/
theorem flatWeight_degree_le (factor : IntervalCoefficients.Factors p)
    (count order : ℕ) (positive : 0 < order) :
    (flatWeight factor count order).natDegree ≤ count * (order - 1) := by
  unfold flatWeight
  calc
    _ ≤ ∑ slot ∈ Finset.range count,
        (truncatedInverse ((Polynomial.X + Polynomial.C (factor slot).1) ^
          (factor slot).2) order).natDegree :=
      Polynomial.natDegree_prod_le (Finset.range count) (fun slot =>
        truncatedInverse ((Polynomial.X + Polynomial.C (factor slot).1) ^
          (factor slot).2) order)
    _ ≤ ∑ _slot ∈ Finset.range count, (order - 1) := by
      apply Finset.sum_le_sum
      intro slot _
      have := truncatedInverse_degree_lt
        ((Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2) order positive
      omega
    _ = count * (order - 1) := by simp

/-- A low product coefficient is unchanged by replacing the global truncation
with the product of the factorwise truncations. -/
theorem coeff_mul_flatWeight (Y : Polynomial (ZMod p))
    (factor : IntervalCoefficients.Factors p) (count order index : ℕ)
    (below : index < order) :
    (Y * flatWeight factor count order).coeff index =
      (Y * truncatedInverse (∏ slot ∈ Finset.range count,
        (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2) order).coeff
          index := by
  rw [← trunc_flatWeight factor count order,
    coeff_mul_trunc_right _ _ _ _ below, ← Polynomial.coe_mul, Polynomial.coeff_coe]

/-- Scalar evaluation computes a flat weight by one finite sum for each factor. -/
def flatWeightEvaluation (factor : IntervalCoefficients.Factors p)
    (count order : ℕ) (z : ZMod p) : ZMod p :=
  ∏ slot ∈ Finset.range count, ∑ index ∈ Finset.range order,
    modularReciprocalCoefficient (factor slot).1 (factor slot).2 index * z ^ index

theorem flatWeightEvaluation_correct (factor : IntervalCoefficients.Factors p)
    (count order : ℕ) (valid : IntervalCoefficients.Valid factor count)
    (within : order ≤ p) (z : ZMod p) :
    flatWeightEvaluation factor count order z = (flatWeight factor count order).eval z := by
  classical
  simp only [flatWeightEvaluation, flatWeight, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro slot member
  rw [truncatedInverse, HermiteTuple.trunc_eq_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro index member_index
  rw [Polynomial.eval_monomial,
    modularReciprocalCoefficient_correct (factor slot).1
      (valid slot (Finset.mem_range.mp member)).1 (factor slot).2 index
      (valid slot (Finset.mem_range.mp member)).2
      ((Finset.mem_range.mp member_index).trans_le within)]
  simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C,
    add_comm]

/-- The existing interval procedure evaluates the global reciprocal truncation. -/
theorem weightEvaluation_eq_eval_truncatedInverse (factor : IntervalCoefficients.Factors p)
    (count order : ℕ) (valid : IntervalCoefficients.Valid factor count)
    (within : order ≤ p) (z : ZMod p) :
    IntervalCoefficients.weightEvaluation factor count order z =
      (truncatedInverse (∏ slot ∈ Finset.range count,
        (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2) order).eval z := by
  rw [IntervalCoefficients.weightEvaluation, sumLoop_correct, add_zero,
    truncatedInverse, HermiteTuple.trunc_eq_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro index member
  rw [IntervalCoefficients.allCoefficient_correct factor count valid index
    ((Finset.mem_range.mp member).trans_le within), Polynomial.eval_monomial]

/-- The flat scalar sum recovers the same low coefficient provided the entire
product stays below the first aliased exponent. -/
theorem flatWeight_projector (Y : Polynomial (ZMod p))
    (factor : IntervalCoefficients.Factors p) (count order : ℕ)
    (valid : IntervalCoefficients.Valid factor count)
    (positive : 0 < order) (below_prime : order < p)
    (degree_bound : Y.natDegree + count * (order - 1) < p + order - 2) :
    (Y * truncatedInverse (∏ slot ∈ Finset.range count,
      (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2) order).coeff
        (order - 1) =
      -(∑ z : (ZMod p)ˣ, (z : ZMod p) ^ (p - order) *
        flatWeightEvaluation factor count order (z : ZMod p) * Y.eval (z : ZMod p)) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hi : order - 1 < p - 1 := by omega
  have hdegree : (Y * flatWeight factor count order).natDegree <
      (order - 1) + (p - 1) := by
    have hmul := Polynomial.natDegree_mul_le (p := Y) (q := flatWeight factor count order)
    have hweight := flatWeight_degree_le factor count order positive
    omega
  have hexp : p - 1 - (order - 1) = p - order := by omega
  rw [← coeff_mul_flatWeight Y factor count order (order - 1) (by omega),
    coefficient_projector_neg _ _ hi hdegree, hexp]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  rw [Polynomial.eval_mul,
    flatWeightEvaluation_correct factor count order valid below_prime.le]
  ring

/-- Replacing the old weight by its flat variant preserves the scalar sum for
a polynomial callback under the stronger no-alias bound. It is not a pointwise
equality of the two weights. -/
theorem scalar_sum_flatWeightEvaluation_eq (Y : Polynomial (ZMod p))
    (factor : IntervalCoefficients.Factors p) (count order : ℕ)
    (valid : IntervalCoefficients.Valid factor count)
    (positive : 0 < order) (below_prime : order < p)
    (Y_degree : Y.natDegree ≤ p - 2)
    (degree_bound : Y.natDegree + count * (order - 1) < p + order - 2) :
    (∑ z : (ZMod p)ˣ, (z : ZMod p) ^ (p - order) *
      flatWeightEvaluation factor count order (z : ZMod p) * Y.eval (z : ZMod p)) =
      ∑ z : (ZMod p)ˣ, (z : ZMod p) ^ (p - order) *
        IntervalCoefficients.weightEvaluation factor count order (z : ZMod p) *
          Y.eval (z : ZMod p) := by
  have flat := flatWeight_projector Y factor count order valid positive below_prime degree_bound
  have old := weighted_taylor_projector Y
    (truncatedInverse (∏ slot ∈ Finset.range count,
      (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2) order)
    order positive below_prime Y_degree (truncatedInverse_degree_lt _ _ positive)
  simp_rw [← weightEvaluation_eq_eval_truncatedInverse factor count order valid below_prime.le] at old
  exact neg_inj.mp (flat.symm.trans old)

end NtimeDspace.FlatHermite
