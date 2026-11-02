import NtimeDspace.ReciprocalCoefficients
import Mathlib.Data.ZMod.Basic

/-!
# Modular binomial coefficients without large integer intermediates

The loop multiplies `(multiplicity + i) / (i + 1)` directly in the prime
field. Its mutable arithmetic data are a decreasing natural index and one
field accumulator. `Nat.choose` occurs only in correctness statements and
proofs, never in the procedure. For indices below the prime, every divisor
is nonzero even when a numerator is zero in the field.

This removes an oversized integer intermediate from the reciprocal leaf.
Field operations and recursion still require a machine implementation before
any work-tape or bit-operation bound can be asserted.
-/

namespace NtimeDspace.HermiteRecovery

variable {p : ℕ} [Fact p.Prime]

/-- Descending scalar-accumulator loop; the multiplicity is already a residue. -/
def modularBinomialLoop (multiplicity : ZMod p) : ℕ → ZMod p → ZMod p
  | 0, accumulator => accumulator
  | index + 1, accumulator =>
      modularBinomialLoop multiplicity index
        (accumulator * (multiplicity + index) / (index + 1 : ℕ))

/-- Compute the rising binomial coefficient directly modulo the prime. -/
def modularBinomial (multiplicity index : ℕ) : ZMod p :=
  modularBinomialLoop (multiplicity : ZMod p) index 1

theorem index_cast_ne_zero {index : ℕ} (positive : 0 < index) (below : index < p) :
    (index : ZMod p) ≠ 0 := by
  intro zero
  have h := congrArg ZMod.val zero
  rw [ZMod.val_natCast_of_lt below, ZMod.val_zero] at h
  omega

/-- The binomial recurrence remains valid modulo `p`; only the denominator
needs to be nonzero. No bound on the numerator or multiplicity is required. -/
theorem binomial_cast_step (multiplicity index : ℕ) (positive : 0 < multiplicity)
    (below : index + 1 < p) :
    (Nat.choose (multiplicity + (index + 1) - 1) (index + 1) : ZMod p) =
      (Nat.choose (multiplicity + index - 1) index : ZMod p) *
        ((multiplicity : ZMod p) + index) / (index + 1 : ℕ) := by
  have denominator := index_cast_ne_zero (p := p) (index := index + 1) (by omega) below
  apply (eq_div_iff denominator).mpr
  have recurrence := Nat.add_one_mul_choose_eq (multiplicity + index - 1) index
  have next : multiplicity + index - 1 + 1 = multiplicity + index := by omega
  rw [next] at recurrence
  have cast_recurrence := congrArg (fun value : ℕ => (value : ZMod p)) recurrence
  push_cast at cast_recurrence
  simpa only [show multiplicity + (index + 1) - 1 = multiplicity + index by omega,
    Nat.cast_add, Nat.cast_one] using cast_recurrence.symm.trans
    (mul_comm _ _)

/-- Loop invariant: the remaining product is the indicated binomial residue. -/
theorem modularBinomialLoop_correct (multiplicity index : ℕ) (positive : 0 < multiplicity)
    (below : index < p) (accumulator : ZMod p) :
    modularBinomialLoop (multiplicity : ZMod p) index accumulator =
      accumulator * (Nat.choose (multiplicity + index - 1) index : ZMod p) := by
  induction index generalizing accumulator with
  | zero => simp [modularBinomialLoop]
  | succ index ih =>
      rw [modularBinomialLoop, ih (by omega), binomial_cast_step multiplicity index positive below]
      ring

theorem modularBinomial_correct (multiplicity index : ℕ) (positive : 0 < multiplicity)
    (below : index < p) :
    modularBinomial (p := p) multiplicity index =
      (Nat.choose (multiplicity + index - 1) index : ZMod p) := by
  simpa only [modularBinomial, one_mul] using
    modularBinomialLoop_correct multiplicity index positive below (1 : ZMod p)

/-- The reciprocal-series leaf with the binomial factor computed in the field. -/
def modularReciprocalCoefficient (a : ZMod p) (multiplicity index : ℕ) : ZMod p :=
  (-1) ^ index * modularBinomial multiplicity index * (a⁻¹) ^ (multiplicity + index)

theorem modularReciprocalCoefficient_eq (a : ZMod p) (multiplicity index : ℕ)
    (positive : 0 < multiplicity) (below : index < p) :
    modularReciprocalCoefficient a multiplicity index =
      reciprocalCoefficient a multiplicity index := by
  rw [modularReciprocalCoefficient, modularBinomial_correct multiplicity index positive below]
  rfl

/-- The modular loop computes the actual reciprocal power-series coefficient. -/
theorem modularReciprocalCoefficient_correct (a : ZMod p) (nonzero : a ≠ 0)
    (multiplicity index : ℕ) (positive : 0 < multiplicity) (below : index < p) :
    modularReciprocalCoefficient a multiplicity index =
      PowerSeries.coeff index
        (((PowerSeries.C a + PowerSeries.X : PowerSeries (ZMod p)) ^ multiplicity)⁻¹) := by
  rw [modularReciprocalCoefficient_eq a multiplicity index positive below]
  exact reciprocalCoefficient_correct a nonzero multiplicity index positive

/-- The bounded-index modular procedure can replace a reciprocal leaf in the
existing coefficient-tree correctness interface. -/
theorem modularReciprocalCoefficient_representsBelow (a : ZMod p) (nonzero : a ≠ 0)
    (multiplicity order : ℕ) (positive : 0 < multiplicity) (within : order ≤ p) :
    CoefficientTree.RepresentsBelow order
      (.leaf (modularReciprocalCoefficient a multiplicity))
      (truncatedInverse ((Polynomial.X + Polynomial.C a) ^ multiplicity) order) := by
  apply CoefficientTree.RepresentsBelow.leaf
  intro index below
  rw [truncatedInverse, PowerSeries.coeff_trunc, ite_eq_left below,
    modularReciprocalCoefficient_correct a nonzero multiplicity index positive
      (below.trans_le within)]
  simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X,
    Polynomial.coe_C, add_comm]

end NtimeDspace.HermiteRecovery
