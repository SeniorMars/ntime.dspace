/-
Copyright (c) 2026 The NtimeDspace Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The NtimeDspace Authors
-/

import NtimeDspace.FlatHermite

/-!
# A scalar Horner loop for reciprocal factors

The descending loop evaluates a truncated reciprocal factor with one field
accumulator. It uses the ratio between successive reciprocal coefficients, so
it does not recompute a binomial coefficient for each summand. The results here
specify arithmetic values; the program implementation and resource bounds are
separate.
-/

namespace NtimeDspace.FlatHermite

open scoped BigOperators
open HermiteRecovery

variable {p : ℕ} [Fact p.Prime]

theorem modularReciprocalCoefficient_zero (a : ZMod p) (multiplicity : ℕ) :
    modularReciprocalCoefficient a multiplicity 0 = (a⁻¹) ^ multiplicity := by
  simp [modularReciprocalCoefficient, modularBinomial, modularBinomialLoop]

/-- Only the next index must be below the prime; the numerator may vanish. -/
theorem modularReciprocalCoefficient_succ (a : ZMod p) (multiplicity index : ℕ)
    (positive : 0 < multiplicity) (below : index + 1 < p) :
    modularReciprocalCoefficient a multiplicity (index + 1) =
      -(modularReciprocalCoefficient a multiplicity index *
        ((multiplicity : ZMod p) + index) * a⁻¹ / (index + 1 : ℕ)) := by
  rw [modularReciprocalCoefficient, modularReciprocalCoefficient,
    modularBinomial_correct multiplicity (index + 1) positive below,
    modularBinomial_correct multiplicity index positive (by omega),
    binomial_cast_step multiplicity index positive below,
    pow_succ, show multiplicity + (index + 1) = (multiplicity + index) + 1 by omega,
    pow_succ]
  simp only [div_eq_mul_inv]
  ring

/-- Descending Horner evaluation with an explicit tail accumulator. -/
def factorHornerLoop (a : ZMod p) (multiplicity : ℕ) (z : ZMod p) :
    ℕ → ZMod p → ZMod p
  | 0, accumulator => accumulator
  | index + 1, accumulator =>
      factorHornerLoop a multiplicity z index
        (1 - accumulator * ((multiplicity : ZMod p) + index) * a⁻¹ * z /
          (index + 1 : ℕ))

/-- The constant reciprocal coefficient times the normalized Horner sum. -/
def factorHorner (a : ZMod p) (multiplicity : ℕ) (z : ZMod p) (order : ℕ) : ZMod p :=
  (a⁻¹) ^ multiplicity * factorHornerLoop a multiplicity z order 0

theorem factorHornerLoop_eq_reverse_foldl (a : ZMod p) (multiplicity : ℕ) (z : ZMod p)
    (order : ℕ) (accumulator : ZMod p) :
    factorHornerLoop a multiplicity z order accumulator =
      (List.range order).reverse.foldl (fun acc index =>
        1 - acc * ((multiplicity : ZMod p) + index) * a⁻¹ * z / (index + 1 : ℕ))
        accumulator := by
  induction order generalizing accumulator with
  | zero => rfl
  | succ order ih =>
      rw [factorHornerLoop, List.range_succ, List.reverse_append, List.foldl_append]
      simp only [List.reverse_singleton, List.foldl_cons, List.foldl_nil]
      exact ih _

/-- An ascending bounded program fold supplies the descending index explicitly. -/
theorem factorHornerLoop_eq_foldl (a : ZMod p) (multiplicity : ℕ) (z : ZMod p)
    (order : ℕ) (accumulator : ZMod p) :
    factorHornerLoop a multiplicity z order accumulator =
      (List.range order).foldl (fun acc index =>
        1 - acc * ((multiplicity : ZMod p) + ((order - 1 - index : ℕ) : ZMod p)) * a⁻¹ * z /
          ((order - 1 - index) + 1 : ℕ)) accumulator := by
  rw [factorHornerLoop_eq_reverse_foldl, List.range_eq_range', List.reverse_range',
    List.foldl_map]
  simp only [Nat.zero_add, ← List.range_eq_range']

/-- The tail accumulator represents one additional reciprocal-series term. -/
theorem factorHornerLoop_correct (a : ZMod p) (multiplicity : ℕ) (z : ZMod p)
    (order : ℕ) (positive : 0 < multiplicity) (below : order < p)
    (accumulator : ZMod p) :
    (a⁻¹) ^ multiplicity * factorHornerLoop a multiplicity z order accumulator =
      (∑ index ∈ Finset.range order,
        modularReciprocalCoefficient a multiplicity index * z ^ index) +
      accumulator * modularReciprocalCoefficient a multiplicity order * z ^ order := by
  induction order generalizing accumulator with
  | zero => simp [factorHornerLoop, modularReciprocalCoefficient_zero, mul_comm]
  | succ order ih =>
      rw [factorHornerLoop, ih (by omega), Finset.sum_range_succ,
        modularReciprocalCoefficient_succ a multiplicity order positive below, pow_succ]
      ring

/-- The Horner loop evaluates the same finite sum as one factor of the flat weight. -/
theorem factorHorner_eq_sum (a : ZMod p) (multiplicity : ℕ) (z : ZMod p)
    (order : ℕ) (positive : 0 < multiplicity) (within : order ≤ p) :
    factorHorner a multiplicity z order =
      ∑ index ∈ Finset.range order,
        modularReciprocalCoefficient a multiplicity index * z ^ index := by
  cases order with
  | zero => simp [factorHorner, factorHornerLoop]
  | succ order =>
      rw [factorHorner, factorHornerLoop]
      simp only [zero_mul, zero_div, sub_zero]
      rw [factorHornerLoop_correct a multiplicity z order positive (by omega),
        Finset.sum_range_succ, one_mul]

/-- The factorwise Horner values multiply to the flat-weight evaluation. -/
theorem prod_factorHorner_eq_flatWeightEvaluation
    (factor : IntervalCoefficients.Factors p) (count order : ℕ)
    (valid : IntervalCoefficients.Valid factor count) (within : order ≤ p) (z : ZMod p) :
    (∏ slot ∈ Finset.range count,
      factorHorner (factor slot).1 (factor slot).2 z order) =
        flatWeightEvaluation factor count order z := by
  apply Finset.prod_congr rfl
  intro slot member
  exact factorHorner_eq_sum _ _ _ _ (valid slot (Finset.mem_range.mp member)).2 within

end NtimeDspace.FlatHermite
