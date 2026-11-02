import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
The finite-field coefficient projector used in paper.tex, Lemma `lem:scalar`.
The cutoff is relative to the requested coefficient: `degree B < i + (p - 1)`.
This is the no-aliasing step of scalar recovery, not the full Hermite theorem.
-/

namespace NtimeDspace

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem projector_monomial (i e : ℕ) (hi : i < p - 1)
    (he : e < i + (p - 1)) :
    (∑ z : (ZMod p)ˣ, (z : ZMod p) ^ (p - 1 - i) * (z : ZMod p) ^ e) =
      if e = i then -1 else 0 := by
  have hdiv : (p - 1 ∣ p - 1 - i + e) ↔ e = i := by
    constructor
    · intro h
      have hpos : 0 < p - 1 - i + e := by omega
      have hlt : p - 1 - i + e < 2 * (p - 1) := by omega
      obtain ⟨k, hk⟩ := h
      have hkpos : 0 < k := by
        by_contra h
        have : k = 0 := by omega
        simp [this] at hk
        omega
      have hklt : k < 2 := by nlinarith
      have : k = 1 := by omega
      simp [this] at hk
      omega
    · intro hei
      subst e
      have : p - 1 - i + i = p - 1 := by omega
      rw [this]
  simp_rw [← pow_add]
  simpa only [ZMod.card, hdiv] using
    (FiniteField.sum_pow_units (ZMod p) (p - 1 - i + e))

/-- Weighted evaluations recover a single coefficient without storing all coefficients. -/
theorem coefficient_projector (B : Polynomial (ZMod p)) (i : ℕ)
    (hi : i < p - 1) (hdeg : B.natDegree < i + (p - 1)) :
    (∑ z : (ZMod p)ˣ, (z : ZMod p) ^ (p - 1 - i) * B.eval (z : ZMod p)) =
      -B.coeff i := by
  classical
  calc
    _ = ∑ e ∈ Finset.range (B.natDegree + 1), B.coeff e *
        (∑ z : (ZMod p)ˣ, (z : ZMod p) ^ (p - 1 - i) * (z : ZMod p) ^ e) := by
      simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = ∑ e ∈ Finset.range (B.natDegree + 1), if e = i then -B.coeff e else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      have he' : e < i + (p - 1) := by
        have := Finset.mem_range.mp he
        omega
      rw [projector_monomial i e hi he']
      split_ifs <;> simp
    _ = -B.coeff i := by
      by_cases h : i < B.natDegree + 1
      · simp [h]
      · have hc : B.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [h, hc]

/-- The form used after multiplying the untruncated Taylor polynomial by its weight. -/
theorem coefficient_projector_neg (B : Polynomial (ZMod p)) (i : ℕ)
    (hi : i < p - 1) (hdeg : B.natDegree < i + (p - 1)) :
    B.coeff i = -(∑ z : (ZMod p)ˣ,
      (z : ZMod p) ^ (p - 1 - i) * B.eval (z : ZMod p)) := by
  rw [coefficient_projector B i hi hdeg, neg_neg]

/-- At the first excluded monomial, a second exponent aliases the target.
Thus the strict degree cutoff in `coefficient_projector` is necessary. -/
theorem projector_first_alias (i : ℕ) (hi : i < p - 1) :
    (∑ z : (ZMod p)ˣ,
      (z : ZMod p) ^ (p - 1 - i) * (z : ZMod p) ^ (i + (p - 1))) = -1 := by
  have hexp : (p - 1 - i) + (i + (p - 1)) = 2 * (p - 1) := by omega
  simp_rw [← pow_add, hexp]
  rw [FiniteField.sum_pow_units, ZMod.card, if_pos (dvd_mul_left _ _)]

end NtimeDspace
