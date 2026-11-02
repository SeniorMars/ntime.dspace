import NtimeDspace.HermiteCoefficientLoop

/-!
The complete closed-loop budget is quadratic in the modulus bit width when
its scalar parameters are bounded by the modulus. This includes the input,
retained parameters, and serialized continuation stack, before compilation.
-/

namespace NtimeDspace.HermiteCoefficientBudget

open Turing Turing.MultiTapeTM CoefficientStackEncoding

theorem height_le_log (p count : ℕ) (bounded : count ≤ p) :
    CoefficientInitialization.height count ≤ p.log2 + 1 := by
  rw [CoefficientInitialization.height_eq_clog]
  exact Nat.clog_le_of_le_pow (bounded.trans (Nat.lt_log2_self (n := p)).le)

theorem register_bound_le (p count index : ℕ) (positive : 0 < p)
    (countBound : count ≤ p) (indexBound : index ≤ p) :
    runRegisterBound (CoefficientInitialization.request count 0 index) p ≤ 2 * p := by
  have height := height_le_log p count countBound
  have logarithm := Nat.log2_le_self p
  have span := CoefficientInitialization.span_le count
  have envelope : max 1 count ≤ p := max_le (by omega) countBound
  unfold runRegisterBound CoefficientInitialization.request
  dsimp only
  simp only [max_le_iff, Nat.zero_add]
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem register_log_bound (p count index : ℕ) (positive : 0 < p)
    (countBound : count ≤ p) (indexBound : index ≤ p) :
    (runRegisterBound (CoefficientInitialization.request count 0 index) p).log2 + 1 ≤
      p.log2 + 2 := by
  let B := runRegisterBound (CoefficientInitialization.request count 0 index) p
  have bounded : B ≤ 2 * p := register_bound_le p count index positive countBound indexBound
  by_cases zero : B = 0
  · simp only [B, zero, Nat.log2_zero]
    omega
  · have pSmall := Nat.lt_log2_self (n := p)
    have upper : B < 2 ^ (p.log2 + 2) := by
      rw [show p.log2 + 2 = (p.log2 + 1) + 1 by omega, pow_succ]
      omega
    have logarithm := (Nat.log2_lt zero).mpr upper
    change B.log2 + 1 ≤ _
    omega

/-- A concrete bound on the complete scalar-input and stack budget. The
parameter restrictions hold in the intended Hermite recovery range. -/
theorem spaceBound_le (p count node order index : ℕ) (positive : 0 < p)
    (countBound : count ≤ p) (nodeBound : node ≤ p)
    (orderBound : order ≤ p) (indexBound : index ≤ p) :
    HermiteCoefficientLoop.spaceBound (p, count, node, order, index) ≤
      256 * (p.log2 + 1) ^ 2 := by
  have input := HermiteFactorSpace.encInput_length_le p count node order index p
    le_rfl countBound nodeBound orderBound indexBound
  have bp := length_encNat_le_log2 (Nat.le_refl p)
  have bc := length_encNat_le_log2 countBound
  have bn := length_encNat_le_log2 nodeBound
  have bo := length_encNat_le_log2 orderBound
  have height := height_le_log p count countBound
  have registers := register_log_bound p count index positive countBound indexBound
  have productBound :
      (CoefficientInitialization.height count + 1) *
        (28 * ((runRegisterBound (CoefficientInitialization.request count 0 index) p).log2 + 1) + 15) ≤
      (p.log2 + 2) * (28 * (p.log2 + 2) + 15) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold HermiteCoefficientLoop.spaceBound
  dsimp only
  nlinarith [Nat.zero_le p.log2]

end NtimeDspace.HermiteCoefficientBudget
