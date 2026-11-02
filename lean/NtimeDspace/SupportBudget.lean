import NtimeDspace.SupportBounds
import Mathlib.Algebra.Order.Floor.Div

/-!
# Executable support-code length budget

The integer ceiling division below equals the real-valued ceiling used by the
support-length and asymptotic proofs. Its evaluation uses only natural-number
arithmetic, including when the numerator is zero.
-/

namespace NtimeDspace.SupportBudget

/-- Ceiling division by a positive natural agrees with the natural ceiling
of the corresponding exact real quotient. -/
theorem ceilDiv_eq_natCeil (numerator denominator : ℕ) (positive : 0 < denominator) :
    (numerator + denominator - 1) / denominator = ⌈(numerator : ℝ) / denominator⌉₊ := by
  apply eq_of_forall_ge_iff
  intro bound
  rw [← Nat.ceilDiv_eq_add_pred_div, ceilDiv_le_iff_le_smul positive,
    Nat.ceil_le, div_le_iff₀ (show (0 : ℝ) < denominator by exact_mod_cast positive)]
  norm_cast
  simp only [smul_eq_mul, Nat.mul_comm]

/-- Integer-only implementation of the manuscript's support-code budget. -/
def limit (N k : ℕ) : ℕ :=
  (24 * N * (2 * k + 1) + Parameters.s k - 1) / Parameters.s k

theorem limit_eq_supportLimit (N k : ℕ) : limit N k = SupportBounds.supportLimit N k := by
  rw [limit, ceilDiv_eq_natCeil _ _ (Parameters.s_pos k), SupportBounds.supportLimit]
  norm_cast

end NtimeDspace.SupportBudget
