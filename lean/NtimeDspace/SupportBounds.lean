import NtimeDspace.SupportEncoding
import NtimeDspace.Parameters
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Aggregate length bounds for the actual Elias gamma gap encoding.
The logarithmic tangent inequality gives the manuscript's arithmetic/geometric
mean estimate, including the monotonic extension from actual support size to
its allowed size. This bounds bit-string lengths, not machine workspace.
-/

namespace NtimeDspace.SupportBounds

open SupportEncoding

theorem log_tangent (x a : ℝ) (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ Real.log a + x / a - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt ha)] at h
  linarith

theorem gammaEncode_length_log_bound (gap : ℕ) :
    (gammaEncode gap).length * Real.log 2 ≤ Real.log 2 + 2 * Real.log gap := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.log2_le_logb gap
  rw [Real.logb] at h
  have hf := (le_div_iff₀ hl).mp h
  rw [gammaEncode_length]
  push_cast
  nlinarith

/-- Summed supporting-line inequality for log, before inserting a size budget. -/
theorem encodeGaps_tangent_bound (gaps : List ℕ)
    (positive : ∀ gap ∈ gaps, 0 < gap) (a : ℝ) (ha : 0 < a) :
    (encodeGaps gaps).length * Real.log 2 ≤
      (gaps.length : ℝ) * (Real.log 2 + 2 * Real.log a - 2) +
        2 * (gaps.sum : ℝ) / a := by
  induction gaps with
  | nil => simp [encodeGaps]
  | cons gap gaps ih =>
    have hgap : 0 < gap := positive gap (by simp)
    have htail := ih (fun g hg => positive g (by simp [hg]))
    have ht := log_tangent (gap : ℝ) a (by exact_mod_cast hgap) ha
    have hg := gammaEncode_length_log_bound gap
    simp only [encodeGaps, List.length_append, List.length_cons,
      List.sum_cons, Nat.cast_add, Nat.cast_one] at *
    simp only [mul_add, add_div, mul_div_assoc] at *
    nlinarith

theorem tangent_slope_nonneg (a : ℝ) (ha : 2 ≤ a) :
    0 ≤ Real.log 2 + 2 * Real.log a - 2 := by
  have hm : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num) ha
  have htwo := Real.log_two_gt_d9
  linarith

/-- The exact manuscript bound, allowing a real-valued upper size budget. -/
theorem encodeGaps_length_le_real_budget (gaps : List ℕ)
    (positive : ∀ gap ∈ gaps, 0 < gap) (N q : ℝ)
    (hN : 0 < N) (hq : 0 < q) (half : q ≤ N / 2)
    (count : (gaps.length : ℝ) ≤ q) (total : (gaps.sum : ℝ) ≤ N) :
    (encodeGaps gaps).length ≤ q * (1 + 2 * Real.logb 2 (N / q)) := by
  have ha : 0 < N / q := div_pos hN hq
  have ha2 : 2 ≤ N / q := (le_div_iff₀ hq).mpr (by linarith)
  have hs := tangent_slope_nonneg (N / q) ha2
  have hlen := encodeGaps_tangent_bound gaps positive (N / q) ha
  have hcount := mul_le_mul_of_nonneg_right count hs
  have htotal := div_le_div_of_nonneg_right total (le_of_lt ha)
  have hcancel : N / (N / q) = q := by field_simp
  rw [hcancel] at htotal
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_left₀ hl).mp
  rw [Real.logb]
  have heq : (q * (1 + 2 * (Real.log (N / q) / Real.log 2))) * Real.log 2 =
      q * (Real.log 2 + 2 * Real.log (N / q)) := by
    field_simp
  rw [heq]
  rw [mul_div_assoc] at hlen
  nlinarith

/-- Natural support budgets include q=0, whose only admissible list is empty. -/
theorem encodeGaps_length_le_budget (gaps : List ℕ)
    (positive : ∀ gap ∈ gaps, 0 < gap) (N q : ℕ)
    (half : q ≤ N / 2) (count : gaps.length ≤ q) (total : gaps.sum ≤ N) :
    (encodeGaps gaps).length ≤ (q : ℝ) * (1 + 2 * Real.logb 2 ((N : ℝ) / q)) := by
  by_cases hq : q = 0
  · have hg : gaps = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hq, hg, encodeGaps]
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  apply encodeGaps_length_le_real_budget gaps positive N q
  · have : 0 < N := by omega
    exact_mod_cast this
  · exact_mod_cast hqpos
  · have h : 2 * q ≤ N := by omega
    have hr : (2 : ℝ) * q ≤ N := by exact_mod_cast h
    linarith
  · exact_mod_cast count
  · exact_mod_cast total

/-- The manuscript's explicit maximum code length for support enumeration. -/
noncomputable def supportLimit (N k : ℕ) : ℕ :=
  ⌈(24 : ℝ) * N * (2 * k + 1) / Parameters.s k⌉₊

theorem encodeGaps_length_le_parameter_bound (gaps : List ℕ)
    (positive : ∀ gap ∈ gaps, 0 < gap) (N k : ℕ) (hk : 6 ≤ k)
    (count : gaps.length ≤ Parameters.q N k) (total : gaps.sum ≤ N) :
    (encodeGaps gaps).length ≤
      (24 : ℝ) * N * (2 * k + 1) / Parameters.s k := by
  by_cases hNzero : N = 0
  · have hq : Parameters.q N k = 0 := by simp [hNzero, Parameters.q]
    have hg : gaps = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hg, encodeGaps, hNzero]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hNzero
  have hs : (0 : ℝ) < Parameters.s k := by exact_mod_cast Parameters.s_pos k
  have hs64 : (64 : ℝ) ≤ Parameters.s k := by
    exact_mod_cast Parameters.sixty_four_le_s k hk
  have hcap : (0 : ℝ) < 24 * N / Parameters.s k := div_pos (by positivity) hs
  have hhalf : (24 : ℝ) * N / Parameters.s k ≤ N / 2 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs64 (le_of_lt hN)]
  have hcount : (gaps.length : ℝ) ≤ 24 * N / Parameters.s k := by
    apply (le_div_iff₀ hs).mpr
    have h : gaps.length * Parameters.s k ≤ 24 * N :=
      (Nat.mul_le_mul_right _ count).trans (Parameters.q_mul_s_le N k (by omega))
    exact_mod_cast h
  have htotal : (gaps.sum : ℝ) ≤ N := by exact_mod_cast total
  have hlen := encodeGaps_length_le_real_budget gaps positive N
    (24 * N / Parameters.s k) hN hcap hhalf hcount htotal
  have hratio : (N : ℝ) / (24 * N / Parameters.s k) = Parameters.s k / 24 := by
    field_simp
  rw [hratio] at hlen
  have hlog : Real.logb 2 ((Parameters.s k : ℝ) / 24) ≤ k := by
    have hm := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
      (div_pos hs (by norm_num)) (div_le_self (le_of_lt hs) (by norm_num : (1 : ℝ) ≤ 24))
    have hspow : (Parameters.s k : ℝ) = (2 : ℝ) ^ k := by simp [Parameters.s]
    rw [hspow, Real.logb_pow] at hm
    simpa [hspow] using hm
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hcap)
  have heq : (24 : ℝ) * N * (2 * k + 1) / Parameters.s k =
      (24 * N / Parameters.s k) * (1 + 2 * k) := by ring
  rw [heq]
  nlinarith

theorem encodeGaps_length_le_supportLimit (gaps : List ℕ)
    (positive : ∀ gap ∈ gaps, 0 < gap) (N k : ℕ) (hk : 6 ≤ k)
    (count : gaps.length ≤ Parameters.q N k) (total : gaps.sum ≤ N) :
    (encodeGaps gaps).length ≤ supportLimit N k := by
  have h := encodeGaps_length_le_parameter_bound gaps positive N k hk count total
  have hc := Nat.le_ceil ((24 : ℝ) * N * (2 * k + 1) / Parameters.s k)
  unfold supportLimit
  exact_mod_cast h.trans hc

end NtimeDspace.SupportBounds
