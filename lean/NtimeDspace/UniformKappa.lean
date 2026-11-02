/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.UniformSpace

-- upstream: local-only (comparison of the application's uniform space budget)

/-!
# The uniform space bound has the paper's analytic rate

`S_eventually_le_parameter_term` bounds all three summands of `Budget.S` by
four times the selected parameter term `n * choose n / s (choose n)`.
`S_isBigO_kappa` then compares the complete discrete budget with the paper's
natural-logarithm rate, using `ParameterAsymptotics.parameter_term_isBigO`.

These are numerical comparisons of the existing budget. Machine-level
consequences use the separately proved simulation in space `S`.
-/

namespace NtimeDspace.Budget

open Filter Parameters ParameterChoice

private theorem S_mul_s_le (n : ℕ) (positive : 0 < choose n)
    (polylog : (n.log2 + 1) ^ 5 ≤ n) :
    S n * s (choose n) ≤ 4 * n * choose n := by
  let k := choose n
  let l := n.log2 + 1
  have hk : 1 ≤ k := positive
  have hs : s k ≤ l :=
    ((s_le_R k positive).trans (R_le_log2 n k positive (admissible n))).trans
      (Nat.le_succ _)
  have hn : n ≤ n * k := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hk
  have hfirst : (n * (k + 1) / s k) * s k ≤ 2 * (n * k) := by
    calc
      _ ≤ n * (k + 1) := Nat.div_mul_le_self _ _
      _ ≤ n * (2 * k) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (n * k) := by ring
  have hsecond : (n / l) * s k ≤ n * k := by
    calc
      _ ≤ (n / l) * l := Nat.mul_le_mul_left _ hs
      _ ≤ n := Nat.div_mul_le_self _ _
      _ ≤ n * k := hn
  have hthird : l ^ 4 * s k ≤ n * k := by
    calc
      _ ≤ l ^ 4 * l := Nat.mul_le_mul_left _ hs
      _ = l ^ 5 := by ring
      _ ≤ n := polylog
      _ ≤ n * k := hn
  calc
    S n * s k = (n * (k + 1) / s k) * s k + (n / l) * s k + l ^ 4 * s k := by
      dsimp only [S, k, l]
      ring
    _ ≤ 2 * (n * k) + n * k + n * k :=
      Nat.add_le_add (Nat.add_le_add hfirst hsecond) hthird
    _ = 4 * n * k := by ring

/-- The schedule and polylogarithmic summands are absorbed by the same
parameter term as the leading support budget. -/
theorem S_eventually_le_parameter_term :
    ∀ᶠ n : ℕ in atTop,
      (S n : ℝ) ≤ 4 * ((n : ℝ) * choose n / s (choose n)) := by
  filter_upwards [ParameterAsymptotics.selected_eventually_positive,
    Polylog.eventually_polylog_le 1 5] with n hk hpolylog
  have hpolylog' : (n.log2 + 1) ^ 5 ≤ n := by
    simpa only [one_mul] using hpolylog
  have hbound := S_mul_s_le n hk hpolylog'
  have hs : (0 : ℝ) < s (choose n) := by exact_mod_cast s_pos (choose n)
  rw [← mul_div_assoc, le_div_iff₀ hs]
  have hreal : (S n : ℝ) * s (choose n) ≤ 4 * (n : ℝ) * choose n := by
    exact_mod_cast hbound
  simpa only [mul_assoc] using hreal

/-- The complete uniform space bound, including schedules and polynomial
logarithmic overhead, is `O(n (log log n)² / sqrt (log n))`. -/
theorem S_isBigO_kappa :
    (fun n : ℕ => (S n : ℝ)) =O[atTop] ParameterAsymptotics.kappa := by
  have hparameter : (fun n : ℕ => (S n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * choose n / s (choose n)) := by
    apply Asymptotics.IsBigO.of_bound 4
    filter_upwards [S_eventually_le_parameter_term] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (S n)),
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) * choose n / s (choose n))] using hn
  exact hparameter.trans ParameterAsymptotics.parameter_term_isBigO

end NtimeDspace.Budget
