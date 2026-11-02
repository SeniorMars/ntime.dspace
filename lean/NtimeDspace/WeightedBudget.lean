/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.Domination
import NtimeDspace.UniformKappa

-- upstream: local-only (budget for the application's weighted counter)

/-!
# A budget for weighted constraint systems

`L A N` allows polynomial logarithmic overhead, the support code, measurement
tuples for at most three incidences per variable, and one group assignment.
`L_isBigO_kappa` compares this discrete budget with the paper's rate. The
parameter `A` accounts for fixed polynomial bounds on the input encoding.

These are numerical bounds. They do not by themselves construct a counting
machine or supply its input-access routines.
-/

namespace NtimeDspace.WeightedBudget

open Filter Parameters

/-- Twice the earlier counting buffers accommodates three incidences per variable. -/
noncomputable def L (A N : ℕ) : ℕ :=
  (A + 16) * (N.log2 + 3) ^ 3 + 2 * Budget.Gpart N + 16

theorem eight_le_L (A N : ℕ) : 8 ≤ L A N := by
  unfold L
  omega

theorem poly_le_L (A N : ℕ) : (A + 16) * (N.log2 + 3) ^ 3 ≤ L A N := by
  unfold L
  omega

theorem counting_lt_L (A N : ℕ) : 2 * Budget.Gpart N < L A N := by
  unfold L
  omega

theorem support_lt_L (A N : ℕ) :
    SupportBudget.limit N (ParameterChoice.choose N) + 1 < L A N := by
  have h : SupportBudget.limit N (ParameterChoice.choose N) + 1 ≤ Budget.Gpart N :=
    (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  exact lt_of_le_of_lt (h.trans (Nat.le_mul_of_pos_left _ (by omega))) (counting_lt_L A N)

theorem group_lt_L (A N : ℕ) :
    2 * N / s (ParameterChoice.choose N) < L A N := by
  have h : 2 * N / s (ParameterChoice.choose N) + 1 ≤ Budget.Gpart N := Nat.le_add_left _ _
  exact lt_of_le_of_lt ((Nat.le_succ _).trans
    (h.trans (Nat.le_mul_of_pos_left _ (by omega)))) (counting_lt_L A N)

/-- The larger incidence bound needs at most twice the old number of copies. -/
theorem copies_le_double {M N D : ℕ} (hM : M ≤ 3 * N) (hD : D ≤ N) :
    2 * M / D ≤ 2 * (2 * (2 * N) / D) := by
  rcases Nat.eq_zero_or_pos D with rfl | hpos
  · simp
  have hfloor := Nat.lt_div_mul_add (a := 4 * N) (b := D) hpos
  have hmul : 2 * M < (2 * (4 * N / D)) * D := by nlinarith
  have hquot : 2 * M / D < 2 * (4 * N / D) :=
    (Nat.div_lt_iff_lt_mul hpos).mpr hmul
  simpa only [show 2 * (2 * N) = 4 * N by ring] using hquot.le

/-- Measurement coordinates times their digit width fit in the same budget. -/
theorem measurement_le_L (A N M : ℕ) (hM : M ≤ 3 * N)
    (hD : D (ParameterChoice.choose N) ≤ N) :
    (s (ParameterChoice.choose N) * (2 * M / D (ParameterChoice.choose N)) *
      TailParameters.badCount (ParameterChoice.choose N)) *
      ((2 * D (ParameterChoice.choose N) + 1).log2 + 1) ≤ L A N := by
  have hc := copies_le_double hM hD
  have hwidth := Nat.mul_le_mul_right
    ((2 * D (ParameterChoice.choose N) + 1).log2 + 1)
    (Nat.mul_le_mul_right (TailParameters.badCount (ParameterChoice.choose N))
      (Nat.mul_le_mul_left (s (ParameterChoice.choose N)) hc))
  have hm : (s (ParameterChoice.choose N) * (2 * (2 * N) / D (ParameterChoice.choose N)) *
      TailParameters.badCount (ParameterChoice.choose N)) *
      ((2 * D (ParameterChoice.choose N) + 1).log2 + 1) ≤ Budget.Gpart N :=
    (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  calc
    _ ≤ 2 * ((s (ParameterChoice.choose N) * (2 * (2 * N) / D (ParameterChoice.choose N)) *
        TailParameters.badCount (ParameterChoice.choose N)) *
        ((2 * D (ParameterChoice.choose N) + 1).log2 + 1)) := by
      convert hwidth using 1; ring
    _ ≤ 2 * Budget.Gpart N := Nat.mul_le_mul_left _ hm
    _ ≤ L A N := (counting_lt_L A N).le

theorem L_le_S (A N : ℕ) (hk : 0 < ParameterChoice.choose N) :
    L A N ≤ (27 * (A + 16) + 822) * Budget.S N := by
  have hS1 : 1 ≤ Budget.S N := by
    have hpow : 1 ≤ (N.log2 + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact hpow.trans (Nat.le_add_left _ _)
  have hfirst : N * (ParameterChoice.choose N + 1) / s (ParameterChoice.choose N) ≤
      Budget.S N := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have hpoly : (N.log2 + 1) ^ 4 ≤ Budget.S N := Nat.le_add_left _ _
  have hcube : (N.log2 + 3) ^ 3 ≤ 27 * Budget.S N := by
    calc
      _ ≤ (3 * (N.log2 + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) _
      _ = 27 * (N.log2 + 1) ^ 3 := by ring
      _ ≤ 27 * (N.log2 + 1) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ _ := Nat.mul_le_mul_left _ hpoly
  have hG := Budget.Gpart_le_S 1 N (by omega) N le_rfl (by omega) hk
  unfold L
  nlinarith

/-- The full weighted-counter budget has the paper's analytic rate. -/
theorem L_isBigO_kappa (A : ℕ) :
    (fun N : ℕ => (L A N : ℝ)) =O[atTop] ParameterAsymptotics.kappa := by
  have hS : (fun N : ℕ => (L A N : ℝ)) =O[atTop] (fun N => (Budget.S N : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound (27 * (A + 16) + 822 : ℝ)
    filter_upwards [ParameterAsymptotics.selected_eventually_positive] with N hN
    have h := L_le_S A N hN
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (L A N)),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Budget.S N))] using
      (show (L A N : ℝ) ≤ (27 * (A + 16) + 822 : ℝ) * Budget.S N by exact_mod_cast h)
  exact hS.trans Budget.S_isBigO_kappa

end NtimeDspace.WeightedBudget
