/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.Final
import NtimeDspace.UniformKappa

-- upstream: local-only (quantitative endpoint of the application's simulation)

/-!
# Simultaneous simulation at the paper's analytic rate

`Budget.kappaBudget` is the positive natural rounding of the paper's rate. It
absorbs the finitely many small inputs where the total real logarithm makes
`ParameterAsymptotics.kappa` vanish, and is still `O(κ)` at infinity.

`ntime_kappa_simultaneous_bounds` gives one deterministic machine with time
`2^(C*kappaBudget n)` and space `C*kappaBudget n` for each language in `NTIME(n)`.
The bound is proved from the implemented simulation and the numerical comparison
`Budget.S_isBigO_kappa`; neither is an extra hypothesis. It is a linear-time
simulation endpoint, not the general weighted counting or general-time theorem.
-/

namespace NtimeDspace.Budget

open Filter ParameterAsymptotics

/-- A positive natural resource bound asymptotic to the paper's real rate.
The simulating machine does not need to evaluate this proof-side bound. -/
noncomputable def kappaBudget (n : ℕ) : ℕ := 1 + ⌈kappa n⌉₊

theorem kappaBudget_pos (n : ℕ) : 0 < kappaBudget n := by
  unfold kappaBudget
  omega

theorem kappa_le_kappaBudget (n : ℕ) : kappa n ≤ (kappaBudget n : ℝ) := by
  have h := Nat.le_ceil (kappa n)
  simp only [kappaBudget, Nat.cast_add, Nat.cast_one]
  linarith

private theorem kappa_nonneg (n : ℕ) : 0 ≤ kappa n := by
  unfold kappa
  positivity

private theorem one_le_kappa_eventually : ∀ᶠ n : ℕ in atTop, 1 ≤ kappa n := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [table_term_eventually_le_kappa, hlog.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with n htable hlogn hn
  have hpow : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  nlinarith

/-- Positive rounding changes the rate only by a constant factor eventually. -/
theorem kappaBudget_isBigO_kappa :
    (fun n : ℕ => (kappaBudget n : ℝ)) =O[atTop] kappa := by
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards [one_le_kappa_eventually] with n hn
  have hceil := Nat.ceil_lt_add_one (kappa_nonneg n)
  have hbudget : (kappaBudget n : ℝ) ≤ 3 * kappa n := by
    simp only [kappaBudget, Nat.cast_add, Nat.cast_one]
    linarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (kappaBudget n)),
    abs_of_nonneg (kappa_nonneg n)] using hbudget

/-- The rounded budget is sublinear as a real-valued function. -/
theorem kappaBudget_isLittleO_linear :
    (fun n : ℕ => (kappaBudget n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
  kappaBudget_isBigO_kappa.trans_isLittleO kappa_isLittleO_linear

/-- The complete implemented budget is bounded at every input length by one
constant times the rounded analytic rate. -/
theorem S_le_mul_kappaBudget : ∃ C : ℕ, ∀ n, S n ≤ C * kappaBudget n := by
  obtain ⟨c, hc⟩ := S_isBigO_kappa.bound
  have heventually : ∀ᶠ n : ℕ in atTop, S n ≤ ⌈c⌉₊ * kappaBudget n := by
    filter_upwards [hc] with n hn
    have hn' : (S n : ℝ) ≤ c * kappa n := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (S n)),
        abs_of_nonneg (kappa_nonneg n)] using hn
    have hbound : (S n : ℝ) ≤ (⌈c⌉₊ : ℝ) * (kappaBudget n : ℝ) := by
      calc
        _ ≤ c * kappa n := hn'
        _ ≤ (⌈c⌉₊ : ℝ) * kappa n :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil c) (kappa_nonneg n)
        _ ≤ (⌈c⌉₊ : ℝ) * (kappaBudget n : ℝ) :=
          mul_le_mul_of_nonneg_left (kappa_le_kappaBudget n) (Nat.cast_nonneg _)
    exact_mod_cast hbound
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp heventually
  let Csmall := (Finset.range n0).sup S
  refine ⟨⌈c⌉₊ + Csmall, fun n => ?_⟩
  by_cases hn : n < n0
  · have hsmall : S n ≤ Csmall := Finset.le_sup (Finset.mem_range.mpr hn)
    have hpos := kappaBudget_pos n
    exact hsmall.trans (by nlinarith)
  · exact (hn0 n (by omega)).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

end NtimeDspace.Budget

namespace NtimeDspace

open Budget Cslib.Complexity Turing Turing.MultiTapeTM

/-- Every nondeterministic linear-time language has a single deterministic
decider with simultaneous `2^O(κ(n))` time and `O(κ(n))` space. The displayed
positive rounding makes the bounds valid also at the finite small inputs. -/
theorem ntime_kappa_simultaneous_bounds {A : Set (List Bool)}
    (hA : A ∈ NTIME encBits (fun n => n)) :
    ∃ C, DecidableInTimeAndSpace A encBits
      (fun a => 2 ^ (C * kappaBudget a.length)) (fun a => C * kappaBudget a.length) := by
  obtain ⟨C, hC⟩ := ntime_simultaneous_bounds hA
  obtain ⟨K, hK⟩ := S_le_mul_kappaBudget
  refine ⟨C * K, hC.mono (fun a => ?_) (fun a => ?_)⟩
  · apply Nat.pow_le_pow_right (by norm_num)
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left C (hK a.length)
  · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left C (hK a.length)

/-- Nondeterministic linear time is contained in deterministic space with the
paper's rate, rounded positively at small inputs. -/
theorem ntime_subset_dspace_kappa :
    NTIME encBits (fun n => n) ⊆ DSPACE encBits kappaBudget := by
  intro A hA
  obtain ⟨C, hC⟩ := ntime_kappa_simultaneous_bounds hA
  exact mem_DSPACE_iff.mpr ⟨C, 0, _, hC⟩

end NtimeDspace
