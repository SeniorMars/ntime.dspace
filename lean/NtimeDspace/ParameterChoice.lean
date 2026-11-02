import NtimeDspace.Parameters
import Mathlib.Data.Nat.Find

/-!
The largest growing parameter is a concrete bounded search. Small inputs select
zero; once the k=6 budget is available, the selected value satisfies exactly
the manuscript's admissibility and maximality requirements. The search's
machine workspace and eventual real-logarithm estimates are separate.
-/

namespace NtimeDspace.ParameterChoice

open Parameters

def cost (k : ℕ) : ℕ := 16 * s k ^ 2 * k ^ 2

def choose (N : ℕ) : ℕ := Nat.findGreatest (fun k => cost k ≤ N.log2) N.log2

theorem le_cost (k : ℕ) : k ≤ cost k := by
  have hk : k ≤ k ^ 2 := by nlinarith
  have hspos := s_pos k
  have hs : 0 < 16 * s k ^ 2 := by positivity
  exact hk.trans (Nat.le_mul_of_pos_left _ hs)

theorem admissible (N : ℕ) : cost (choose N) ≤ N.log2 := by
  unfold choose
  exact Nat.findGreatest_spec (P := fun k => cost k ≤ N.log2)
    (m := 0) (Nat.zero_le _) (by simp [cost])

theorem selected_le_log2 (N : ℕ) : choose N ≤ N.log2 := Nat.findGreatest_le _

theorem maximal (N k : ℕ) (budget : cost k ≤ N.log2) : k ≤ choose N :=
  Nat.le_findGreatest ((le_cost k).trans budget) budget

theorem six_le_selected (N : ℕ) (large : cost 6 ≤ N.log2) : 6 ≤ choose N :=
  maximal N 6 large

theorem next_inadmissible (N : ℕ) : N.log2 < cost (choose N + 1) := by
  by_contra h
  have contradiction := maximal N (choose N + 1) (Nat.le_of_not_gt h)
  omega

/-- The next search cost is bounded by sixteen times the present cost after
the initial zero case. Together with maximality this brackets log₂N. -/
theorem next_cost_le (k : ℕ) (positive : 0 < k) : cost (k + 1) ≤ 16 * cost k := by
  have h : (k + 1) ^ 2 ≤ 4 * k ^ 2 := by nlinarith
  have hs : s (k + 1) = 2 * s k := by simp [s, pow_succ, Nat.mul_comm]
  unfold cost
  rw [hs]
  nlinarith

theorem log2_lt_sixteen_cost (N : ℕ) (positive : 0 < choose N) :
    N.log2 < 16 * cost (choose N) :=
  (next_inadmissible N).trans_le (next_cost_le (choose N) positive)

end NtimeDspace.ParameterChoice
