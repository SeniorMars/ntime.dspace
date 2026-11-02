import NtimeDspace.Domination

/-!
# Basic facts about the budget

The budget is at least `log₂ n + 1` and at least `C0 + 8`, and it grows with
`C0`. These are the side conditions of `decidable_of_prog_len`.
-/

namespace NtimeDspace.Budget

open Parameters Cslib.Complexity.CountingSimulation ProgTerm

theorem log2_le_lgN (k s c n : ℕ) (hc : 1 ≤ c) : n.log2 ≤ lgN k s c n := by
  apply log2_mono
  have : n ≤ clk c n := by unfold clk; nlinarith
  exact this.trans ((le_paddedTime _).trans (paddedTime_le_edgesN k s _))

theorem log2_add_one_le_L (k s c C0 n : ℕ) (hc : 1 ≤ c) : n.log2 + 1 ≤ L k s c C0 n := by
  have h := log2_le_lgN k s c n hc
  rw [L_eq]
  have : lgN k s c n + 3 ≤ polyPart k s c C0 n := by
    unfold polyPart
    have h1 : lgN k s c n + 3 ≤ (lgN k s c n + 3) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h2 : (lgN k s c n + 3) ^ 3 ≤ (C0 + 8) * (lgN k s c n + 3) ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  omega

theorem C0_le_L (k s c C0 n : ℕ) : C0 + 8 ≤ L k s c C0 n := by
  rw [L_eq]; omega

theorem L_mono_C0 (k s c n : ℕ) {C0 C1 : ℕ} (h : C0 ≤ C1) : L k s c C0 n ≤ L k s c C1 n := by
  rw [L_eq, L_eq]
  have : polyPart k s c C0 n ≤ polyPart k s c C1 n := by unfold polyPart; gcongr
  omega

theorem lt_two_pow_L (k s c C0 n : ℕ) (hc : 1 ≤ c) : n < 2 ^ L k s c C0 n :=
  Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by norm_num) (log2_add_one_le_L k s c C0 n hc))

end NtimeDspace.Budget
