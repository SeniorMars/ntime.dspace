import NtimeDspace.BudgetBasic

/-!
# The decider's values fit the budget

Each quantity the decider computes is below `2^L`: polynomial values in `N`,
the label space `D`, the number of node tuples `(q+1)^Q`, the support codes,
the measurement tuples, the seed range, the schedules, and the machine
constants (given `C0` bounds them).
-/

namespace NtimeDspace.Budget

open Parameters Cslib.Complexity.CountingSimulation ProgTerm

variable {k s c C0 n : ℕ}

theorem lgN_add_three_le_poly : lgN k s c n + 3 ≤ polyPart k s c C0 n := by
  unfold polyPart
  have h1 : lgN k s c n + 3 ≤ (lgN k s c n + 3) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h2 : (lgN k s c n + 3) ^ 3 ≤ (C0 + 8) * (lgN k s c n + 3) ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem cube_le_poly : 3 * (lgN k s c n + 1) + 1 ≤ polyPart k s c C0 n := by
  unfold polyPart
  have h1 : 3 * (lgN k s c n + 1) + 1 ≤ (lgN k s c n + 3) ^ 3 := by
    have h9 : 3 ^ 2 ≤ (lgN k s c n + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : (lgN k s c n + 3) ^ 3 = (lgN k s c n + 3) ^ 2 * (lgN k s c n + 3) := by ring
    nlinarith
  have h2 : (lgN k s c n + 3) ^ 3 ≤ (C0 + 8) * (lgN k s c n + 3) ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem poly_le_L : polyPart k s c C0 n ≤ L k s c C0 n := by rw [L_eq]; omega

/-- `N³ + 1 < 2^L`. -/
theorem N_cube_lt : NN k s c n ^ 3 + 1 < 2 ^ L k s c C0 n := by
  have h := Nat.lt_log2_self (n := NN k s c n)
  have h3 : NN k s c n ^ 3 < 2 ^ (3 * (lgN k s c n + 1)) := by
    rw [pow_mul']; exact Nat.pow_lt_pow_left h (by norm_num)
  have hL : 3 * (lgN k s c n + 1) + 1 ≤ L k s c C0 n := cube_le_poly.trans poly_le_L
  calc NN k s c n ^ 3 + 1 ≤ 2 ^ (3 * (lgN k s c n + 1)) := h3
    _ < 2 ^ (3 * (lgN k s c n + 1) + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ L k s c C0 n := Nat.pow_le_pow_right (by norm_num) hL

/-- Anything at most `N³` is below `2^L`. -/
theorem lt_of_le_cube {x : ℕ} (hx : x ≤ NN k s c n ^ 3) : x < 2 ^ L k s c C0 n := by
  have := N_cube_lt (k := k) (s := s) (c := c) (C0 := C0) (n := n); omega

/-- The label space `D = s^{2Q}` is below `2^L`. -/
theorem D_lt : D (kN k s c n) < 2 ^ L k s c C0 n := by
  have hadm := ParameterChoice.admissible (NN k s c n)
  unfold ParameterChoice.cost at hadm
  have hD : D (kN k s c n) < 2 ^ (2 * Parameters.s (kN k s c n) ^ 2 * kN k s c n ^ 2 + 1) := by
    rw [D_binary]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hle : 2 * Parameters.s (kN k s c n) ^ 2 * kN k s c n ^ 2 + 1 ≤ L k s c C0 n := by
    have : 2 * Parameters.s (kN k s c n) ^ 2 * kN k s c n ^ 2 ≤ lgN k s c n := by
      have : 2 * Parameters.s (kN k s c n) ^ 2 * kN k s c n ^ 2 ≤ 16 * Parameters.s (kN k s c n) ^ 2 * kN k s c n ^ 2 := by
        nlinarith
      exact this.trans hadm
    have := lgN_add_three_le_poly (k := k) (s := s) (c := c) (C0 := C0) (n := n)
    have := poly_le_L (k := k) (s := s) (c := c) (C0 := C0) (n := n)
    omega
  exact hD.trans_le (Nat.pow_le_pow_right (by norm_num) hle)

/-- The selected `k` and `2^k` are below `2^L`. -/
theorem kN_lt_L : kN k s c n < L k s c C0 n := by
  have : kN k s c n ≤ lgN k s c n := ParameterChoice.selected_le_log2 (NN k s c n)
  have := lgN_add_three_le_poly (k := k) (s := s) (c := c) (C0 := C0) (n := n)
  have := poly_le_L (k := k) (s := s) (c := c) (C0 := C0) (n := n)
  omega

theorem two_pow_kN_lt : 2 ^ kN k s c n < 2 ^ L k s c C0 n :=
  Nat.pow_lt_pow_right (by norm_num) kN_lt_L

/-- The support codes: `limit + 1 < L`. -/
theorem limit_lt_L : SupportBudget.limit (NN k s c n) (kN k s c n) + 1 < L k s c C0 n := by
  unfold L
  generalize tupleWidth k s c n * ((2 * D (kN k s c n) + 1).log2 + 1) = X
  generalize 2 * (k + 1) * numBlocks (tN c n) = Y
  generalize 2 * NN k s c n / Parameters.s (kN k s c n) = Z
  omega

/-- The measurement tuples: `W·(log₂(2D+1)+1) ≤ L`. -/
theorem tuple_le_L : tupleWidth k s c n * ((2 * D (kN k s c n) + 1).log2 + 1) ≤ L k s c C0 n := by
  unfold L
  generalize tupleWidth k s c n * ((2 * D (kN k s c n) + 1).log2 + 1) = X
  generalize 2 * (k + 1) * numBlocks (tN c n) = Y
  generalize 2 * NN k s c n / Parameters.s (kN k s c n) = Z
  omega

/-- The group sizes: `2N/2^k < L`. -/
theorem group_lt_L : 2 * NN k s c n / Parameters.s (kN k s c n) < L k s c C0 n := by
  unfold L
  generalize tupleWidth k s c n * ((2 * D (kN k s c n) + 1).log2 + 1) = X
  generalize 2 * (k + 1) * numBlocks (tN c n) = Y
  generalize 2 * NN k s c n / Parameters.s (kN k s c n) = Z
  omega

/-- The schedules: `3^((k+1)·numBlocks) < 2^L`. -/
theorem schedules_lt : 3 ^ ((k + 1) * numBlocks (tN c n)) < 2 ^ L k s c C0 n := by
  have h : 3 ^ ((k + 1) * numBlocks (tN c n)) ≤ 2 ^ (2 * ((k + 1) * numBlocks (tN c n))) := by
    calc 3 ^ ((k + 1) * numBlocks (tN c n)) ≤ 4 ^ ((k + 1) * numBlocks (tN c n)) :=
          Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (2 * ((k + 1) * numBlocks (tN c n))) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hle : 2 * ((k + 1) * numBlocks (tN c n)) < L k s c C0 n := by
    unfold L
    generalize tupleWidth k s c n * ((2 * D (kN k s c n) + 1).log2 + 1) = X
    have e : 2 * ((k + 1) * numBlocks (tN c n)) = 2 * (k + 1) * numBlocks (tN c n) := by ring
    rw [e]
    generalize 2 * (k + 1) * numBlocks (tN c n) = Y
    generalize 2 * NN k s c n / Parameters.s (kN k s c n) = Z
    omega
  exact h.trans_lt (Nat.pow_lt_pow_right (by norm_num) hle)

/-- Machine constants below `2^C0` are below `2^L`. -/
theorem const_lt {x : ℕ} (hx : x < 2 ^ C0) : x < 2 ^ L k s c C0 n :=
  hx.trans_le (Nat.pow_le_pow_right (by norm_num) (by have := C0_le_L k s c C0 n; omega))

end NtimeDspace.Budget
