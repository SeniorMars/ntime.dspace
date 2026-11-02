import NtimeDspace.BudgetAsymptotics

/-!
# A uniform sublinear space function

`S n = n·(k+1)/s(k) + n/(log₂ n + 1) + (log₂ n + 1)⁴` with `k = choose n`.
`S_sublinear`: `c·S n + c ≤ n` eventually, for every `c`. Every decider budget
is `O(S)` (`Final`), so `NTIME(n) ⊆ DSPACE(S)`.
-/

namespace NtimeDspace.Budget

open Parameters Filter

/-- The uniform space function. -/
def S (n : ℕ) : ℕ :=
  n * (ParameterChoice.choose n + 1) / s (ParameterChoice.choose n) + n / (n.log2 + 1) +
    (n.log2 + 1) ^ 4

theorem S_first_eventually (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, m * (n * (ParameterChoice.choose n + 1) / s (ParameterChoice.choose n)) ≤ n := by
  have hε : (0 : ℝ) < 1 / (4 * (m + 1)) := by positivity
  filter_upwards [paramTerm_littleO.def hε, ParameterAsymptotics.selected_eventually_positive]
    with n h hk
  simp only [Real.norm_eq_abs] at h
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h
  set kk := ParameterChoice.choose n
  have hs : (0 : ℝ) < s kk := by exact_mod_cast s_pos kk
  have hk1 : (1 : ℝ) ≤ kk := by exact_mod_cast hk
  have h1 : ((n * (kk + 1) / s kk : ℕ) : ℝ) ≤ 2 * ((n : ℝ) * kk / s kk) := by
    calc ((n * (kk + 1) / s kk : ℕ) : ℝ) ≤ (n * (kk + 1) : ℝ) / s kk := by exact_mod_cast Nat.cast_div_le
      _ ≤ 2 * ((n : ℝ) * kk / s kk) := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hs]
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have key : (m : ℝ) * ((n * (kk + 1) / s kk : ℕ) : ℝ) ≤ n := by
    calc (m : ℝ) * ((n * (kk + 1) / s kk : ℕ) : ℝ) ≤ (m + 1) * (2 * (1 / (4 * (m + 1)) * n)) := by
          gcongr
          · linarith
          · linarith
      _ = n / 2 := by field_simp; ring
      _ ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) n]
  exact_mod_cast key

theorem S_second_eventually (m : ℕ) : ∀ᶠ n : ℕ in atTop, m * (n / (n.log2 + 1)) ≤ n / 4 + 1 := by
  filter_upwards [Polylog.tendsto_log2.eventually (eventually_ge_atTop (4 * m))] with n hn
  have h1 : m * (n / (n.log2 + 1)) * 4 ≤ n := by
    calc m * (n / (n.log2 + 1)) * 4 = (n / (n.log2 + 1)) * (4 * m) := by ring
      _ ≤ (n / (n.log2 + 1)) * (n.log2 + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ n := Nat.div_mul_le_self _ _
  omega

theorem S_sublinear (c : ℕ) : ∀ᶠ n in atTop, c * S n + c ≤ n := by
  filter_upwards [S_first_eventually (4 * c), S_second_eventually (4 * c),
    Polylog.eventually_polylog_le (4 * c + 1) 4, eventually_ge_atTop (16 * c + 16)]
    with n h1 h2 h3 h4
  have h3' : 4 * c * (n.log2 + 1) ^ 4 ≤ n := by
    calc 4 * c * (n.log2 + 1) ^ 4 ≤ (4 * c + 1) ^ 4 * (n.log2 + 1) ^ 4 := by
          gcongr
          calc 4 * c ≤ 4 * c + 1 := by omega
            _ = (4 * c + 1) ^ 1 := by ring
            _ ≤ (4 * c + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = ((4 * c + 1) * (n.log2 + 1)) ^ 4 := by ring
      _ ≤ n := h3
  unfold S
  have e : c * (n * (ParameterChoice.choose n + 1) / s (ParameterChoice.choose n) + n / (n.log2 + 1) +
      (n.log2 + 1) ^ 4) * 4 = 4 * c * (n * (ParameterChoice.choose n + 1) / s (ParameterChoice.choose n)) +
      4 * c * (n / (n.log2 + 1)) + 4 * c * (n.log2 + 1) ^ 4 := by ring
  have : c * (n * (ParameterChoice.choose n + 1) / s (ParameterChoice.choose n) + n / (n.log2 + 1) +
      (n.log2 + 1) ^ 4) * 4 ≤ n + (n / 4 + 1) + n := by omega
  omega

end NtimeDspace.Budget
