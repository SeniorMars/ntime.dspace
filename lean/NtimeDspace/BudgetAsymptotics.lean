import NtimeDspace.Budget
import NtimeDspace.ParameterAsymptotics
import NtimeDspace.Polylog
import NtimeDspace.MainCorrect

/-!
# The budget is sublinear

`L_sublinear`: for every `c'`, eventually `c' · L(n) + c' ≤ n`. The support
budget, the measurement tuples and the group sizes are `O(N·k/s) = o(N)`
(`ParameterAsymptotics`), the polylogarithmic part is `o(N)`, the schedule
part is `O(t / log t)`, and `N ≤ K·(n + 1)`.
-/

namespace NtimeDspace.Budget

open Parameters Cslib.Complexity.CountingSimulation ProgTerm Filter

/-- The part of the budget that depends on `N` only. -/
noncomputable def Gpart (N : ℕ) : ℕ :=
  (SupportBudget.limit N (ParameterChoice.choose N) + 1) +
    (s (ParameterChoice.choose N) * (2 * (2 * N) / D (ParameterChoice.choose N)) *
      TailParameters.badCount (ParameterChoice.choose N)) *
      ((2 * D (ParameterChoice.choose N) + 1).log2 + 1) +
    (2 * N / s (ParameterChoice.choose N) + 1)

/-- `N·k/s` bounds the `N`-only part up to a constant, for `k ≥ 1`. -/
theorem Gpart_le (N : ℕ) (hk : 0 < ParameterChoice.choose N) :
    (Gpart N : ℝ) ≤ 100 * ((N : ℝ) * ParameterChoice.choose N / s (ParameterChoice.choose N)) + 3 := by
  set kk := ParameterChoice.choose N
  have hs : (0 : ℝ) < s kk := by exact_mod_cast s_pos kk
  have hk1 : (1 : ℝ) ≤ kk := by exact_mod_cast hk
  have hlim := ParameterAsymptotics.support_limit_le_parameter_term N hk
  rw [← SupportBudget.limit_eq_supportLimit] at hlim
  -- measurement tuples
  have hD : 0 < D kk := by unfold D; exact pow_pos (s_pos kk) _
  have hBC := TailParameters.badCount_scaled kk hk
  have hW : ((s kk * (2 * (2 * N) / D kk) * TailParameters.badCount kk : ℕ) : ℝ) ≤
      4 * (N : ℝ) / (3 * (s kk : ℝ) ^ 4) := by
    have h1 : ((2 * (2 * N) / D kk : ℕ) : ℝ) ≤ 4 * N / D kk := by
      rw [show 2 * (2 * N) = 4 * N by ring]
      exact_mod_cast Nat.cast_div_le
    have h2 : (3 * (s kk : ℝ) ^ 5) * TailParameters.badCount kk ≤ D kk := by exact_mod_cast hBC
    have hDr : (0 : ℝ) < D kk := by exact_mod_cast hD
    push_cast
    rw [le_div_iff₀ (by positivity)]
    calc (s kk : ℝ) * ((2 * (2 * N) / D kk : ℕ) : ℝ) * TailParameters.badCount kk * (3 * (s kk : ℝ) ^ 4)
        ≤ (s kk : ℝ) * (4 * N / D kk) * TailParameters.badCount kk * (3 * (s kk : ℝ) ^ 4) := by
          gcongr
      _ = 4 * N / D kk * ((3 * (s kk : ℝ) ^ 5) * TailParameters.badCount kk) := by ring
      _ ≤ 4 * N / D kk * D kk := by gcongr
      _ = 4 * N := by field_simp
  have hlogD : (((2 * D kk + 1).log2 + 1 : ℕ) : ℝ) ≤ 5 * (s kk : ℝ) ^ 2 * kk ^ 2 := by
    have h1 : (2 * D kk + 1).log2 ≤ (D kk).log2 + 2 := by
      have hlt : 2 * D kk + 1 < 2 ^ ((D kk).log2 + 3) := by
        have := Nat.lt_log2_self (n := D kk)
        rw [pow_succ, pow_succ] at *; omega
      have := (Nat.log2_lt (by omega)).mpr hlt
      omega
    rw [D_log2] at h1
    have hs1 : (1 : ℝ) ≤ s kk := by exact_mod_cast s_pos kk
    have : ((2 * D kk + 1).log2 + 1 : ℕ) ≤ 2 * s kk ^ 2 * kk ^ 2 + 3 := by omega
    have hr : (((2 * D kk + 1).log2 + 1 : ℕ) : ℝ) ≤ 2 * (s kk : ℝ) ^ 2 * kk ^ 2 + 3 := by
      exact_mod_cast this
    have h1sk : (1 : ℝ) ≤ (s kk : ℝ) ^ 2 * kk ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hs1) (one_le_pow₀ hk1)
    linarith
  have hks : (kk : ℝ) ≤ s kk := by
    exact_mod_cast (Nat.lt_two_pow_self (n := kk)).le
  have hterm : 4 * (N : ℝ) / (3 * (s kk : ℝ) ^ 4) * (5 * (s kk : ℝ) ^ 2 * kk ^ 2) ≤
      7 * ((N : ℝ) * kk / s kk) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [show 7 * ((N : ℝ) * kk / s kk) * (3 * (s kk : ℝ) ^ 4) = 21 * N * kk * s kk ^ 3 by
      field_simp; ring]
    have h : 20 * (s kk : ℝ) ^ 2 * kk ^ 2 ≤ 21 * kk * s kk ^ 3 := by
      have h0 : 0 ≤ (s kk : ℝ) ^ 2 * kk := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hks h0]
    nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) N)]
  have hgroup : ((2 * N / s kk : ℕ) : ℝ) ≤ 2 * ((N : ℝ) * kk / s kk) := by
    calc ((2 * N / s kk : ℕ) : ℝ) ≤ (2 * N : ℝ) / s kk := by exact_mod_cast Nat.cast_div_le
      _ ≤ 2 * ((N : ℝ) * kk / s kk) := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hs]
          nlinarith [Nat.cast_nonneg (α := ℝ) N]
  unfold Gpart
  push_cast
  have hWl : ((s kk * (2 * (2 * N) / D kk) * TailParameters.badCount kk : ℕ) : ℝ) *
      (((2 * D kk + 1).log2 + 1 : ℕ) : ℝ) ≤ 7 * ((N : ℝ) * kk / s kk) := by
    refine le_trans ?_ hterm
    exact mul_le_mul hW hlogD (by positivity) (by positivity)
  push_cast at hWl hgroup hlim
  nlinarith

theorem paramTerm_littleO :
    (fun N : ℕ => (N : ℝ) * ParameterChoice.choose N / s (ParameterChoice.choose N)) =o[atTop]
      (fun N : ℕ => (N : ℝ)) :=
  ParameterAsymptotics.parameter_term_isBigO.trans_isLittleO
    ParameterAsymptotics.kappa_isLittleO_linear

/-- The `N`-only part is `o(N)`. -/
theorem Gpart_eventually (m : ℕ) : ∀ᶠ N : ℕ in atTop, m * Gpart N ≤ N := by
  have hε : (0 : ℝ) < 1 / (200 * (m + 1)) := by positivity
  filter_upwards [paramTerm_littleO.def hε, ParameterAsymptotics.selected_eventually_positive,
    eventually_ge_atTop (6 * (m + 1))] with N h hk hN
  have hG := Gpart_le N hk
  simp only [Real.norm_eq_abs] at h
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h
  have hNr : (6 * (m + 1) : ℝ) ≤ N := by exact_mod_cast hN
  have key : (m : ℝ) * Gpart N ≤ N := by
    have hm : (m : ℝ) ≤ m + 1 := by linarith
    calc (m : ℝ) * Gpart N ≤ (m + 1) * (100 * (1 / (200 * (m + 1)) * N) + 3) := by
          gcongr
          linarith
      _ = N / 2 + 3 * (m + 1) := by field_simp; ring
      _ ≤ N := by linarith
  exact_mod_cast key

/-- The block length is at most `log₂ N + 2`. -/
theorem blockLength_le (k s t : ℕ) (ht : 2 ≤ t) :
    blockLength t ≤ (edgesN k s t).log2 + 2 := by
  have hN : t ≤ edgesN k s t := (le_paddedTime t).trans (ProgTerm.paddedTime_le_edgesN k s t)
  unfold blockLength
  have hpos : edgesN k s t ≠ 0 := by omega
  have h2 : t + 2 ≤ 2 ^ ((edgesN k s t).log2 + 2) := by
    have := Nat.lt_log2_self (n := edgesN k s t)
    rw [pow_succ]; omega
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr h2

theorem blockLength_le_self (t : ℕ) (ht : 2 ≤ t) : blockLength t ≤ t := by
  unfold blockLength
  refine (Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem numBlocks_mul_le (t : ℕ) : numBlocks t * blockLength t ≤ t + blockLength t := by
  unfold numBlocks
  rw [Nat.ceilDiv_eq_add_pred_div]
  have := Nat.div_mul_le_self (t + blockLength t - 1) (blockLength t)
  omega

/-- `N ≤ K·(n + 1)` with `K = 4(3k+1)(s+k+4)c`. -/
theorem edgesN_le (k s c n : ℕ) (hc : 2 ≤ c) :
    edgesN k s (clk c n) ≤ 4 * (3 * k + 1) * (s + k + 4) * c * (n + 1) := by
  have ht : 2 ≤ clk c n := by unfold clk; nlinarith
  have h1 := numBlocks_mul_le (clk c n)
  have h2 := blockLength_le_self (clk c n) ht
  have h3 : numBlocks (clk c n) * blockLength (clk c n) ≤ 2 * clk c n := by omega
  unfold edgesN Turing.MultiTapePTM.letterBits
  have e : 2 * (numBlocks (clk c n) * (3 * k + 1) * ((s + k + 4) * blockLength (clk c n))) =
      2 * (3 * k + 1) * (s + k + 4) * (numBlocks (clk c n) * blockLength (clk c n)) := by ring
  rw [e]
  have e2 : 4 * (3 * k + 1) * (s + k + 4) * c * (n + 1) = 2 * (3 * k + 1) * (s + k + 4) * (2 * clk c n) := by
    unfold clk; ring
  rw [e2]
  exact Nat.mul_le_mul_left _ h3

/-- The polylogarithmic part, in terms of `N`. -/
theorem polyPart_le (k s c C0 n : ℕ) (hc : 2 ≤ c) :
    polyPart k s c C0 n ≤ (27 * (C0 + 8) + 24 * (C0 + 1) * (C0 + 3)) * (lgN k s c n + 1) ^ 3 := by
  have ht : 2 ≤ clk c n := by unfold clk; nlinarith
  unfold polyPart
  set g := lgN k s c n
  have hb : bN c n ≤ g + 2 := blockLength_le k s (clk c n) ht
  have hb' : bN c n + 1 ≤ 3 * (g + 1) := by omega
  have h1 : (g + 3) ^ 3 ≤ 27 * (g + 1) ^ 3 := by
    have : g + 3 ≤ 3 * (g + 1) := by omega
    calc (g + 3) ^ 3 ≤ (3 * (g + 1)) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 27 * (g + 1) ^ 3 := by ring
  have h2 : g + C0 + 3 ≤ (C0 + 3) * (g + 1) := by nlinarith
  have h3 : 8 * (bN c n + 1) * (C0 + 1) * (g + C0 + 3) ≤ 24 * (C0 + 1) * (C0 + 3) * (g + 1) ^ 3 := by
    calc 8 * (bN c n + 1) * (C0 + 1) * (g + C0 + 3)
        ≤ 8 * (3 * (g + 1)) * (C0 + 1) * ((C0 + 3) * (g + 1)) := by gcongr
      _ = 24 * (C0 + 1) * (C0 + 3) * (g + 1) ^ 2 := by ring
      _ ≤ 24 * (C0 + 1) * (C0 + 3) * (g + 1) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  calc (C0 + 8) * (g + 3) ^ 3 + 8 * (bN c n + 1) * (C0 + 1) * (g + C0 + 3)
      ≤ (C0 + 8) * (27 * (g + 1) ^ 3) + 24 * (C0 + 1) * (C0 + 3) * (g + 1) ^ 3 := by gcongr
    _ = _ := by ring

theorem poly_eventually (A m : ℕ) : ∀ᶠ N : ℕ in atTop, m * (A * (N.log2 + 1) ^ 3) ≤ N := by
  filter_upwards [Polylog.eventually_polylog_le (m * A + 1) 3] with N hN
  calc m * (A * (N.log2 + 1) ^ 3) = (m * A) * (N.log2 + 1) ^ 3 := by ring
    _ ≤ (m * A + 1) ^ 3 * (N.log2 + 1) ^ 3 := by
        gcongr
        calc m * A ≤ m * A + 1 := by omega
          _ = (m * A + 1) ^ 1 := by ring
          _ ≤ (m * A + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    _ = ((m * A + 1) * (N.log2 + 1)) ^ 3 := by ring
    _ ≤ N := hN

/-- The schedule part is `o(n)`. -/
theorem schedule_eventually (k c m : ℕ) (hc : 2 ≤ c) :
    ∀ᶠ n : ℕ in atTop, 8 * m * (2 * (k + 1) * numBlocks (clk c n)) ≤ n + 1 + 16 * m * (k + 1) := by
  set B := 32 * m * (k + 1) * c + 1
  filter_upwards [eventually_ge_atTop (2 ^ B)] with n hn
  set t := clk c n
  have hbB : B ≤ blockLength t := by
    unfold blockLength
    have h : B - 1 < Nat.clog 2 (t + 2) := by
      rw [← ProgTerm.lt_clog_iff]
      have : 2 ^ (B - 1) ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : n ≤ t := by unfold t clk; nlinarith
      omega
    omega
  have hnb : numBlocks t ≤ t / B + 1 := by
    unfold numBlocks
    rw [Nat.ceilDiv_eq_add_pred_div]
    calc (t + blockLength t - 1) / blockLength t ≤ (t + blockLength t) / blockLength t :=
          Nat.div_le_div_right (by omega)
      _ = t / blockLength t + 1 := Nat.add_div_right t (by omega)
      _ ≤ t / B + 1 := by gcongr
  have hdiv : t / B * B ≤ t := Nat.div_mul_le_self t B
  have hkey : 8 * m * (2 * (k + 1)) * (t / B) * (2 * c) ≤ t := by
    calc 8 * m * (2 * (k + 1)) * (t / B) * (2 * c) = (t / B) * (32 * m * (k + 1) * c) := by ring
      _ ≤ (t / B) * B := Nat.mul_le_mul_left _ (by omega)
      _ ≤ t := hdiv
  have ht : t = c * (n + 1) := by unfold t clk; ring
  have hkey' : 8 * m * (2 * (k + 1)) * (t / B) * 2 ≤ n + 1 := by
    have h2 : (8 * m * (2 * (k + 1)) * (t / B) * 2) * c ≤ (n + 1) * c := by
      calc (8 * m * (2 * (k + 1)) * (t / B) * 2) * c = 8 * m * (2 * (k + 1)) * (t / B) * (2 * c) := by
            ring
        _ ≤ t := hkey
        _ = (n + 1) * c := by rw [ht]; ring
    exact Nat.le_of_mul_le_mul_right h2 (by omega)
  calc 8 * m * (2 * (k + 1) * numBlocks t) ≤ 8 * m * (2 * (k + 1) * (t / B + 1)) := by gcongr
    _ = 8 * m * (2 * (k + 1)) * (t / B) + 16 * m * (k + 1) := by ring
    _ ≤ n + 1 + 16 * m * (k + 1) := by omega

end NtimeDspace.Budget
