import NtimeDspace.UniformSpace

/-!
# Every budget is `O(S)`

`L_le_S`: for fixed machine constants, `L(n) ≤ C·S(n) + C` for all `n ≥ 1`.
The `N`-only part uses `N ≤ K·(n+1)`, the monotonicity of `choose` and the
decrease of `k/2^k`; the polylogarithmic part uses `log₂ N ≤ log₂ n + B`; the
schedule part uses `blockLength t ≥ log₂ n + 1`.
-/

namespace NtimeDspace.Budget

open Parameters Cslib.Complexity.CountingSimulation ProgTerm Filter

/-- `k / 2^k` decreases for `k ≥ 1`. -/
theorem ks_anti {a b : ℕ} (h1 : 1 ≤ a) (hab : a ≤ b) : b * s a ≤ a * s b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    have hs : s (b + 1) = 2 * s b := by unfold s; ring
    rw [hs]
    have : s a ≤ s b := Nat.pow_le_pow_right (by norm_num) hab
    nlinarith

theorem log2_mono {a b : ℕ} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]; exact Nat.log_mono_right h

theorem L_eq (k s c C0 n : ℕ) : L k s c C0 n =
    polyPart k s c C0 n + Gpart (NN k s c n) + 2 * (k + 1) * numBlocks (tN c n) + C0 + 8 := by
  simp only [L, Gpart, tupleWidth]; ring

/-- `log₂ (a·b) ≤ log₂ a + log₂ b + 1`. -/
theorem log2_mul_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : (a * b).log2 ≤ a.log2 + b.log2 + 1 := by
  have h1 := Nat.lt_log2_self (n := a)
  have h2 := Nat.lt_log2_self (n := b)
  have : a * b < 2 ^ (a.log2 + b.log2 + 2) := by
    calc a * b < 2 ^ (a.log2 + 1) * 2 ^ (b.log2 + 1) := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ (a.log2 + b.log2 + 2) := by rw [← pow_add]; ring_nf
  have := (Nat.log2_lt (by positivity)).mpr this
  omega

/-- The `N`-only part is `O(S)`. -/
theorem Gpart_le_S (K n : ℕ) (hK : 1 ≤ K) (N : ℕ) (hNn : n ≤ N) (hN : N ≤ 2 * K * n)
    (hk : 0 < ParameterChoice.choose n) :
    Gpart N ≤ 200 * K * (n * (ParameterChoice.choose n + 1) / s (ParameterChoice.choose n) + 1) + 3 := by
  have hmono : ParameterChoice.choose n ≤ ParameterChoice.choose N :=
    ParameterAsymptotics.selected_monotone hNn
  have hkN : 0 < ParameterChoice.choose N := lt_of_lt_of_le hk hmono
  have hG := Gpart_le N hkN
  set a := ParameterChoice.choose n
  set b := ParameterChoice.choose N
  have hab := ks_anti hk hmono
  have hsa : (0 : ℝ) < s a := by exact_mod_cast s_pos a
  have hsb : (0 : ℝ) < s b := by exact_mod_cast s_pos b
  have h1 : (N : ℝ) * b / s b ≤ (N : ℝ) * a / s a := by
    rw [div_le_div_iff₀ hsb hsa]
    have : (b : ℝ) * s a ≤ a * s b := by exact_mod_cast hab
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have h2 : (N : ℝ) * a / s a ≤ 2 * K * ((n : ℝ) * a / s a) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hsa]
    have : (N : ℝ) ≤ 2 * K * n := by exact_mod_cast hN
    nlinarith [Nat.cast_nonneg (α := ℝ) a]
  have h3 : (n : ℝ) * a / s a ≤ ((n * (a + 1) / s a : ℕ) : ℝ) + 1 := by
    have hfl := Nat.lt_div_mul_add (a := n * (a + 1)) (b := s a) (s_pos a)
    have hr : ((n * (a + 1) : ℕ) : ℝ) < ((n * (a + 1) / s a : ℕ) : ℝ) * s a + s a := by exact_mod_cast hfl
    rw [div_le_iff₀ hsa]
    push_cast at hr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have key : (Gpart N : ℝ) ≤ 200 * K * (((n * (a + 1) / s a : ℕ) : ℝ) + 1) + 3 := by
    have := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 2 * K by positivity)
    nlinarith
  exact_mod_cast key

theorem blockLength_ge (c n : ℕ) (hc : 1 ≤ c) (hn : 1 ≤ n) : n.log2 + 1 ≤ blockLength (clk c n) := by
  unfold blockLength
  have h : n.log2 < Nat.clog 2 (clk c n + 2) := by
    rw [← ProgTerm.lt_clog_iff]
    have := Nat.log2_self_le (n := n) (by omega)
    have : n ≤ clk c n := by unfold clk; nlinarith
    omega
  omega

theorem schedule_le (k c n : ℕ) (hc : 1 ≤ c) (hn : 1 ≤ n) :
    2 * (k + 1) * numBlocks (clk c n) ≤ 2 * (k + 1) * (c * (n / (n.log2 + 1)) + c + 2) := by
  have hb := blockLength_ge c n hc hn
  apply Nat.mul_le_mul_left
  unfold numBlocks
  rw [Nat.ceilDiv_eq_add_pred_div]
  set b := blockLength (clk c n)
  set l := n.log2 + 1
  have h1 : (clk c n + b - 1) / b ≤ clk c n / b + 1 := by
    calc (clk c n + b - 1) / b ≤ (clk c n + b) / b := Nat.div_le_div_right (by omega)
      _ = clk c n / b + 1 := Nat.add_div_right _ (by omega)
  have h2 : clk c n / b ≤ clk c n / l := Nat.div_le_div_left hb (by omega)
  have h3 : clk c n / l ≤ c * (n / l) + c + 1 := by
    unfold clk
    have hl : 0 < l := by omega
    rw [Nat.div_le_iff_le_mul_add_pred hl]
    have hmod := Nat.mod_lt n hl
    have hdiv := Nat.div_add_mod n l
    nlinarith
  omega

theorem polyPart_le_S (k s c C0 n : ℕ) (hc : 2 ≤ c) (hn : 1 ≤ n) :
    polyPart k s c C0 n ≤ (27 * (C0 + 8) + 24 * (C0 + 1) * (C0 + 3)) *
      ((4 * (3 * k + 1) * (s + k + 4) * c * 2).log2 + 3) ^ 3 * (n.log2 + 1) ^ 4 := by
  set K := 4 * (3 * k + 1) * (s + k + 4) * c
  have hK : 1 ≤ K := by
    have : 1 ≤ 4 * (3 * k + 1) * (s + k + 4) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc 1 ≤ 4 * (3 * k + 1) * (s + k + 4) * 1 := by omega
      _ ≤ K := Nat.mul_le_mul_left _ (by omega)
  have hP := polyPart_le k s c C0 n hc
  have hNle : NN k s c n ≤ K * 2 * n := by
    have := edgesN_le k s c n hc
    calc NN k s c n ≤ K * (n + 1) := this
      _ ≤ K * 2 * n := by nlinarith
  have hlg : lgN k s c n ≤ (K * 2).log2 + n.log2 + 1 :=
    (log2_mono hNle).trans (log2_mul_le _ _ (by omega) (by omega))
  set B := (K * 2).log2 + 3
  have hB1 : B + n.log2 ≤ B * (n.log2 + 1) := by
    have : 1 ≤ B := by omega
    nlinarith
  have h1 : lgN k s c n + 1 ≤ B * (n.log2 + 1) := by omega
  have h2 : (lgN k s c n + 1) ^ 3 ≤ B ^ 3 * (n.log2 + 1) ^ 4 := by
    calc (lgN k s c n + 1) ^ 3 ≤ (B * (n.log2 + 1)) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = B ^ 3 * (n.log2 + 1) ^ 3 := by ring
      _ ≤ B ^ 3 * (n.log2 + 1) ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  calc polyPart k s c C0 n ≤ (27 * (C0 + 8) + 24 * (C0 + 1) * (C0 + 3)) * (lgN k s c n + 1) ^ 3 := hP
    _ ≤ (27 * (C0 + 8) + 24 * (C0 + 1) * (C0 + 3)) * (B ^ 3 * (n.log2 + 1) ^ 4) :=
        Nat.mul_le_mul_left _ h2
    _ = _ := by ring

/-- **Every budget is `O(S)`.** -/
theorem L_le_S (k s c C0 : ℕ) (hc : 2 ≤ c) :
    ∃ C, ∀ᶠ n in atTop, L k s c C0 n ≤ C * S n + C := by
  set K := 4 * (3 * k + 1) * (s + k + 4) * c
  set A := (27 * (C0 + 8) + 24 * (C0 + 1) * (C0 + 3)) * ((K * 2).log2 + 3) ^ 3
  refine ⟨A + 200 * K + 2 * (k + 1) * c + (200 * K + 3 + 2 * (k + 1) * (c + 2) + C0 + 8), ?_⟩
  filter_upwards [ParameterAsymptotics.selected_eventually_positive, eventually_ge_atTop 1]
    with n hk hn
  have hK : 1 ≤ K := by
    have : 1 ≤ 4 * (3 * k + 1) * (s + k + 4) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc 1 ≤ 4 * (3 * k + 1) * (s + k + 4) * 1 := by omega
      _ ≤ K := Nat.mul_le_mul_left _ (by omega)
  have hNn : n ≤ NN k s c n := by
    have : n ≤ clk c n := by unfold clk; nlinarith
    exact this.trans ((le_paddedTime _).trans (paddedTime_le_edgesN k s _))
  have hNle : NN k s c n ≤ 2 * K * n := by
    have := edgesN_le k s c n hc
    calc NN k s c n ≤ K * (n + 1) := this
      _ ≤ 2 * K * n := by nlinarith
  have hG := Gpart_le_S K n hK (NN k s c n) hNn hNle hk
  have hP := polyPart_le_S k s c C0 n hc hn
  have hS := schedule_le k c n (by omega) hn
  rw [L_eq]
  unfold S
  set S1 := n * (ParameterChoice.choose n + 1) / Parameters.s (ParameterChoice.choose n)
  set S2 := n / (n.log2 + 1)
  set S3 := (n.log2 + 1) ^ 4
  have hP' : polyPart k s c C0 n ≤ A * S3 := hP
  set C := A + 200 * K + 2 * (k + 1) * c + (200 * K + 3 + 2 * (k + 1) * (c + 2) + C0 + 8)
  have e1 : 2 * (k + 1) * (c * S2 + c + 2) = 2 * (k + 1) * c * S2 + 2 * (k + 1) * (c + 2) := by ring
  have e2 : 200 * K * (S1 + 1) = 200 * K * S1 + 200 * K := by ring
  have m1 : 200 * K * S1 ≤ C * S1 := Nat.mul_le_mul_right _ (by omega)
  have m2 : 2 * (k + 1) * c * S2 ≤ C * S2 := Nat.mul_le_mul_right _ (by omega)
  have m3 : A * S3 ≤ C * S3 := Nat.mul_le_mul_right _ (by omega)
  have hS' : 2 * (k + 1) * numBlocks (tN c n) ≤ 2 * (k + 1) * c * S2 + 2 * (k + 1) * (c + 2) := by
    rw [← e1]; exact hS
  calc polyPart k s c C0 n + Gpart (NN k s c n) + 2 * (k + 1) * numBlocks (tN c n) + C0 + 8
      ≤ A * S3 + (200 * K * S1 + 200 * K + 3) + (2 * (k + 1) * c * S2 + 2 * (k + 1) * (c + 2)) +
          C0 + 8 := by rw [e2] at hG; omega
    _ ≤ C * S1 + C * S2 + C * S3 + C := by omega
    _ = C * (S1 + S2 + S3) + C := by ring

end NtimeDspace.Budget
