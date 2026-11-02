import NtimeDspace.ParameterChoice
import NtimeDspace.SupportBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Real logarithmic estimates for the actual bounded-search parameter from the
manuscript. These compare numerical resource expressions; they do not assert
that an implemented machine uses that much space.
-/

namespace NtimeDspace.ParameterAsymptotics

open Filter Parameters ParameterChoice
open scoped Topology

/-- Every fixed parameter is eventually admitted by the concrete search. -/
theorem selected_ge_of_pow_cost_le (N k : ℕ) (large : 2 ^ cost k ≤ N) :
    k ≤ choose N := by
  apply maximal N k
  rw [Nat.log2_eq_log_two]
  exact Nat.le_log_of_pow_le (by norm_num) large

theorem selected_monotone : Monotone choose := by
  intro M N hMN
  apply maximal N (choose M)
  exact (admissible M).trans (by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hMN)

theorem selected_tendsto_atTop : Tendsto choose atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (2 ^ cost k)] with N hN
  exact selected_ge_of_pow_cost_le N k hN

theorem selected_eventually_positive : ∀ᶠ N : ℕ in atTop, 0 < choose N := by
  filter_upwards [selected_tendsto_atTop.eventually_ge_atTop 1] with N hN
  omega

/-- Floor-log conversion with a concrete factor, avoiding any asymptotic
assumption about the selected search value. -/
theorem log_le_twice_log2 (N : ℕ) (hN : 0 < N) (hlog : 1 ≤ N.log2) :
    Real.log N ≤ 2 * (N.log2 : ℝ) := by
  have hpow : N < 2 ^ (N.log2 + 1) := by
    simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hpowR : (N : ℝ) < (2 : ℝ) ^ (N.log2 + 1) := by exact_mod_cast hpow
  have h := Real.log_lt_log (by exact_mod_cast hN) hpowR
  rw [Real.log_pow] at h
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hL : (1 : ℝ) ≤ N.log2 := by exact_mod_cast hlog
  push_cast at h
  nlinarith [mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ N.log2 + 1)]

/-- Admissibility bounds the selected integer by four times log log N,
once log N is at least two. -/
theorem selected_le_four_log_log (N : ℕ) (positive : 0 < choose N)
    (large_log : 2 ≤ Real.log N) :
    (choose N : ℝ) ≤ 4 * Real.log (Real.log N) := by
  let k := choose N
  have hsL : s k ≤ N.log2 :=
    (s_le_R k positive).trans (R_le_log2 N k positive (admissible N))
  have hsR : (0 : ℝ) < s k := by exact_mod_cast s_pos k
  have hlog : (k : ℝ) * Real.log 2 ≤ Real.log (N.log2 : ℝ) := by
    have h : Real.log (s k : ℝ) ≤ Real.log (N.log2 : ℝ) :=
      Real.log_le_log hsR (by exact_mod_cast hsL)
    simpa only [s, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hLupper : (N.log2 : ℝ) ≤ 2 * Real.log N := by
    have h := Real.log2_le_logb N
    rw [Real.logb] at h
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hm := (le_div_iff₀ hl2).mp h
    nlinarith [mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg N.log2)]
  have hLpos : (0 : ℝ) < N.log2 := lt_of_lt_of_le hsR (by exact_mod_cast hsL)
  have hLsq : (N.log2 : ℝ) ≤ (Real.log N) ^ 2 := by nlinarith
  have hlogupper := Real.log_le_log hLpos hLsq
  rw [Real.log_pow] at hlogupper
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  norm_num at hlogupper
  nlinarith [mul_le_mul_of_nonneg_left hhalf hk]

/-- Maximality supplies the matching lower bound on s, expressed without
squaring a quotient or changing the parameter search. -/
theorem sqrt_log_le_scaled_s (N : ℕ) (positive : 0 < choose N)
    (hN : 0 < N) :
    Real.sqrt (Real.log N) ≤ 32 * (s (choose N) : ℝ) * choose N := by
  let k := choose N
  have hk : (0 : ℝ) < k := by exact_mod_cast positive
  have hs : (0 : ℝ) < s k := by exact_mod_cast s_pos k
  have hL : 1 ≤ N.log2 := (by omega : 1 ≤ k).trans (selected_le_log2 N)
  have hlog := log_le_twice_log2 N hN hL
  have hmax := log2_lt_sixteen_cost N positive
  have hmaxR : (N.log2 : ℝ) < 256 * (s k : ℝ) ^ 2 * (k : ℝ) ^ 2 := by
    dsimp [cost] at hmax
    have hm : (N.log2 : ℝ) < 16 * (16 * (s k : ℝ) ^ 2 * (k : ℝ) ^ 2) := by
      exact_mod_cast hmax
    nlinarith
  have hsq : Real.log N ≤ (32 * (s k : ℝ) * k) ^ 2 := by nlinarith
  exact (Real.sqrt_le_iff).2 ⟨by positivity, hsq⟩

/-- An explicit constant for the manuscript's central parameter estimate. -/
theorem parameter_ratio_le (N : ℕ) (positive : 0 < choose N)
    (large_log : 2 ≤ Real.log N) :
    (choose N : ℝ) / s (choose N) ≤
      512 * (Real.log (Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by
  let k := choose N
  have hN : 0 < N := by
    by_contra hn
    have : N = 0 := by omega
    norm_num [this] at large_log
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs : (0 : ℝ) < s k := by exact_mod_cast s_pos k
  have ht : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.2 (by linarith)
  have hsmall := selected_le_four_log_log N positive large_log
  have hden := sqrt_log_le_scaled_s N positive hN
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hk2 : (k : ℝ) ^ 2 ≤ 16 * (Real.log (Real.log N)) ^ 2 := by
    dsimp [k]
    nlinarith
  apply (div_le_div_iff₀ hs ht).2
  have hmul := mul_le_mul_of_nonneg_left hden hk
  have hmul2 := mul_le_mul_of_nonneg_right hk2 (by positivity : (0 : ℝ) ≤ 32 * s k)
  nlinarith

/-- The parameter resource term has the claimed natural-logarithm rate.
The only eventual conditions are proved from the concrete search and log's
ordinary growth; the conclusion is not an input hypothesis. -/
theorem parameter_term_isBigO :
    (fun N : ℕ => (N : ℝ) * choose N / s (choose N)) =O[atTop]
      (fun N : ℕ => (N : ℝ) * (Real.log (Real.log N)) ^ 2 / Real.sqrt (Real.log N)) := by
  apply Asymptotics.IsBigO.of_bound 512
  have hgrowth : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [selected_eventually_positive, hgrowth.eventually_ge_atTop 2] with N hk hlog
  have h := mul_le_mul_of_nonneg_left (parameter_ratio_le N hk hlog) (Nat.cast_nonneg N)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  simpa only [mul_div_assoc, mul_left_comm, mul_assoc] using h

/-- The paper's rate, using natural logs. Its value at small inputs is irrelevant
to the asymptotic statements; Lean's total logarithm and division fix it. -/
noncomputable def kappa (N : ℕ) : ℝ :=
  (N : ℝ) * (Real.log (Real.log N)) ^ 2 / Real.sqrt (Real.log N)

/-- The lower-order table budget is eventually bounded by κ with constant one. -/
theorem table_term_eventually_le_kappa :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 / 4 : ℝ) * Real.log N ≤ kappa N := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
    (by norm_num : (0 : ℝ) < 3 / 4)).bound (by norm_num : (0 : ℝ) < 1)
  have hsmallN := tendsto_natCast_atTop_atTop.eventually hsmall
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hsmallN, hlog.eventually_ge_atTop 1,
    hloglog.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hbound hlogN hloglogN hN
  dsimp only [Function.comp_def] at hloglogN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogpos : 0 < Real.log N := by linarith
  have hsqrt : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.2 hlogpos
  have hproduct : Real.log N * Real.sqrt (Real.log N) =
      (Real.log N) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.log N * (Real.log N) ^ (1 / 2 : ℝ) =
          (Real.log N) ^ (1 : ℝ) * (Real.log N) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = (Real.log N) ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hlogpos]; norm_num
  have hbound' : (Real.log N) ^ (3 / 2 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlogpos.le _),
      abs_of_nonneg (Real.rpow_nonneg hNpos.le _), one_mul] using hbound
  have htotal : ((N : ℝ) ^ (1 / 4 : ℝ) * Real.log N) * Real.sqrt (Real.log N) ≤ N := by
    calc
      _ = (N : ℝ) ^ (1 / 4 : ℝ) * (Real.log N) ^ (3 / 2 : ℝ) := by rw [← hproduct]; ring
      _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hbound' (Real.rpow_nonneg hNpos.le _)
      _ = N := by rw [← Real.rpow_add hNpos]; norm_num
  unfold kappa
  apply (le_div_iff₀ hsqrt).2
  have hll : 1 ≤ (Real.log (Real.log N)) ^ 2 := by nlinarith
  exact htotal.trans (by nlinarith [mul_le_mul_of_nonneg_left hll hNpos.le])

theorem table_term_isBigO :
    (fun N : ℕ => (N : ℝ) ^ (1 / 4 : ℝ) * Real.log N) =O[atTop] kappa := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [table_term_eventually_le_kappa] with N hN
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) * Real.log N),
    abs_of_nonneg (by unfold kappa; positivity : 0 ≤ kappa N), one_mul] using hN

/-- κ is sublinear, independently of whether an algorithm attains this rate. -/
theorem kappa_isLittleO_linear : kappa =o[atTop] (fun N : ℕ => (N : ℝ)) := by
  have hsmall : (fun x : ℝ => (Real.log x) ^ (2 : ℕ)) =o[atTop]
      (fun x : ℝ => Real.sqrt x) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlimit := (hsmall.comp_tendsto hlog).tendsto_div_nhds_zero
  apply Asymptotics.isLittleO_of_tendsto
  · intro N hN
    simp only [kappa, hN, zero_mul, zero_div]
  · have hcancel (N : ℕ) : kappa N / (N : ℝ) =
        (Real.log (Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by
      by_cases hN : (N : ℝ) = 0
      · simp [kappa, hN]
      · simp [kappa, mul_div_assoc, mul_div_cancel_left₀ _ hN]
    simpa only [hcancel, Function.comp_def] using hlimit

/-- The ceiling used by actual support enumeration costs at most one extra bit,
and that constant is absorbed by the selected parameter term. -/
theorem support_limit_le_parameter_term (N : ℕ) (positive : 0 < choose N) :
    (SupportBounds.supportLimit N (choose N) : ℝ) ≤
      73 * ((N : ℝ) * choose N / s (choose N)) := by
  let k := choose N
  have hs : (0 : ℝ) < s k := by exact_mod_cast s_pos k
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast positive
  have hsN : s k ≤ N :=
    (s_le_R k positive).trans (R_le_N N k positive (admissible N))
  have hsNR : (s k : ℝ) ≤ N := by exact_mod_cast hsN
  have hterm : 1 ≤ (N : ℝ) * k / s k := by
    apply (le_div_iff₀ hs).2
    nlinarith [mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg N)]
  have hmain : (24 : ℝ) * N * (2 * k + 1) / s k ≤
      72 * ((N : ℝ) * k / s k) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hs).2
    nlinarith [mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg N)]
  have hceil := Nat.ceil_lt_add_one (by positivity :
    (0 : ℝ) ≤ 24 * N * (2 * k + 1) / s k)
  change (⌈(24 : ℝ) * N * (2 * k + 1) / s k⌉₊ : ℝ) ≤ _
  nlinarith

theorem support_limit_isBigO :
    (fun N : ℕ => (SupportBounds.supportLimit N (choose N) : ℝ)) =O[atTop] kappa := by
  have h : (fun N : ℕ => (SupportBounds.supportLimit N (choose N) : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) * choose N / s (choose N)) := by
    apply Asymptotics.IsBigO.of_bound 73
    filter_upwards [selected_eventually_positive] with N hk
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ SupportBounds.supportLimit N (choose N)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) * choose N / s (choose N))] using
      support_limit_le_parameter_term N hk
  exact h.trans parameter_term_isBigO

theorem parameter_and_table_isBigO :
    (fun N : ℕ => (N : ℝ) * choose N / s (choose N) +
      (N : ℝ) ^ (1 / 4 : ℝ) * Real.log N) =O[atTop] kappa :=
  parameter_term_isBigO.add table_term_isBigO

theorem parameter_and_table_isLittleO_linear :
    (fun N : ℕ => (N : ℝ) * choose N / s (choose N) +
      (N : ℝ) ^ (1 / 4 : ℝ) * Real.log N) =o[atTop] (fun N : ℕ => (N : ℝ)) :=
  parameter_and_table_isBigO.trans_isLittleO kappa_isLittleO_linear

end NtimeDspace.ParameterAsymptotics
