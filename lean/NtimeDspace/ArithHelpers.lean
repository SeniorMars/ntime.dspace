import NtimeDspace.WeightTerm
import NtimeDspace.ParserTerm
import NtimeDspace.ParameterChoice
import NtimeDspace.InnerLoopTerm

/-!
# Arithmetic helper terms

Terms for `Nat.clog 2`, ceiling division, `max`, the parameter choice
`ParameterChoice.choose`, and primality by trial division. Powers of a loop
variable are avoided: `2^i < m` is tested as `0 < (m-1)/2^i` by repeated
division (`divPowT`).
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-! ### `clog 2` -/

/-- `Nat.clog 2 m` for `1 ≤ m`: the number of `i < m` with `2^i < m`. -/
def clogT (m : Term) : Term :=
  sumT m fun i => lt (const 0) (divPowT (const 2) (sub m (const 1)) i)

theorem lt_clog_iff {m i : ℕ} : 2 ^ i < m ↔ i < Nat.clog 2 m := by
  rw [← not_le, ← not_le, Nat.clog_le_iff_le_pow (by norm_num)]

theorem clog_le_self (m : ℕ) : Nat.clog 2 m ≤ m := by
  rcases Nat.lt_or_ge (Nat.clog 2 m) (m + 1) with h | h
  · by_contra hc
    push_neg at hc
    have := lt_clog_iff.mpr hc
    have : m < 2 ^ m := Nat.lt_two_pow_self
    omega
  · have : 2 ^ m < m := lt_clog_iff.mpr (by omega)
    have : m < 2 ^ m := Nat.lt_two_pow_self
    omega

theorem denote_clogT {m : Term} {env : List ℕ} (hm : StableAt w m env) (hpos : 1 ≤ m.denote w env) :
    (clogT m).denote w env = Nat.clog 2 (m.denote w env) := by
  rw [clogT, denote_sumT _ _ env (fun i => if i < Nat.clog 2 (m.denote w env) then 1 else 0)
    (fun acc i => ?_), sum_lt_indicator, min_eq_right (clog_le_self _)]
  simp only [denote_lt, denote_const, divPowT_denote _ _ _ _ (stableAt_const _ _), denote_sub,
    hm.cons₂, denote_lvl_index]
  by_cases h : i < Nat.clog 2 (m.denote w env)
  · have := lt_clog_iff.mpr h
    rw [if_pos h, if_pos (Nat.div_pos_iff.mpr ⟨by positivity, by omega⟩)]
  · have : ¬ 2 ^ i < m.denote w env := fun h' => h (lt_clog_iff.mp h')
    rw [if_neg h, if_neg (by rw [Nat.div_pos_iff]; omega)]

theorem StableAt.clogT {m : Term} {env : List ℕ} (hm : StableAt w m env)
    (hpos : 1 ≤ m.denote w env) : StableAt w (clogT m) env := fun extra => by
  rw [denote_clogT (hm.extend extra) (by rw [hm extra]; exact hpos), denote_clogT hm hpos, hm extra]

/-! ### Ceiling division and maximum -/

def ceilDivT (a b : Term) : Term := div (sub (add a b) (const 1)) b

theorem denote_ceilDivT (a b : Term) (env : List ℕ) :
    (ceilDivT a b).denote w env = (a.denote w env + b.denote w env - 1) / b.denote w env := by
  simp [ceilDivT]

def maxT (a b : Term) : Term := ite (lt a b) b a

theorem denote_maxT (a b : Term) (env : List ℕ) :
    (maxT a b).denote w env = max (a.denote w env) (b.denote w env) := by
  simp only [maxT, denote_ite, denote_lt]
  split_ifs <;> omega

/-! ### The parameter choice -/

open Parameters ParameterChoice in
theorem cost_mono : Monotone cost := by
  intro a b hab
  unfold cost
  have h1 : s a ≤ s b := Nat.pow_le_pow_right (by norm_num) hab
  have h2 : s a ^ 2 ≤ s b ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h3

open Parameters ParameterChoice in
theorem cost_le_iff (k lg : ℕ) (hk : 1 ≤ k) : cost (k) ≤ lg ↔ 0 < lg / (16 * (k * k)) / 4 ^ k := by
  rw [Nat.div_pos_iff, Nat.le_div_iff_mul_le (by positivity)]
  unfold cost s
  have : (2 ^ k) ^ 2 = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [this]
  constructor
  · intro h; exact ⟨by positivity, by nlinarith⟩
  · intro h; nlinarith [h.2]

/-- `ParameterChoice.choose N`, from `lg = log₂ N`: the number of `i < lg` with
`cost (i+1) ≤ lg`. -/
def chooseT (lg : Term) : Term :=
  sumT lg fun i => lt (const 0) (divPowT (const 4)
    (div lg (mul (const 16) (mul (add i (const 1)) (add i (const 1))))) (add i (const 1)))

open Parameters ParameterChoice in
theorem denote_chooseT {lg : Term} {env : List ℕ} (hlg : StableAt w lg env) (N : ℕ)
    (hv : lg.denote w env = N.log2) : (chooseT lg).denote w env = choose N := by
  rw [chooseT, denote_sumT _ _ env (fun i => if i < choose N then 1 else 0) (fun acc i => ?_),
    sum_lt_indicator, hv, min_eq_right (selected_le_log2 N)]
  rw [denote_lt, denote_const, divPowT_denote _ _ _ _ (stableAt_const _ _)]
  simp only [denote_div, denote_mul, denote_add, denote_const, denote_lvl_index, hlg.cons₂, hv]
  by_cases h : i < choose N
  · rw [if_pos h, if_pos ((cost_le_iff (i + 1) N.log2 (by omega)).mp
      (cost_mono (show i + 1 ≤ choose N by omega) |>.trans (admissible N)))]
  · rw [if_neg h, if_neg (fun h' => h (by
      have := maximal N (i + 1) ((cost_le_iff (i + 1) N.log2 (by omega)).mpr h'); omega))]

theorem StableAt.chooseT {lg : Term} {env : List ℕ} (hlg : StableAt w lg env) (N : ℕ)
    (hv : lg.denote w env = N.log2) : StableAt w (chooseT lg) env := fun extra => by
  rw [denote_chooseT (hlg.extend extra) N (by rw [hlg extra, hv]), denote_chooseT hlg N hv]

/-! ### Primality -/

/-- `1` if `p` is prime: `2 ≤ p` and no `d` with `2 ≤ d < p` divides `p`. -/
def primeT (p : Term) : Term :=
  mul (lt (const 1) p) (allT (sub p (const 2)) fun d => lt (const 0) (mod p (add d (const 2))))

theorem prime_iff_no_small_divisor {p : ℕ} (h2 : 1 < p) :
    (∀ d < p - 2, ¬ (d + 2) ∣ p) ↔ p.Prime := by
  rw [Nat.prime_def_lt]
  constructor
  · intro h
    refine ⟨h2, fun m hm hdvd => ?_⟩
    rcases m with _ | _ | m
    · rw [Nat.zero_dvd] at hdvd; omega
    · rfl
    · exact absurd hdvd (h m (by omega))
  · rintro ⟨_, h⟩ d hd hdvd
    have := h (d + 2) (by omega) hdvd
    omega

theorem denote_primeT {p : Term} {env : List ℕ} (hp : StableAt w p env) :
    (primeT p).denote w env = if (p.denote w env).Prime then 1 else 0 := by
  rw [primeT, denote_mul, denote_lt, denote_const,
    allT_denote _ _ env (fun d => ¬ (d + 2) ∣ p.denote w env) (fun acc d => by
      simp only [denote_lt, denote_const, denote_mod, denote_add, denote_lvl_index, hp.cons₂]
      by_cases h : (d + 2) ∣ p.denote w env
      · rw [if_neg (by rw [Nat.mod_eq_zero_of_dvd h]; omega), if_neg (not_not.mpr h)]
      · rw [if_pos (Nat.pos_of_ne_zero (fun h0 => h (Nat.dvd_of_mod_eq_zero h0))), if_pos h])]
  by_cases h2 : 1 < p.denote w env
  · rw [if_pos h2, one_mul]
    by_cases hq : (p.denote w env).Prime
    · rw [if_pos hq]
      exact if_pos ((prime_iff_no_small_divisor h2).mpr hq)
    · rw [if_neg hq]
      exact if_neg (fun hall => hq ((prime_iff_no_small_divisor h2).mp hall))
  · rw [if_neg h2, zero_mul, if_neg (fun hq => h2 hq.one_lt)]

end NtimeDspace.ProgTerm
