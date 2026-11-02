import Mathlib.Tactic

/-!
Exact integer arithmetic for Section 4's parameter choice. These lemmas do not
assert the eventual real-logarithm asymptotic bound or machine-space usage.
-/

namespace NtimeDspace.Parameters

def s (k : ℕ) : ℕ := 2 ^ k
def Q (k : ℕ) : ℕ := s k ^ 2 * k
def R (k : ℕ) : ℕ := 8 * s k * k
def D (k : ℕ) : ℕ := s k ^ (2 * Q k)
def q (N k : ℕ) : ℕ := 3 * N * R k / Q k

theorem s_pos (k : ℕ) : 0 < s k := by
  exact Nat.two_pow_pos k

theorem Q_pos (k : ℕ) (hk : 0 < k) : 0 < Q k := by
  exact Nat.mul_pos (pow_pos (s_pos k) 2) hk

theorem D_binary (k : ℕ) : D k = 2 ^ (2 * s k ^ 2 * k ^ 2) := by
  unfold D Q s
  rw [← pow_mul]
  congr 1
  ring

theorem D_pow_eight (k : ℕ) : D k ^ 8 = 2 ^ (16 * s k ^ 2 * k ^ 2) := by
  rw [D_binary, ← pow_mul]
  congr 1
  ring

/-- The integer version of the manuscript's `D ≤ N^(1/8)` estimate. -/
theorem D_pow_eight_le (N k : ℕ) (hN : 0 < N)
    (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) : D k ^ 8 ≤ N := by
  rw [D_pow_eight]
  apply (Nat.pow_le_pow_right (by decide : 0 < 2) budget).trans
  exact (Nat.le_log2 hN.ne').mp (le_refl N.log2)

/-- The floor in the Taylor cutoff simplifies exactly with the chosen parameters. -/
theorem q_eq (N k : ℕ) (hk : 0 < k) : q N k = 24 * N / s k := by
  have hden : 0 < s k * k := Nat.mul_pos (s_pos k) hk
  have hnum : 3 * N * R k = (24 * N) * (s k * k) := by unfold R; ring
  have hQ : Q k = s k * (s k * k) := by unfold Q; ring
  unfold q
  rw [hnum, hQ]
  exact Nat.mul_div_mul_right _ _ hden

/-- Positive node count ensures that the chosen number of Taylor coefficients
strictly exceeds the degree bound. -/
theorem degree_below_QJ (N k : ℕ) (hk : 0 < k) :
    3 * N * R k < Q k * (q N k + 1) := by
  exact Nat.lt_mul_div_succ _ (Q_pos k hk)

/-- A small eighth power is enough for the construction's incidence threshold. -/
theorem incidence_budget {labels N : ℕ} (hlabels : 2 ≤ labels)
    (hbudget : labels ^ 8 ≤ N) : 12 * labels ^ 2 ≤ N := by
  have hsix : 12 ≤ labels ^ 6 := by
    have h := Nat.pow_le_pow_left hlabels 6
    norm_num at h
    omega
  calc
    12 * labels ^ 2 ≤ labels ^ 6 * labels ^ 2 := Nat.mul_le_mul_right _ hsix
    _ = labels ^ 8 := by rw [← pow_add]
    _ ≤ N := hbudget

/-- The manuscript starts at `k = 6`, hence its group count is at least 64. -/
theorem sixty_four_le_s (k : ℕ) (hk : 6 ≤ k) : 64 ≤ s k := by
  simpa [s] using Nat.pow_le_pow_right (by decide : 0 < 2) hk

theorem thirty_two_le_R (k : ℕ) (hk : 6 ≤ k) : 32 ≤ R k := by
  have hs := sixty_four_le_s k hk
  unfold R
  nlinarith

theorem six_mul_R_le_Q (k : ℕ) (hk : 6 ≤ k) : 6 * R k ≤ Q k := by
  have hs : 48 ≤ s k := (by omega : 48 ≤ 64).trans (sixty_four_le_s k hk)
  calc
    6 * R k = 48 * s k * k := by unfold R; ring
    _ ≤ s k * s k * k := Nat.mul_le_mul_right k (Nat.mul_le_mul_right (s k) hs)
    _ = Q k := by unfold Q; ring

theorem s_le_D (k : ℕ) (hk : 0 < k) : s k ≤ D k := by
  exact Nat.le_self_pow (by have := Q_pos k hk; omega) (s k)

theorem two_le_D (k : ℕ) (hk : 6 ≤ k) : 2 ≤ D k := by
  exact (by have := sixty_four_le_s k hk; omega : 2 ≤ s k).trans
    (s_le_D k (by omega))

/-- The parameter inequalities depend only on the discrete log budget here. -/
theorem Q_le_log2 (N k : ℕ) (hk : 0 < k)
    (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) : Q k ≤ N.log2 := by
  have hfactor : 1 ≤ 16 * k := by omega
  calc
    Q k = 1 * Q k := by simp
    _ ≤ (16 * k) * Q k := Nat.mul_le_mul_right _ hfactor
    _ = 16 * s k ^ 2 * k ^ 2 := by unfold Q; ring
    _ ≤ N.log2 := budget

theorem R_le_log2 (N k : ℕ) (hk : 0 < k)
    (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) : R k ≤ N.log2 := by
  have hfactor : 1 ≤ 2 * s k * k := by have := s_pos k; nlinarith
  calc
    R k = R k * 1 := by simp
    _ ≤ R k * (2 * s k * k) := Nat.mul_le_mul_left _ hfactor
    _ = 16 * s k ^ 2 * k ^ 2 := by unfold R; ring
    _ ≤ N.log2 := budget

theorem Q_le_N (N k : ℕ) (hk : 0 < k)
    (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) : Q k ≤ N :=
  (Q_le_log2 N k hk budget).trans (Nat.log2_le_self N)

theorem R_le_N (N k : ℕ) (hk : 0 < k)
    (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) : R k ≤ N :=
  (R_le_log2 N k hk budget).trans (Nat.log2_le_self N)

theorem s_le_R (k : ℕ) (hk : 0 < k) : s k ≤ R k := by
  have hfactor : 1 ≤ 8 * k := by omega
  calc
    s k = s k * 1 := by simp
    _ ≤ s k * (8 * k) := Nat.mul_le_mul_left _ hfactor
    _ = R k := by unfold R; ring

theorem q_pos (N k : ℕ) (hk : 0 < k)
    (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) : 0 < q N k := by
  have hsN := (s_le_R k hk).trans (R_le_N N k hk budget)
  rw [q_eq N k hk]
  exact Nat.div_pos (by omega) (s_pos k)

theorem q_mul_s_le (N k : ℕ) (hk : 0 < k) : q N k * s k ≤ 24 * N := by
  rw [q_eq N k hk]
  exact Nat.div_mul_le_self _ _

theorem q_le_half (N k : ℕ) (hk : 6 ≤ k) : q N k ≤ N / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  have hs := sixty_four_le_s k hk
  have hq := q_mul_s_le N k (by omega)
  have hscale : q N k * 48 ≤ q N k * s k := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- With the selected parameters there is room for every affine schedule. -/
theorem schedule_budget_of_D_pow_eight (N k : ℕ) (hk : 6 ≤ k)
    (hbudget : D k ^ 8 ≤ N) : 2 * Q k * s k ^ 2 ≤ N := by
  have hs : 2 ≤ s k := by have := sixty_four_le_s k hk; omega
  have hks : k ≤ s k := (Nat.lt_two_pow_self (n := k)).le
  have htwo : 2 * k ≤ s k ^ 2 := by nlinarith
  have hQ := Q_pos k (by omega)
  calc
    2 * Q k * s k ^ 2 = (2 * k) * s k ^ 4 := by unfold Q; ring
    _ ≤ s k ^ 2 * s k ^ 4 := Nat.mul_le_mul_right _ htwo
    _ = s k ^ 6 := by rw [← pow_add]
    _ ≤ s k ^ ((2 * Q k) * 8) := Nat.pow_le_pow_right (s_pos k) (by omega)
    _ = D k ^ 8 := by unfold D; rw [← pow_mul]
    _ ≤ N := hbudget

theorem construction_incidence_budget (N M k : ℕ) (hk : 6 ≤ k)
    (hN : 0 < N) (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2)
    (incidences : N ≤ M) : 12 * D k ^ 2 ≤ M :=
  (incidence_budget (two_le_D k hk) (D_pow_eight_le N k hN budget)).trans incidences

theorem construction_schedule_budget (N k : ℕ) (hk : 6 ≤ k)
    (hN : 0 < N) (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) :
    2 * Q k * s k ^ 2 ≤ N :=
  schedule_budget_of_D_pow_eight N k hk (D_pow_eight_le N k hN budget)

theorem log_budget_implies_N_ge_256 (N k : ℕ) (hk : 6 ≤ k)
    (hN : 0 < N) (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) : 256 ≤ N := by
  have hpow := Nat.pow_le_pow_left (two_le_D k hk) 8
  norm_num at hpow
  exact hpow.trans (D_pow_eight_le N k hN budget)

theorem taylor_order_le_N (N k : ℕ) (hk : 6 ≤ k) (hN : 2 ≤ N) :
    q N k + 1 ≤ N := by
  have := q_le_half N k hk
  omega

/-- Integer degree budget used before applying the finite-field scalar identity. -/
theorem degree_plus_order_lt_four_N_sq (N k : ℕ) (hk : 6 ≤ k)
    (hN : 0 < N) (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) :
    3 * N * R k + (q N k + 1) < 4 * N ^ 2 := by
  have hlarge := log_budget_implies_N_ge_256 N k hk hN budget
  have hR := R_le_N N k (by omega) budget
  have hJ := taylor_order_le_N N k hk (by omega)
  have hmul := Nat.mul_le_mul_left (3 * N) hR
  nlinarith

/-- All scalar-recovery degree and node inequalities follow from the same
integer budget and prime lower bound. Primality itself is needed only later. -/
theorem scalar_parameter_bounds (N k p : ℕ) (hk : 6 ≤ k)
    (hN : 0 < N) (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2)
    (hp : 4 * N ^ 2 < p) :
    Q k < p ∧ R k < p ∧ q N k + 1 < p ∧ 3 * N * R k ≤ p - 2 := by
  have hQ := Q_le_N N k (by omega) budget
  have hR := R_le_N N k (by omega) budget
  have hlarge := log_budget_implies_N_ge_256 N k hk hN budget
  have hJ := taylor_order_le_N N k hk (by omega)
  have hdegree := degree_plus_order_lt_four_N_sq N k hk hN budget
  have hNp : N < p := by nlinarith
  omega

/-- Factorwise-truncated Hermite weights fit below the first aliased exponent
under the existing prime range. No larger prime or eventual threshold is needed. -/
theorem flat_scalar_no_alias (N k p : ℕ) (hk : 6 ≤ k)
    (hN : 0 < N) (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2)
    (hp : 4 * N ^ 2 < p) :
    3 * N * R k + Q k * q N k ≤ p - 2 := by
  have hQ := Q_le_N N k (by omega) budget
  have hR := R_le_N N k (by omega) budget
  have hq := q_le_half N k hk
  have hlarge := log_budget_implies_N_ge_256 N k hk hN budget
  have hR' := Nat.mul_le_mul_left (3 * N) hR
  have hQ' := Nat.mul_le_mul hQ hq
  have hhalf : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
  have hQ'' := Nat.mul_le_mul_left N hhalf
  have result : 3 * N * R k + Q k * q N k + 2 ≤ p := by nlinarith
  omega

theorem q_le_prime_sub_two (N k p : ℕ) (hk : 6 ≤ k)
    (hN : 0 < N) (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2)
    (hp : 4 * N ^ 2 < p) : q N k ≤ p - 2 := by
  have horder := (scalar_parameter_bounds N k p hk hN budget hp).2.2.1
  omega

/-- Schedule bits per node tuple satisfy a stronger integer log-budget bound. -/
theorem schedule_bits_log_budget (N k : ℕ)
    (budget : 16 * s k ^ 2 * k ^ 2 ≤ N.log2) : 16 * (Q k * k) ≤ N.log2 := by
  convert budget using 1
  unfold Q
  ring

theorem D_log2 (k : ℕ) : (D k).log2 = 2 * s k ^ 2 * k ^ 2 := by
  rw [D_binary, Nat.log2_two_pow]

/-- Bits in the ordinary binary encoding of the largest shifted measurement
value `2D`; zero is representable in the same fixed-width word. -/
def measurementBits (k : ℕ) : ℕ := (2 * D k).log2 + 1

theorem measurementBits_eq (k : ℕ) :
    measurementBits k = 2 * s k ^ 2 * k ^ 2 + 2 := by
  unfold measurementBits
  rw [D_binary, ← pow_succ', Nat.log2_two_pow]

/-- Cross-multiplied integer form of the manuscript's measurement-tuple budget.
The hypothesis is `count ≤ 2N/s^4` without rounding ambiguity. -/
theorem measurement_tuple_scaled_budget (N k count : ℕ)
    (hcount : count * s k ^ 4 ≤ 2 * N) :
    (count * measurementBits k) * s k ^ 4 ≤
      N * (4 * s k ^ 2 * k ^ 2 + 4) := by
  have h := Nat.mul_le_mul_right (measurementBits k) hcount
  rw [measurementBits_eq] at h ⊢
  nlinarith

end NtimeDspace.Parameters
