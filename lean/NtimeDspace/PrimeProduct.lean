import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Enough primes between `4N²` and `N³`

For `N ≥ 30`, the product of the primes in `(4N², N³]` exceeds `2^N`
(`two_pow_lt_prod_primes`), by Chebyshev's lower bound on `θ`
(`Chebyshev.theta_ge`) and `primorial_le_four_pow`. So a positive number below
`2^N` is nonzero modulo one of these primes (`exists_prime_not_dvd`).
-/

namespace NtimeDspace.PrimeProduct

open Real Finset

/-- The primes in `(a, b]`. -/
def primesIoc (a b : ℕ) : Finset ℕ := (Ioc a b).filter Nat.Prime

theorem primorial_mul_prod (a b : ℕ) (hab : a ≤ b) :
    primorial a * ∏ p ∈ primesIoc a b, p = primorial b := by
  unfold primorial primesIoc
  rw [← prod_union]
  · congr 1
    ext p
    simp only [mem_union, mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩) <;> exact ⟨by omega, ‹_›⟩
    · rintro ⟨h1, h2⟩
      by_cases h : p < a + 1
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
  · rw [disjoint_left]
    intro p hp hq
    simp only [mem_filter, mem_range, mem_Ioc] at hp hq
    omega

theorem theta_nat_eq (n : ℕ) : Chebyshev.theta n = Real.log (primorial n) := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]

theorem log_le_six_sqrt (N : ℕ) : Real.log ((N : ℝ) ^ 3) ≤ 6 * √(N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.log_le_rpow_div (x := (N : ℝ) ^ 3) (ε := 1 / 6) (by positivity) (by norm_num)
  have e : ((N : ℝ) ^ 3) ^ (1 / 6 : ℝ) = √(N : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [e] at h
  linarith

theorem theta_cube_ge (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) ^ 3 * Real.log 2 - 14 * (N : ℝ) ^ 2 ≤ Chebyshev.theta (N ^ 3 : ℕ) := by
  have h := Chebyshev.theta_ge (N ^ 3)
  push_cast at h
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : √((N : ℝ) ^ 3) * √(N : ℝ) = (N : ℝ) ^ 2 := by
    rw [← Real.sqrt_mul (by positivity), show (N : ℝ) ^ 3 * N = ((N : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have h1 : Real.log ((N : ℝ) ^ 3 + 1) ≤ 2 * (N : ℝ) ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (N : ℝ) ^ 3 + 1 by positivity)
    have h2 := Real.log_le_rpow_div (x := (N : ℝ) ^ 3 + 1) (ε := 1 / 2) (by positivity) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h2
    have h3 : √((N : ℝ) ^ 3 + 1) ≤ (N : ℝ) ^ 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    linarith
  have h2 : 2 * √((N : ℝ) ^ 3) * Real.log ((N : ℝ) ^ 3) ≤ 12 * (N : ℝ) ^ 2 := by
    have := log_le_six_sqrt N
    have hs : 0 ≤ √((N : ℝ) ^ 3) := Real.sqrt_nonneg _
    calc 2 * √((N : ℝ) ^ 3) * Real.log ((N : ℝ) ^ 3)
        ≤ 2 * √((N : ℝ) ^ 3) * (6 * √(N : ℝ)) := by gcongr
      _ = 12 * (√((N : ℝ) ^ 3) * √(N : ℝ)) := by ring
      _ = 12 * (N : ℝ) ^ 2 := by rw [hsq]
  push_cast
  linarith

/-- **Enough primes**: for `N ≥ 30`, `2^N · (4N²)# < (N³)#`. -/
theorem two_pow_mul_primorial_lt (N : ℕ) (hN : 30 ≤ N) :
    2 ^ N * primorial (4 * N ^ 2) < primorial (N ^ 3) := by
  have hp1 : (0 : ℝ) < primorial (4 * N ^ 2) := by exact_mod_cast primorial_pos _
  have hp2 : (0 : ℝ) < primorial (N ^ 3) := by exact_mod_cast primorial_pos _
  have hlow := theta_cube_ge N (by omega)
  have hup : Real.log (primorial (4 * N ^ 2)) ≤ (4 * N ^ 2 : ℕ) * Real.log 4 := by
    rw [← Real.log_pow, ← theta_nat_eq]
    have := Chebyshev.theta_le_log4_mul_x (x := ((4 * N ^ 2 : ℕ) : ℝ)) (by positivity)
    rw [Real.log_pow] at *
    linarith
  rw [theta_nat_eq] at hlow
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hNr : (30 : ℝ) ≤ N := by exact_mod_cast hN
  have key : Real.log ((2 : ℝ) ^ N * primorial (4 * N ^ 2)) < Real.log (primorial (N ^ 3)) := by
    rw [Real.log_mul (by positivity) hp1.ne', Real.log_pow]
    push_cast at hup ⊢
    rw [hlog4] at hup
    have hN3 : (N : ℝ) ^ 3 = N * N ^ 2 := by ring
    have hgap : (14 : ℝ) * N ^ 2 + 8 * N ^ 2 * Real.log 2 + N * Real.log 2 < N ^ 3 * Real.log 2 := by
      have h30 : (30 : ℝ) * N ^ 2 ≤ N ^ 3 := by nlinarith
      have hl : (0.69 : ℝ) < Real.log 2 := hlog2
      have hl1 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; norm_num at this; linarith
      nlinarith [sq_nonneg (N : ℝ)]
    linarith
  have := (Real.log_lt_log_iff (by positivity) hp2).mp key
  exact_mod_cast this

theorem two_pow_lt_prod_primes (N : ℕ) (hN : 30 ≤ N) :
    2 ^ N < ∏ p ∈ primesIoc (4 * N ^ 2) (N ^ 3), p := by
  have h := two_pow_mul_primorial_lt N hN
  rw [← primorial_mul_prod (4 * N ^ 2) (N ^ 3) (by nlinarith)] at h
  have hp := primorial_pos (4 * N ^ 2)
  rw [mul_comm (primorial _)] at h
  exact Nat.lt_of_mul_lt_mul_right h

/-- A positive number below the product is not divisible by some prime of the set. -/
theorem exists_prime_not_dvd {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {m : ℕ} (hm : 0 < m)
    (hlt : m < ∏ p ∈ S, p) : ∃ p ∈ S, ¬ p ∣ m := by
  by_contra h
  push_neg at h
  have hdvd : ∏ p ∈ S, p ∣ m :=
    Finset.prod_primes_dvd m (fun p hp => (hS p hp).prime) h
  exact absurd (Nat.le_of_dvd hm hdvd) (by omega)

end NtimeDspace.PrimeProduct
