import NtimeDspace.MachineContract
import Mathlib.NumberTheory.Bertrand

/-!
# A nonempty modulus window at the fixed exponent three

Bertrand's postulate supplies a prime strictly above `4 * N²` and at most
`8 * N²`. For `N ≥ 8` this lies below `N³`; explicit prime witnesses cover
`N = 5, 6, 7`. Thus the modular-input contract at exponent three is nonvacuous
for every bounded-occurrence formula on at least five declared variables.

The input constructor below uses classical choice. No prime-search algorithm,
search time, or workspace bound is asserted.
-/

namespace NtimeDspace.PrimeWindow

/-- A prime in the manuscript's modulus window, at the fixed exponent three.
The numerical threshold five includes the three cases below the direct
Bertrand bound. -/
theorem exists_admissible_prime (N : ℕ) (large : 5 ≤ N) :
    ∃ p : ℕ, p.Prime ∧ 4 * N ^ 2 < p ∧ p ≤ N ^ 3 := by
  by_cases bertrand_large : 8 ≤ N
  · obtain ⟨p, prime, lower, upper⟩ :=
      Nat.exists_prime_lt_and_le_two_mul (4 * N ^ 2) (by positivity)
    refine ⟨p, prime, lower, upper.trans ?_⟩
    calc
      2 * (4 * N ^ 2) = 8 * N ^ 2 := by ring
      _ ≤ N * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) bertrand_large
      _ = N ^ 3 := by ring
  · have small : N = 5 ∨ N = 6 ∨ N = 7 := by omega
    rcases small with rfl | rfl | rfl
    · exact ⟨101, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨149, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨197, by norm_num, by norm_num, by norm_num⟩

/-- Choose an admissible modulus without changing the supplied formula or its
declared variable count. This is an existence-level, noncomputable constructor. -/
noncomputable def input {N : ℕ} (formula : Formula N)
    (bounded : formula.BoundedOccurrence) (large : 5 ≤ N) : ModularInput 3 where
  variableCount := N
  formula := formula
  bounded := bounded
  modulus := (exists_admissible_prime N large).choose
  prime := (exists_admissible_prime N large).choose_spec.1
  lower := (exists_admissible_prime N large).choose_spec.2.1
  upper := (exists_admissible_prime N large).choose_spec.2.2

@[simp] theorem input_variableCount {N : ℕ} (formula : Formula N)
    (bounded : formula.BoundedOccurrence) (large : 5 ≤ N) :
    (input formula bounded large).variableCount = N := rfl

@[simp] theorem input_formula {N : ℕ} (formula : Formula N)
    (bounded : formula.BoundedOccurrence) (large : 5 ≤ N) :
    (input formula bounded large).formula = formula := rfl

end NtimeDspace.PrimeWindow
