import NtimeDspace.Parameters
import NtimeDspace.SpectralTail

/-!
# Spectral and measurement bounds for the paper's explicit parameters

For `s = 2^k`, `Q = s² k`, and `R = 8 s k`, the actual bad spectral
indices satisfy `3 s^5 c ≤ D`. Combining this integer inequality with the
copy-occupancy bound gives the measurement-row budget without rounding or
division assumptions. No machine resource claim is made here.
-/

namespace NtimeDspace.TailParameters

noncomputable section

open Parameters

/-- The actual parameterized tensor-index and coordinate space. -/
abbrev Label (k : ℕ) := TensorBasisField.Label (Fin (Q k)) (s k)

def center (k : ℕ) : ℝ := SpectralTail.mean (Q k) (s k)

/-- The bad indices for the actual floor-centered interpolation window. -/
def badIndices (k : ℕ) : Finset (Label k) :=
  ParityInterpolation.badIndices TensorBasisField.antisymmetricCount
    (CenteredWindow.start (center k) (R k)) (R k)

def badCount (k : ℕ) : ℕ := (badIndices k).card

def tau (k : ℕ) : ℝ := 1 / (s k : ℝ) ^ 4

theorem exponent_eq (k : ℕ) (positive : 0 < k) :
    (R k : ℝ) ^ 2 / (8 * (Q k : ℝ)) = 8 * k := by
  have hs : (s k : ℝ) ≠ 0 := by exact_mod_cast (s_pos k).ne'
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  simp only [R, Q, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  field_simp

/-- An elementary exponential estimate, valid already for `k ≥ 1`. -/
theorem six_mul_s_pow_five_le_exp (k : ℕ) (positive : 0 < k) :
    6 * (s k : ℝ) ^ 5 ≤ Real.exp (8 * k) := by
  have six : (6 : ℝ) ≤ (2 : ℝ) ^ (3 * k) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 3 ≤ 3 * k by omega)
    norm_num at h
    linarith
  have two : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  calc
    6 * (s k : ℝ) ^ 5 = 6 * (2 : ℝ) ^ (5 * k) := by
      simp [s, ← pow_mul, Nat.mul_comm]
    _ ≤ (2 : ℝ) ^ (3 * k) * (2 : ℝ) ^ (5 * k) :=
      mul_le_mul_of_nonneg_right six (by positivity)
    _ = (2 : ℝ) ^ (8 * k) := by rw [← pow_add]; congr 1; omega
    _ ≤ (Real.exp 1) ^ (8 * k) := pow_le_pow_left₀ (by norm_num) two _
    _ = Real.exp (8 * k) := by rw [← Real.exp_nat_mul]; simp

theorem exponential_tail_le (k : ℕ) (positive : 0 < k) :
    2 * Real.exp (-8 * k) ≤ 1 / (3 * (s k : ℝ) ^ 5) := by
  have hs : (0 : ℝ) < s k := by exact_mod_cast s_pos k
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 3 * (s k : ℝ) ^ 5)).mpr
  calc
    (2 * Real.exp (-8 * k)) * (3 * (s k : ℝ) ^ 5) =
        (6 * (s k : ℝ) ^ 5) / Real.exp (8 * k) := by
      rw [show (-8 : ℝ) * k = -(8 * (k : ℝ)) by ring, Real.exp_neg]
      ring
    _ ≤ 1 := (div_le_one (Real.exp_pos _)).mpr (six_mul_s_pow_five_le_exp k positive)

theorem exponential_tail_le_tau (k : ℕ) (positive : 0 < k) :
    2 * Real.exp (-8 * k) ≤ tau k / (3 * s k) := by
  convert exponential_tail_le k positive using 1
  simp only [tau]
  ring

/-- The concrete bad spectrum satisfies the paper's tail bound with its exact
chosen parameters; no asymptotic threshold beyond `k > 0` is needed here. -/
theorem badCount_le (k : ℕ) (positive : 0 < k) :
    (badCount k : ℝ) ≤ (D k : ℝ) / (3 * (s k : ℝ) ^ 5) := by
  have width : 2 ≤ R k := by
    have hs := s_pos k
    unfold R
    nlinarith
  have tail := SpectralTail.badIndices_card_le (Node := Fin (Q k))
    (s k) (R k) (s_pos k) width
  have tail' : (badCount k : ℝ) ≤
      (D k : ℝ) * (2 * Real.exp (-8 * k)) := by
    simpa only [badCount, badIndices, center, D, Fintype.card_fin, Nat.cast_pow,
      neg_div, exponent_eq k positive, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using tail
  calc
    _ ≤ (D k : ℝ) * (2 * Real.exp (-8 * k)) := tail'
    _ ≤ (D k : ℝ) * (1 / (3 * (s k : ℝ) ^ 5)) :=
      mul_le_mul_of_nonneg_left (exponential_tail_le k positive) (by positivity)
    _ = _ := by ring

theorem badCount_le_tau (k : ℕ) (positive : 0 < k) :
    (badCount k : ℝ) ≤ (D k : ℝ) * tau k / (3 * s k) := by
  convert badCount_le k positive using 1
  simp only [tau]
  ring

/-- Cross-multiplied natural-number version, suitable for row-count bounds. -/
theorem badCount_scaled (k : ℕ) (positive : 0 < k) :
    3 * s k ^ 5 * badCount k ≤ D k := by
  have hs : (0 : ℝ) < s k := by exact_mod_cast s_pos k
  have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 3 * (s k : ℝ) ^ 5)).mp
    (badCount_le k positive)
  exact_mod_cast (show (3 : ℝ) * (s k : ℝ) ^ 5 * badCount k ≤ D k by nlinarith)

/-- One restricted row for each group, copy, and actual bad basis index. -/
abbrev MeasurementRow (k copies : ℕ) := Fin (s k) × Fin copies × badIndices k

theorem measurementRow_card (k copies : ℕ) :
    Fintype.card (MeasurementRow k copies) = s k * copies * badCount k := by
  simp [MeasurementRow, badCount, Nat.mul_assoc]

/-- The row-count calculation is purely integral: `c ≤ D/(3r⁵)` and
`hD ≤ 2M ≤ 6N` imply `rhc · r⁴ ≤ 2N`. -/
theorem measurement_rows_scaled_of_bounds (r copies count dimension incidences variableCount : ℕ)
    (spectral : 3 * r ^ 5 * count ≤ dimension)
    (occupancy : copies * dimension ≤ 2 * incidences)
    (incidence_bound : incidences ≤ 3 * variableCount) :
    (r * copies * count) * r ^ 4 ≤ 2 * variableCount := by
  have h := Nat.mul_le_mul_left copies spectral
  have htotal : copies * (3 * r ^ 5 * count) ≤ 6 * variableCount := by
    exact h.trans (occupancy.trans (by omega))
  have hrewrite : copies * (3 * r ^ 5 * count) = 3 * ((r * copies * count) * r ^ 4) := by ring
  rw [hrewrite] at htotal
  omega

/-- D3's total number of actual restricted rows satisfies the stated budget. -/
theorem measurementRow_scaled (k copies incidences variableCount : ℕ) (positive : 0 < k)
    (occupancy : copies * D k ≤ 2 * incidences)
    (incidence_bound : incidences ≤ 3 * variableCount) :
    Fintype.card (MeasurementRow k copies) * s k ^ 4 ≤ 2 * variableCount := by
  rw [measurementRow_card]
  exact measurement_rows_scaled_of_bounds (s k) copies (badCount k) (D k)
    incidences variableCount (badCount_scaled k positive) occupancy incidence_bound

theorem measurementRow_le (k copies incidences variableCount : ℕ) (positive : 0 < k)
    (occupancy : copies * D k ≤ 2 * incidences)
    (incidence_bound : incidences ≤ 3 * variableCount) :
    (Fintype.card (MeasurementRow k copies) : ℝ) ≤ 2 * tau k * variableCount := by
  have hs : (0 : ℝ) < s k := by exact_mod_cast s_pos k
  have h : (Fintype.card (MeasurementRow k copies) : ℝ) * (s k : ℝ) ^ 4 ≤ 2 * variableCount := by
    exact_mod_cast measurementRow_scaled k copies incidences variableCount positive occupancy incidence_bound
  calc
    _ ≤ (2 * variableCount) / (s k : ℝ) ^ 4 := (le_div_iff₀ (by positivity)).mpr h
    _ = _ := by simp only [tau]; ring

end

end NtimeDspace.TailParameters
