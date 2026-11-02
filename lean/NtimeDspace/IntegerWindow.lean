import NtimeDspace.TailParameters

/-!
An integer-only computation of the manuscript's centered parity window.
The real-valued spectral mean and floor occur only in the specification.
The formula holds also at `k = 0`, with the same integer-division convention.
-/

namespace NtimeDspace.IntegerWindow

open Parameters

/-- Euclidean integer division computes the lower endpoint without real data. -/
def start (k : ℕ) : ℤ := ((s k : ℤ) * k * ((s k : ℤ) - 9) + 1) / 2

theorem centered_argument (k : ℕ) :
    TailParameters.center k - ((R k : ℝ) - 1) / 2 =
      ((s k : ℝ) * k * ((s k : ℝ) - 9) + 1) / 2 := by
  have positive : (s k : ℝ) ≠ 0 := by exact_mod_cast (s_pos k).ne'
  unfold TailParameters.center SpectralTail.mean R Q
  push_cast
  field_simp
  ring

/-- The executable endpoint is exactly the floor-centered spectral window. -/
theorem start_eq_centered (k : ℕ) :
    start k = CenteredWindow.start (TailParameters.center k) (R k) := by
  unfold start CenteredWindow.start
  rw [centered_argument]
  have cast_numerator :
      (((s k : ℤ) * k * ((s k : ℤ) - 9) + 1 : ℤ) : ℝ) =
        (s k : ℝ) * k * ((s k : ℝ) - 9) + 1 := by push_cast; rfl
  rw [← cast_numerator]
  simpa only [Int.floor_intCast, Nat.cast_ofNat] using
    (Int.floor_div_natCast
      (((s k : ℤ) * k * ((s k : ℤ) - 9) + 1 : ℤ) : ℝ) 2).symm

end NtimeDspace.IntegerWindow
