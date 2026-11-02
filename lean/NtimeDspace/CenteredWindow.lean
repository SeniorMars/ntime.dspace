import NtimeDspace.ParityInterpolation
import Mathlib.Data.Real.Archimedean

/-!
The floor-centered integer window used for the parity interpolant contains
every integer less than R/4 from its center. This separates rounding details
from the probabilistic tail estimate for exceptional tensor indices.
-/

namespace NtimeDspace.CenteredWindow

noncomputable section

def start (center : ℝ) (width : ℕ) : ℤ :=
  ⌊center - ((width : ℝ) - 1) / 2⌋

/-- The rounding argument needs only width at least two. -/
theorem mem_of_distance_lt (center : ℝ) (width : ℕ) (large : 2 ≤ width) (j : ℤ)
    (near : |(j : ℝ) - center| < (width : ℝ) / 4) :
    j ∈ ParityInterpolation.integerWindow (start center width) width := by
  have lower := Int.floor_le (center - ((width : ℝ) - 1) / 2)
  have upper := Int.lt_floor_add_one (center - ((width : ℝ) - 1) / 2)
  have hwidth : (2 : ℝ) ≤ width := by exact_mod_cast large
  rw [abs_lt] at near
  apply (ParityInterpolation.mem_integerWindow _ _ _).mpr
  constructor
  · have h : (start center width : ℝ) ≤ j := by
      dsimp [start]
      linarith
    exact_mod_cast h
  · have h : (j : ℝ) < (start center width : ℝ) + width := by
      dsimp [start]
      linarith
    exact_mod_cast h

/-- Every integer outside the actual rounded window belongs to the two-sided
tail event with threshold R/4. -/
theorem distance_le_of_not_mem (center : ℝ) (width : ℕ) (large : 2 ≤ width) (j : ℤ)
    (outside : j ∉ ParityInterpolation.integerWindow (start center width) width) :
    (width : ℝ) / 4 ≤ |(j : ℝ) - center| := by
  by_contra h
  exact outside (mem_of_distance_lt center width large j (lt_of_not_ge h))

/-- Specialization to the concrete tensor eigenvalue count, whose bad set is
already the one used by the finite-field construction. -/
theorem bad_indices_subset {Index : Type*} [Fintype Index]
    (count : Index → ℕ) (center : ℝ) (width : ℕ) (large : 2 ≤ width) :
    ParityInterpolation.badIndices count (start center width) width ⊆
      Finset.univ.filter (fun index => (width : ℝ) / 4 ≤ |(count index : ℝ) - center|) := by
  intro index included
  simp only [ParityInterpolation.badIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at included ⊢
  simpa only [Int.cast_natCast] using
    distance_le_of_not_mem center width large (count index) included

end

end NtimeDspace.CenteredWindow
