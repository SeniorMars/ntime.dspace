import NtimeDspace.FiniteProductTail
import NtimeDspace.SpectralPairCount
import NtimeDspace.CenteredWindow

/-!
# The actual bad-spectrum cardinality bound

Uniform ordered pairs have antisymmetric probability `(r-1)/(2r)`.
Independence across tensor coordinates gives Hoeffding concentration, and the
rounded interpolation window contains every count less than `R/4` from its
mean. Together these facts bound the concrete set of bad tensor indices.
-/

namespace NtimeDspace.SpectralTail

noncomputable section

open scoped BigOperators
open SpectralPairCount FiniteProductTail

theorem antisymmetricBit_average (r : ℕ) (positive : 0 < r) :
    average (antisymmetricBit (r := r)) = ((r : ℝ) - 1) / (2 * r) := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  unfold average
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  calc
    _ = (2 * ∑ pair : Fin r × Fin r, antisymmetricBit pair) / (2 * ((r : ℝ) * r)) := by ring
    _ = _ := by rw [antisymmetricBit_sum]; field_simp

/-- The exact mean of the antisymmetric-count observable on the tensor basis. -/
def mean (coordinates alphabet : ℕ) : ℝ :=
  coordinates * ((alphabet : ℝ) - 1) / (2 * alphabet)

/-- A two-sided tail estimate for the actual concrete-basis index count. -/
theorem antisymmetricCount_tail_card_le {Node : Type*} [Fintype Node] [DecidableEq Node]
    (r : ℕ) (positive : 0 < r) (ε : ℝ) (nonnegative : 0 ≤ ε) :
    ((Finset.univ.filter (fun index : TensorBasisField.Label Node r =>
      ε ≤ |(TensorBasisField.antisymmetricCount index : ℝ) - mean (Fintype.card Node) r|)).card : ℝ) ≤
      2 * (r : ℝ) ^ (2 * Fintype.card Node) *
        Real.exp (-2 * ε ^ 2 / Fintype.card Node) := by
  classical
  letI : NeZero r := ⟨Nat.ne_of_gt positive⟩
  have h := product_tail_card_le (I := Node) (antisymmetricBit (r := r))
    antisymmetricBit_bounds ε nonnegative
  simpa only [antisymmetricBit_average r positive, ← antisymmetricCount_eq_sum,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, ← pow_two, Nat.cast_pow, ← pow_mul,
    mean, mul_div_assoc] using h

/-- Kintali's bad-spectrum estimate, with the concrete basis, actual rounded
integer window, exact mean, and all probabilistic premises discharged.
The window lemma needs only `2 ≤ width`, weaker than the paper's `32 ≤ R`. -/
theorem badIndices_card_le {Node : Type*} [Fintype Node] [DecidableEq Node]
    (r width : ℕ) (positive : 0 < r) (large : 2 ≤ width) :
    ((ParityInterpolation.badIndices
      (TensorBasisField.antisymmetricCount (Node := Node) (r := r))
      (CenteredWindow.start (mean (Fintype.card Node) r) width) width).card : ℝ) ≤
      2 * (r : ℝ) ^ (2 * Fintype.card Node) *
        Real.exp (-((width : ℝ) ^ 2) / (8 * Fintype.card Node)) := by
  have subset := CenteredWindow.bad_indices_subset
    (TensorBasisField.antisymmetricCount (Node := Node) (r := r))
    (mean (Fintype.card Node) r) width large
  have count_le := Finset.card_le_card subset
  have bound := antisymmetricCount_tail_card_le (Node := Node) r positive
    ((width : ℝ) / 4) (by positivity)
  have bound' := (show ((ParityInterpolation.badIndices
    (TensorBasisField.antisymmetricCount (Node := Node) (r := r))
    (CenteredWindow.start (mean (Fintype.card Node) r) width) width).card : ℝ) ≤ _ by
      exact_mod_cast count_le).trans bound
  convert bound' using 1
  congr 2
  ring

end

end NtimeDspace.SpectralTail
