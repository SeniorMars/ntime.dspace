import NtimeDspace.TensorEvaluation
import NtimeDspace.ParityEvaluation

/-!
# Scalar evaluation of the concrete finite-field deformation

The spectral residual is summed over explicitly indexed bad labels. Its
complement gives the matrix entry by the already-proved residual identity, so
the executable procedure constructs neither matrix powers nor a matrix. The
coefficient evaluator combines this scalar entry with the mismatch product.

Tensor labels are accessed as functions and recomputed by scalar routines;
no vector, polynomial, or table of bad labels is constructed. The results here
are functional correctness, not Turing-machine time or workspace guarantees.
-/

namespace NtimeDspace.DeformationEvaluation

open scoped BigOperators
open GroupedAssignmentEvaluation

variable (p : ℕ) [Fact p.Prime] {r Q : ℕ}

/-- A scalar residual coefficient, using the computed parity interpolant and
the tensor norm's power-of-two formula. -/
def beta (start : ℤ) (width : ℕ) (u index : TensorEvaluation.Label r Q) : ZMod p :=
  let count := TensorEvaluation.antisymmetricCount index
  (1 - (-1 : ZMod p) ^ count * ParityEvaluation.evaluate p start width (count : ZMod p)) *
    TensorEvaluation.tensorEntry index u / TensorEvaluation.tensorNorm index

theorem beta_correct (start : ℤ) (width : ℕ) (u index : TensorEvaluation.Label r Q) :
    beta p start width u index = FiniteFieldDeformation.residualCoefficient start width u index := by
  simp only [beta, FiniteFieldDeformation.residualCoefficient, TensorBasisField.beta,
    TensorEvaluation.antisymmetricCount_correct, TensorEvaluation.tensorEntry_correct,
    TensorEvaluation.tensorNorm_correct, ParityEvaluation.evaluate_correct]

/-- The actual bad-label residual, streamed in ordinal order. `badAt` uses a
bounded scalar search, not a chosen inverse or a stored filtered list. -/
def residual (positive : 0 < r) (start : ℤ) (width : ℕ)
    (u w : TensorEvaluation.Label r Q) : ZMod p :=
  scanSum (fun ordinal : Fin (SpectralIndexing.badCount r Q positive start width) =>
    let index := SpectralIndexing.badAt r Q positive start width ordinal
    beta p start width u index.val * TensorEvaluation.tensorEntry index.val w) 0

theorem residual_correct (positive : 0 < r) (start : ℤ) (width : ℕ)
    (u w : TensorEvaluation.Label r Q) :
    residual p positive start width u w =
      DeformationConstruction.residual (FiniteFieldDeformation.bad start width)
        (FiniteFieldDeformation.residualCoefficient (p := p) start width)
        TensorBasisField.tensorFamily u w := by
  rw [residual, scanSum_correct, add_zero]
  simp only [beta_correct, TensorEvaluation.tensorEntry_correct]
  let term : FiniteFieldDeformation.Label (Fin Q) r → ZMod p := fun index =>
    FiniteFieldDeformation.residualCoefficient start width u index * TensorBasisField.tensorFamily index w
  change (∑ ordinal : Fin (SpectralIndexing.badCount r Q positive start width),
      term (SpectralIndexing.badAt r Q positive start width ordinal).val) = _
  calc
    _ = ∑ index : SpectralIndexing.BadLabel r Q start width, term index.val :=
      (SpectralIndexing.badAtEquiv r Q positive start width).sum_comp (fun index => term index.val)
    _ = _ :=
      (Finset.sum_subtype (FiniteFieldDeformation.bad (Node := Fin Q) (r := r) start width)
        (fun _ => Iff.rfl) term).symm

/-- Compute the required matrix entry as the identity entry minus the
spectral residual, avoiding construction of the matrix or its powers. -/
def entry (positive : 0 < r) (start : ℤ) (width : ℕ)
    (u w : TensorEvaluation.Label r Q) : ZMod p :=
  (if TensorEvaluation.sameLabel u w then 1 else 0) - residual p positive start width u w

theorem entry_correct (positive : 0 < r) (two_nonzero : (2 : ZMod p) ≠ 0)
    (start : ℤ) (width : ℕ) (small : width < p) (u w : TensorEvaluation.Label r Q) :
    entry p positive start width u w = FiniteFieldDeformation.entry start width u w := by
  rw [entry, residual_correct]
  simp only [TensorEvaluation.sameLabel_correct]
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm] using
    (FiniteFieldDeformation.residual_identity two_nonzero start width small u w).symm

/-- The coefficient value uses one computed residual for both its constant
part and its complementary matrix entry. -/
def coefficient (positive : 0 < r) (nodeValue : Fin Q → ZMod p) (start : ℤ) (width : ℕ)
    (u w : TensorEvaluation.Label r Q) (point : ZMod p) : ZMod p :=
  let residualValue := residual p positive start width u w
  residualValue + ((if TensorEvaluation.sameLabel u w then 1 else 0) - residualValue) *
    TensorEvaluation.mismatchProduct nodeValue u w point

theorem coefficient_correct (positive : 0 < r) (two_nonzero : (2 : ZMod p) ≠ 0)
    (nodeValue : Fin Q → ZMod p) (start : ℤ) (width : ℕ) (small : width < p)
    (u w : TensorEvaluation.Label r Q) (point : ZMod p) :
    coefficient p positive nodeValue start width u w point =
      (FiniteFieldDeformation.coefficient nodeValue start width u w).eval point := by
  change residual p positive start width u w + entry p positive start width u w *
    TensorEvaluation.mismatchProduct nodeValue u w point = _
  rw [residual_correct, entry_correct p positive two_nonzero start width small,
    TensorEvaluation.mismatchProduct_correct]
  simp only [FiniteFieldDeformation.coefficient, DeformationConstruction.coefficient,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]

end NtimeDspace.DeformationEvaluation
