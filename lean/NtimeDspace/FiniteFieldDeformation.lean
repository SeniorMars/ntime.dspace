import NtimeDspace.MatrixSpectralBridge
import NtimeDspace.TensorBasisField
import NtimeDspace.ParityInterpolation

/-!
The explicit spectral deformation is constructed directly in the prime field.
Its normalization and degree bound follow from the concrete tensor basis,
parity interpolation, matrix locality, and mismatch-node product. No Kintali
deformation identity is assumed. Counting bad indices and implementing the
construction with bounded workspace remain separate obligations.
-/

namespace NtimeDspace.FiniteFieldDeformation

noncomputable section

open scoped BigOperators

variable {Node : Type*} [Fintype Node] [DecidableEq Node]
variable {r p : ℕ} [Fact p.Prime]

abbrev Label (Node : Type*) (r : ℕ) := Node → Fin r × Fin r

def bad (start : ℤ) (width : ℕ) : Finset (Label Node r) :=
  ParityInterpolation.badIndices TensorBasisField.antisymmetricCount start width

def residualCoefficient (start : ℤ) (width : ℕ) (u index : Label Node r) : ZMod p :=
  TensorBasisField.beta (ParityInterpolation.parityPolynomialMod p start width) u index

def entry (start : ℤ) (width : ℕ) : Label Node r → Label Node r → ZMod p :=
  MatrixLocality.Amatrix (ParityInterpolation.parityPolynomialMod p start width)

/-- The residual identity now has no basis or interpolation hypotheses. -/
theorem residual_identity (two_nonzero : (2 : ZMod p) ≠ 0)
    (start : ℤ) (width : ℕ) (small : width < p) (u w : Label Node r) :
    DeformationConstruction.residual (bad start width)
      (residualCoefficient start width) (TensorBasisField.tensorFamily (K := ZMod p)) u w +
      entry start width u w = if u = w then 1 else 0 := by
  have result := ParityInterpolation.parity_filtered_residual_mod p
    (TensorBasisField.tensorBasis Node r two_nonzero)
    (by simpa only [TensorBasisField.tensorBasis_apply] using
      (TensorBasisField.tensorFamily_orthogonal (K := ZMod p) (Node := Node) (r := r)))
    (by simpa only [TensorBasisField.tensorBasis_apply] using
      (TensorBasisField.tensorFamily_norm_ne_zero (Node := Node) (r := r) two_nonzero))
    SpectralDeformation.simultaneousSwap SpectralDeformation.antisymmetryOperator
    TensorBasisField.antisymmetricCount start width small
    (TensorBasisField.tensorBasis_V_eigen two_nonzero)
    (TensorBasisField.tensorBasis_W_eigen two_nonzero) u w
  simpa only [DeformationConstruction.residual, bad, residualCoefficient,
    TensorBasisField.beta, TensorBasisField.tensorBasis_apply, entry,
    MatrixSpectralBridge.Amatrix_eq_operatorEntry] using result

theorem entry_locality (start : ℤ) (width : ℕ) (small : width < p)
    (u w : Label Node r) (nonzero : entry (p := p) start width u w ≠ 0) :
    (DeformationConstruction.mismatchNodes
      (fun label node => (label node).1) (fun label node => (label node).2) u w).card ≤
        width - 1 :=
  (MatrixLocality.Amatrix_locality _ u w nonzero).trans
    (ParityInterpolation.parityPolynomialMod_degree p start width small)

/-- The actual label-to-label polynomial coefficient. -/
def coefficient (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ)
    (u w : Label Node r) : Polynomial (ZMod p) :=
  DeformationConstruction.coefficient nodeValue
    (fun label node => (label node).1) (fun label node => (label node).2)
    (bad start width) (residualCoefficient start width)
    (TensorBasisField.tensorFamily (K := ZMod p)) (entry start width) u w

theorem coefficient_origin (two_nonzero : (2 : ZMod p) ≠ 0)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (small : width < p)
    (u w : Label Node r) :
    (coefficient nodeValue start width u w).eval 0 = if u = w then 1 else 0 := by
  apply DeformationConstruction.coefficient_origin
  exact residual_identity two_nonzero start width small

theorem coefficient_degree (nodeValue : Node → ZMod p)
    (start : ℤ) (width : ℕ) (small : width < p) (u w : Label Node r) :
    (coefficient nodeValue start width u w).natDegree ≤ width - 1 := by
  apply DeformationConstruction.coefficient_degree
  exact entry_locality start width small

set_option maxHeartbeats 1000000 in
/-- Node evaluation of an occupied copy splits into exceptional measurements
and variables in the matching local group. -/
theorem occupied_at_node (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ)
    (occupied : Finset (Label Node r)) (values : Label Node r → ZMod p)
    (u : Label Node r) (node : Node) (nonzero : nodeValue node ≠ 0) :
    (∑ w ∈ occupied, coefficient nodeValue start width u w * Polynomial.C (values w)).eval
        (nodeValue node) =
      (∑ index ∈ bad start width, residualCoefficient start width u index *
        ∑ w ∈ occupied, TensorBasisField.tensorFamily index w * values w) +
      ∑ w ∈ occupied.filter (fun w => (w node).1 = (u node).2),
        entry start width u w *
          (DeformationConstruction.phi nodeValue
            (fun label node => (label node).1) (fun label node => (label node).2) u w).eval
              (nodeValue node) * values w := by
  have result := DeformationConstruction.occupiedForm_at_node nodeValue
    (fun label node => (label node).1) (fun label node => (label node).2)
    (bad start width) (residualCoefficient start width) TensorBasisField.tensorFamily
    (entry start width) occupied values u node nonzero
  simpa only [DeformationConstruction.occupiedForm, coefficient] using result

end

end NtimeDspace.FiniteFieldDeformation
