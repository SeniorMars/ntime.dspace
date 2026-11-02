import NtimeDspace.MatrixLocality
import NtimeDspace.SpectralDeformation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
The concrete matrices used for the locality proof represent exactly the linear
operators used for the spectral proof. This bridge identifies their entries,
including the orientation of the coordinate permutation.
-/

namespace NtimeDspace.MatrixSpectralBridge

noncomputable section

open scoped BigOperators
open MatrixLocality SpectralDeformation

variable {K B : Type*} [Field K] [Fintype B] [DecidableEq B]

theorem operatorEntry_toLin (A : Matrix B B K) (u w : B) :
    operatorEntry (Matrix.toLinAlgEquiv' A) u w = A u w := by
  simp [operatorEntry, Matrix.toLinAlgEquiv'_apply]

theorem matrixPolynomial_toLin (f : Polynomial K) (W : Matrix B B K) :
    Matrix.toLinAlgEquiv' (matrixPolynomial f W) =
      polynomialOperator f (Matrix.toLinAlgEquiv' W) := by
  simp [matrixPolynomial, polynomialOperator]

variable {Node Group : Type*} [Fintype Node] [DecidableEq Node]
variable [Fintype Group] [DecidableEq Group]

omit [Fintype Node] [Fintype Group] [DecidableEq Group] in
theorem swapAt_eq_swapCoordinate (node : Node) (u : Label Node Group) :
    swapAt node u = swapCoordinate node u := rfl

omit [Fintype Node] [Fintype Group] [DecidableEq Group] in
theorem swapAt_involution (node : Node) (u : Label Node Group) :
    swapAt node (swapAt node u) = u := swapCoordinate_involution node u

omit [Fintype Node] [Fintype Group] [DecidableEq Group] in
theorem swapAt_eq_iff (node : Node) (u w : Label Node Group) :
    u = swapAt node w ↔ w = swapAt node u := by
  constructor <;> intro h
  · rw [h, swapAt_involution]
  · rw [h, swapAt_involution]

theorem swapMatrix_toLin (node : Node) :
    Matrix.toLinAlgEquiv' (swapMatrix (K := K) (Group := Group) node) =
      coordinateSwap node := by
  apply LinearMap.ext
  intro v
  funext u
  change (∑ w, (if u = swapAt node w then (1 : K) else 0) * v w) =
    v (swapAt node u)
  simp_rw [swapAt_eq_iff node u, ite_mul, one_mul, zero_mul]
  simp

theorem Wmatrix_toLin :
    Matrix.toLinAlgEquiv' (Wmatrix : Matrix (Label Node Group) (Label Node Group) K) =
      antisymmetryOperator := by
  simp [Wmatrix, antisymmetryOperator, swapMatrix_toLin]

theorem Vmatrix_toLin :
    Matrix.toLinAlgEquiv' (Vmatrix : Matrix (Label Node Group) (Label Node Group) K) =
      simultaneousSwap := by
  apply LinearMap.ext
  intro v
  funext u
  change (∑ w, (if w = MatrixLocality.swapAll u then (1 : K) else 0) * v w) =
    v (MatrixLocality.swapAll u)
  simp

theorem Amatrix_toLin (f : Polynomial K) :
    Matrix.toLinAlgEquiv' (Amatrix (Node := Node) (Group := Group) f) =
      filteredOperator simultaneousSwap antisymmetryOperator f := by
  simp [Amatrix, filteredOperator, matrixPolynomial_toLin, Vmatrix_toLin, Wmatrix_toLin]

/-- The matrix entry in the locality proof is the operator entry in the
spectral residual identity. -/
theorem Amatrix_eq_operatorEntry (f : Polynomial K) (u w : Label Node Group) :
    Amatrix f u w = operatorEntry
      (filteredOperator simultaneousSwap antisymmetryOperator f) u w := by
  rw [← Amatrix_toLin, operatorEntry_toLin]

end

end NtimeDspace.MatrixSpectralBridge
