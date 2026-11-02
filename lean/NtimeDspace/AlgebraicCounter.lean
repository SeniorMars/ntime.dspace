import NtimeDspace.DeformationTaylor
import NtimeDspace.HermiteGlobal

/-!
Composition of the proved Taylor-data and scalar-recovery transformations.
The expression is a finite algebraic specification. It still contains symbolic
polynomials and full assignment sums; it is not a small-space implementation.
Constructing the spectral deformation, realizing grouped access, and proving
machine resources remain separate obligations.
-/

namespace NtimeDspace.AlgebraicCounter

noncomputable section

open scoped BigOperators
open DeformationTaylor TaylorTruncation HermiteRecovery

variable {Var Inc : Type*} [DecidableEq Var] {p : ℕ} [Fact p.Prime]

def scalarExpression (ground : Finset Var) (P : MvPolynomial Inc (ZMod p))
    (coeff : Inc → Var → Polynomial (ZMod p)) (nodes : Finset (ZMod p))
    (order : ℕ) : ZMod p :=
  (nodeProduct nodes order).eval 0 *
    ∑ node ∈ nodes, ∑ z : (ZMod p)ˣ,
      (z : ZMod p) ^ (p - order) * (nodeWeight nodes node order).eval (z : ZMod p) *
        (taylorData ground (expandedPolynomial ground P coeff node) Polynomial.X order).eval
          (z : ZMod p)

/-- The scalar expression recovers the counting polynomial at zero. Both the
Taylor congruence and the degree bounds are derived from the specified linear
forms. No global interpolation or Taylor-correctness premise remains. -/
theorem scalarExpression_correct (ground : Finset Var) (P : MvPolynomial Inc (ZMod p))
    (coeff : Inc → Var → Polynomial (ZMod p)) (nodes : Finset (ZMod p))
    (order bound : ℕ) (positive : 0 < order) (below_prime : order < p)
    (nonzero_nodes : ∀ node ∈ nodes, node ≠ 0)
    (degrees : ∀ inc i, i ∈ ground → (coeff inc i).natDegree ≤ bound)
    (interpolation_capacity : P.totalDegree * bound < nodes.card * order)
    (no_alias : P.totalDegree * bound ≤ p - 2) :
    scalarExpression ground P coeff nodes order = (countingPolynomial ground P coeff).eval 0 := by
  symm
  apply multi_node_scalar_recovery nodes order positive below_prime nonzero_nodes
    (countingPolynomial ground P coeff)
    (fun node => taylorData ground (expandedPolynomial ground P coeff node) Polynomial.X order)
  · exact (countingPolynomial_degree ground P coeff bound degrees).trans_lt interpolation_capacity
  · intro node _
    exact (taylorData_degree ground P coeff node order bound degrees).trans no_alias
  · intro node _
    exact dvd_sub_comm.mp (deformation_taylor_congruence ground P coeff node order)

end

end NtimeDspace.AlgebraicCounter
