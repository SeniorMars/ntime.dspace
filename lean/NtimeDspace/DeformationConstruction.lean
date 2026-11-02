import NtimeDspace.PolynomialFacts
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
The explicit polynomial part of the spectral deformation. The coefficients
are built from the residual expansion and the mismatch-node product. Origin,
node locality, degree, and occupied-copy identities are proved directly.

Residual expansion and matrix locality are named, explicit inputs here. The
spectral module must supply them; this file does not assert the entire Kintali
construction as an axiom or prove a machine resource bound.
-/

namespace NtimeDspace.DeformationConstruction

noncomputable section

open scoped BigOperators

variable {Node Label Group Index K : Type*}
variable [Fintype Node] [DecidableEq Group] [Field K]

def mismatchNodes (first second : Label → Node → Group) (u w : Label) : Finset Node :=
  Finset.univ.filter (fun node => first w node ≠ second u node)

def nodeFactor (value : K) : Polynomial K :=
  1 - Polynomial.C value⁻¹ * Polynomial.X

def phi (nodeValue : Node → K) (first second : Label → Node → Group)
    (u w : Label) : Polynomial K :=
  ∏ node ∈ mismatchNodes first second u w, nodeFactor (nodeValue node)

@[simp] theorem nodeFactor_eval_zero (value : K) : (nodeFactor value).eval 0 = 1 := by
  simp [nodeFactor]

theorem nodeFactor_eval_self (value : K) (nonzero : value ≠ 0) :
    (nodeFactor value).eval value = 0 := by
  simp [nodeFactor, nonzero]

@[simp] theorem phi_eval_zero (nodeValue : Node → K)
    (first second : Label → Node → Group) (u w : Label) :
    (phi nodeValue first second u w).eval 0 = 1 := by
  simp [phi, Polynomial.eval_prod]

theorem phi_eval_eq_zero (nodeValue : Node → K)
    (first second : Label → Node → Group) (u w : Label) (node : Node)
    (nonzero : nodeValue node ≠ 0) (mismatch : first w node ≠ second u node) :
    (phi nodeValue first second u w).eval (nodeValue node) = 0 := by
  rw [phi, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := node)
  · simp [mismatchNodes, mismatch]
  · exact nodeFactor_eval_self _ nonzero

theorem nodeFactor_degree (value : K) : (nodeFactor value).natDegree ≤ 1 := by
  unfold nodeFactor
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le (by simp)
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

theorem phi_degree (nodeValue : Node → K)
    (first second : Label → Node → Group) (u w : Label) :
    (phi nodeValue first second u w).natDegree ≤ (mismatchNodes first second u w).card := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _node ∈ mismatchNodes first second u w, 1 :=
      Finset.sum_le_sum (fun node _ => nodeFactor_degree (nodeValue node))
    _ = _ := by simp

def residual (bad : Finset Index) (beta : Label → Index → K)
    (basis : Index → Label → K) (u w : Label) : K :=
  ∑ index ∈ bad, beta u index * basis index w

def coefficient (nodeValue : Node → K) (first second : Label → Node → Group)
    (bad : Finset Index) (beta : Label → Index → K) (basis : Index → Label → K)
    (A : Label → Label → K) (u w : Label) : Polynomial K :=
  Polynomial.C (residual bad beta basis u w) +
    Polynomial.C (A u w) * phi nodeValue first second u w

/-- The supplied spectral residual identity proves the exact coefficient
normalization at the origin. -/
theorem coefficient_origin [DecidableEq Label] (nodeValue : Node → K)
    (first second : Label → Node → Group) (bad : Finset Index)
    (beta : Label → Index → K) (basis : Index → Label → K) (A : Label → Label → K)
    (residual_identity : ∀ u w, residual bad beta basis u w + A u w =
      if u = w then 1 else 0) (u w : Label) :
    (coefficient nodeValue first second bad beta basis A u w).eval 0 =
      if u = w then 1 else 0 := by
  simpa [coefficient] using residual_identity u w

/-- Matrix locality bounds the degree of every nonconstant summand. Zero
matrix entries contribute only a constant residual coefficient. -/
theorem coefficient_degree (nodeValue : Node → K)
    (first second : Label → Node → Group) (bad : Finset Index)
    (beta : Label → Index → K) (basis : Index → Label → K) (A : Label → Label → K)
    (bound : ℕ) (locality : ∀ u w, A u w ≠ 0 →
      (mismatchNodes first second u w).card ≤ bound) (u w : Label) :
    (coefficient nodeValue first second bad beta basis A u w).natDegree ≤ bound := by
  unfold coefficient
  apply Polynomial.natDegree_add_le_of_degree_le (by simp)
  by_cases zero : A u w = 0
  · simp [zero]
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((phi_degree nodeValue first second u w).trans (locality u w zero))

/-- The auxiliary form on an occupied copy. Its entries may repeat the same
variable; distinct positions remain separate summands. -/
def occupiedForm (nodeValue : Node → K) (first second : Label → Node → Group)
    (bad : Finset Index) (beta : Label → Index → K) (basis : Index → Label → K)
    (A : Label → Label → K) (occupied : Finset Label) (values : Label → K)
    (u : Label) : Polynomial K :=
  ∑ w ∈ occupied,
    coefficient nodeValue first second bad beta basis A u w * Polynomial.C (values w)

theorem occupiedForm_origin [DecidableEq Label] (nodeValue : Node → K)
    (first second : Label → Node → Group) (bad : Finset Index)
    (beta : Label → Index → K) (basis : Index → Label → K) (A : Label → Label → K)
    (residual_identity : ∀ u w, residual bad beta basis u w + A u w =
      if u = w then 1 else 0) (occupied : Finset Label) (values : Label → K)
    (u : Label) (included : u ∈ occupied) :
    (occupiedForm nodeValue first second bad beta basis A occupied values u).eval 0 = values u := by
  unfold occupiedForm
  simp only [NtimeDspace.PolynomialFacts.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    coefficient_origin nodeValue first second bad beta basis A residual_identity]
  simp [included]

theorem occupiedForm_degree (nodeValue : Node → K)
    (first second : Label → Node → Group) (bad : Finset Index)
    (beta : Label → Index → K) (basis : Index → Label → K) (A : Label → Label → K)
    (bound : ℕ) (locality : ∀ u w, A u w ≠ 0 →
      (mismatchNodes first second u w).card ≤ bound)
    (occupied : Finset Label) (values : Label → K) (u : Label) :
    (occupiedForm nodeValue first second bad beta basis A occupied values u).natDegree ≤ bound := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro w _
  exact (Polynomial.natDegree_mul_C_le _ _).trans
    (coefficient_degree nodeValue first second bad beta basis A bound locality u w)

/-- Node evaluation has exactly a residual-measurement part and a local part.
Every nonlocal term vanishes by the explicit mismatch product. -/
theorem occupiedForm_at_node (nodeValue : Node → K)
    (first second : Label → Node → Group) (bad : Finset Index)
    (beta : Label → Index → K) (basis : Index → Label → K) (A : Label → Label → K)
    (occupied : Finset Label) (values : Label → K) (u : Label) (node : Node)
    (nonzero : nodeValue node ≠ 0) :
    (occupiedForm nodeValue first second bad beta basis A occupied values u).eval (nodeValue node) =
      (∑ index ∈ bad, beta u index * ∑ w ∈ occupied, basis index w * values w) +
        ∑ w ∈ occupied.filter (fun w => first w node = second u node),
          A u w * (phi nodeValue first second u w).eval (nodeValue node) * values w := by
  unfold occupiedForm coefficient
  simp only [NtimeDspace.PolynomialFacts.eval_finset_sum, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp only [residual, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    by_cases same : first w node = second u node
    · simp [same]
    · simp [same, phi_eval_eq_zero nodeValue first second u w node nonzero same]

end

end NtimeDspace.DeformationConstruction
