import NtimeDspace.PolynomialFacts
import NtimeDspace.TaylorTruncation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
The Taylor-data congruence for a concrete polynomial of linear deformation
forms. The factor polynomial is arbitrary, so the result applies in particular
to the product of clause factors. Correction coefficients are obtained with
`Polynomial.divX`; their divisibility is proved, not assumed.

This file does not construct the spectral deformation or its degree bounds.
-/

namespace NtimeDspace.DeformationTaylor

noncomputable section

open scoped BigOperators
open TaylorTruncation

variable {Var Inc K : Type*} [DecidableEq Var] [CommRing K]

def linearValue (ground : Finset Var) (coeff : Inc → Var → Polynomial K)
    (assigned : Finset Var) (inc : Inc) : Polynomial K :=
  ∑ i ∈ ground, if i ∈ assigned then coeff inc i else 0

def correctedForm (ground : Finset Var) (coeff : Inc → Var → Polynomial K)
    (node : K) (assigned : Finset Var) (inc : Inc) : MvPolynomial Var (Polynomial K) :=
  MvPolynomial.C (Polynomial.C ((linearValue ground coeff assigned inc).eval node)) +
    ∑ i ∈ ground,
      MvPolynomial.C ((Polynomial.taylor node (coeff inc i)).divX) * MvPolynomial.X i

def expandedPolynomial (ground : Finset Var) (P : MvPolynomial Inc K)
    (coeff : Inc → Var → Polynomial K) (node : K) (assigned : Finset Var) :
    MvPolynomial Var (Polynomial K) :=
  P.eval₂ (MvPolynomial.C.comp Polynomial.C) (correctedForm ground coeff node assigned)

def countingPolynomial (ground : Finset Var) (P : MvPolynomial Inc K)
    (coeff : Inc → Var → Polynomial K) : Polynomial K :=
  ∑ assigned ∈ ground.powerset,
    P.eval₂ Polynomial.C (linearValue ground coeff assigned)

/-- The exact correction coefficient after translation has zero constant term. -/
theorem divX_taylor_mul_X (a : Polynomial K) (node : K) :
    (Polynomial.taylor node a).divX * Polynomial.X =
      Polynomial.taylor node a - Polynomial.C (a.eval node) := by
  have h := Polynomial.divX_mul_X_add (Polynomial.taylor node a)
  rw [Polynomial.taylor_coeff_zero] at h
  exact eq_sub_of_add_eq h

theorem correctedForm_eval (ground : Finset Var) (coeff : Inc → Var → Polynomial K)
    (node : K) (assigned support : Finset Var) (inc : Inc) :
    scaledEval (correctedForm ground coeff node assigned inc) Polynomial.X support =
      Polynomial.C ((linearValue ground coeff assigned inc).eval node) +
        ∑ i ∈ ground, if i ∈ support then
          Polynomial.taylor node (coeff inc i) - Polynomial.C ((coeff inc i).eval node)
          else 0 := by
  simp only [scaledEval, correctedForm, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_C, RingHom.id_apply, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [divX_taylor_mul_X]

/-- Evaluating the correction at the same Boolean assignment gives the
translated deformation, exactly rather than merely modulo a power of `X`. -/
theorem correctedForm_diagonal (ground : Finset Var) (coeff : Inc → Var → Polynomial K)
    (node : K) (assigned : Finset Var) (inc : Inc) :
    scaledEval (correctedForm ground coeff node assigned inc) Polynomial.X assigned =
      Polynomial.taylor node (linearValue ground coeff assigned inc) := by
  rw [correctedForm_eval]
  simp only [linearValue, NtimeDspace.PolynomialFacts.eval_finset_sum, map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem expandedPolynomial_diagonal (ground : Finset Var) (P : MvPolynomial Inc K)
    (coeff : Inc → Var → Polynomial K) (node : K) (assigned : Finset Var) :
    scaledEval (expandedPolynomial ground P coeff node assigned) Polynomial.X assigned =
      Polynomial.taylor node (P.eval₂ Polynomial.C (linearValue ground coeff assigned)) := by
  let ev : MvPolynomial Var (Polynomial K) →+* Polynomial K :=
    MvPolynomial.eval₂Hom (RingHom.id _) (fun i => if i ∈ assigned then Polynomial.X else 0)
  let shift : Polynomial K →+* Polynomial K := (Polynomial.taylorAlgHom node).toRingHom
  change ev (P.eval₂ (MvPolynomial.C.comp Polynomial.C)
      (correctedForm ground coeff node assigned)) =
    shift (P.eval₂ Polynomial.C (linearValue ground coeff assigned))
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext c
    simp [ev, shift]
  · funext inc
    exact correctedForm_diagonal ground coeff node assigned inc

/-- The exact low-order Taylor-data congruence for all polynomial products of
linear deformation forms. The finite differences and assignment loops are
defined explicitly in `TaylorTruncation.taylorData`. -/
theorem deformation_taylor_congruence (ground : Finset Var) (P : MvPolynomial Inc K)
    (coeff : Inc → Var → Polynomial K) (node : K) (order : ℕ) :
    Polynomial.X ^ order ∣
      Polynomial.taylor node (countingPolynomial ground P coeff) -
        taylorData ground (expandedPolynomial ground P coeff node) Polynomial.X order := by
  have h := taylorData_congruence ground (expandedPolynomial ground P coeff node)
    Polynomial.X order
  simpa only [expandedPolynomial_diagonal, countingPolynomial, map_sum] using h

/-- Substitution into a multivariate polynomial multiplies total degree by an
upper bound for the degrees of the substituted univariate polynomials. -/
theorem eval_natDegree_le (P : MvPolynomial Inc K) (values : Inc → Polynomial K)
    (bound : ℕ) (degrees : ∀ inc, (values inc).natDegree ≤ bound) :
    (P.eval₂ Polynomial.C values).natDegree ≤ P.totalDegree * bound := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  calc
    (∏ i ∈ d.support, values i ^ d i).natDegree ≤
        ∑ i ∈ d.support, (values i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i * bound := by
      apply Finset.sum_le_sum
      intro i _
      exact Polynomial.natDegree_pow_le_of_le _ (degrees i)
    _ = (∑ i ∈ d.support, d i) * bound := (Finset.sum_mul _ _ _).symm
    _ ≤ P.totalDegree * bound := Nat.mul_le_mul_right _ (MvPolynomial.le_totalDegree hd)

theorem expandedPolynomial_eval (ground : Finset Var) (P : MvPolynomial Inc K)
    (coeff : Inc → Var → Polynomial K) (node : K) (assigned support : Finset Var) :
    scaledEval (expandedPolynomial ground P coeff node assigned) Polynomial.X support =
      P.eval₂ Polynomial.C (fun inc =>
        scaledEval (correctedForm ground coeff node assigned inc) Polynomial.X support) := by
  let ev : MvPolynomial Var (Polynomial K) →+* Polynomial K :=
    MvPolynomial.eval₂Hom (RingHom.id _) (fun i => if i ∈ support then Polynomial.X else 0)
  change ev (P.eval₂ (MvPolynomial.C.comp Polynomial.C)
      (correctedForm ground coeff node assigned)) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  ext c
  simp [ev]

theorem correctedForm_degree (ground : Finset Var) (coeff : Inc → Var → Polynomial K)
    (node : K) (assigned support : Finset Var) (inc : Inc) (bound : ℕ)
    (degrees : ∀ i ∈ ground, (coeff inc i).natDegree ≤ bound) :
    (scaledEval (correctedForm ground coeff node assigned inc) Polynomial.X support).natDegree
      ≤ bound := by
  rw [correctedForm_eval]
  apply Polynomial.natDegree_add_le_of_degree_le (by simp)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  split_ifs
  · apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le (by simpa using degrees i hi) (by simp)
  · simp

theorem expandedPolynomial_degree (ground : Finset Var) (P : MvPolynomial Inc K)
    (coeff : Inc → Var → Polynomial K) (node : K) (assigned support : Finset Var)
    (bound : ℕ) (degrees : ∀ inc i, i ∈ ground → (coeff inc i).natDegree ≤ bound) :
    (scaledEval (expandedPolynomial ground P coeff node assigned) Polynomial.X support).natDegree
      ≤ P.totalDegree * bound := by
  rw [expandedPolynomial_eval]
  apply eval_natDegree_le
  intro inc
  exact correctedForm_degree ground coeff node assigned support inc bound (degrees inc)

theorem countingPolynomial_degree (ground : Finset Var) (P : MvPolynomial Inc K)
    (coeff : Inc → Var → Polynomial K) (bound : ℕ)
    (degrees : ∀ inc i, i ∈ ground → (coeff inc i).natDegree ≤ bound) :
    (countingPolynomial ground P coeff).natDegree ≤ P.totalDegree * bound := by
  unfold countingPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro assigned _
  apply eval_natDegree_le
  intro inc
  unfold linearValue
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  split_ifs
  · exact degrees inc i hi
  · simp

/-- The untruncated Taylor-data polynomial has the same degree bound as the
original counting polynomial; no truncation is hidden in its definition. -/
theorem taylorData_degree (ground : Finset Var) (P : MvPolynomial Inc K)
    (coeff : Inc → Var → Polynomial K) (node : K) (order bound : ℕ)
    (degrees : ∀ inc i, i ∈ ground → (coeff inc i).natDegree ≤ bound) :
    (taylorData ground (expandedPolynomial ground P coeff node) Polynomial.X order).natDegree
      ≤ P.totalDegree * bound := by
  unfold taylorData
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro support _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro subset _
  apply Polynomial.natDegree_mul_le.trans
  have hsign : ((-1 : Polynomial K) ^ (support.card - subset.card)).natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa using (Polynomial.natDegree_pow_le (p := (-1 : Polynomial K))
      (n := support.card - subset.card))
  rw [hsign, zero_add]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro assigned _
  split_ifs
  · exact expandedPolynomial_degree ground P coeff node assigned subset bound degrees
  · simp

end

end NtimeDspace.DeformationTaylor
