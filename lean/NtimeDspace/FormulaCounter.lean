import NtimeDspace.CountingPolynomial
import NtimeDspace.AlgebraicCounter
import Mathlib.Data.Fintype.Powerset

/-!
The concrete CNF incidence polynomial connects the generic deformation and
scalar recovery theorems to the independently defined satisfying-assignment
count. Every declared variable is included in the subset/assignment bijection.

The scalar expression is still a finite algebraic specification. The incidence
coefficients, origin condition, degree bound, and interpolation parameters must
be supplied. This module does not construct the manuscript's spectral forms or
assert a machine-space bound.
-/

namespace NtimeDspace.FormulaCounter

noncomputable section

open scoped BigOperators

variable {K : Type*} [CommRing K]

/-- Distinct occurrences of the same literal have distinct incidence indices. -/
abbrev Incidence {n : ℕ} (formula : Formula n) :=
  (clause : Fin formula.clauses.length) ×
    Fin (formula.clauses[clause]).literals.length

def literalPolynomial {n : ℕ} (formula : Formula n) (inc : Incidence formula) :
    MvPolynomial (Incidence formula) K :=
  if (formula.clauses[inc.1].literals[inc.2]).positive then MvPolynomial.X inc
  else 1 - MvPolynomial.X inc

def clausePolynomial {n : ℕ} (formula : Formula n)
    (clause : Fin formula.clauses.length) : MvPolynomial (Incidence formula) K :=
  1 - ∏ literal : Fin (formula.clauses[clause]).literals.length,
    (1 - literalPolynomial formula ⟨clause, literal⟩)

def factorPolynomial {n : ℕ} (formula : Formula n) :
    MvPolynomial (Incidence formula) K :=
  ∏ clause : Fin formula.clauses.length, clausePolynomial formula clause

def coefficients {n : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) :
    Incidence formula → Fin n → Polynomial K :=
  fun inc v => L inc.1 inc.2 v

def assignmentOfSupport {n : ℕ} (support : Finset (Fin n)) : Assignment n :=
  fun v => decide (v ∈ support)

def supportOfAssignment {n : ℕ} (assignment : Assignment n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => assignment v = true)

def supportAssignmentEquiv (n : ℕ) : Finset (Fin n) ≃ Assignment n where
  toFun := assignmentOfSupport
  invFun := supportOfAssignment
  left_inv support := by ext v; simp [supportOfAssignment, assignmentOfSupport]
  right_inv assignment := by
    funext v
    cases h : assignment v <;> simp [supportOfAssignment, assignmentOfSupport, h]

theorem linearValue_eq_incidenceForm {n : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (support : Finset (Fin n))
    (inc : Incidence formula) :
    DeformationTaylor.linearValue Finset.univ (coefficients formula L) support inc =
      CountingPolynomial.incidenceForm formula L inc.1 inc.2
        (assignmentOfSupport support) := by
  simp only [DeformationTaylor.linearValue, CountingPolynomial.incidenceForm,
    coefficients]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ support <;>
    simp [assignmentOfSupport, CountingPolynomial.boolValue, hv]

theorem literalPolynomial_eval {n : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (support : Finset (Fin n))
    (inc : Incidence formula) :
    (literalPolynomial formula inc).eval₂ Polynomial.C
        (DeformationTaylor.linearValue Finset.univ (coefficients formula L) support) =
      CountingPolynomial.deformedLiteral formula L inc.1 inc.2
        (assignmentOfSupport support) := by
  unfold literalPolynomial CountingPolynomial.deformedLiteral
  split_ifs <;> simp [linearValue_eq_incidenceForm]

theorem clausePolynomial_eval {n : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (support : Finset (Fin n))
    (clause : Fin formula.clauses.length) :
    (clausePolynomial formula clause).eval₂ Polynomial.C
        (DeformationTaylor.linearValue Finset.univ (coefficients formula L) support) =
      CountingPolynomial.deformedClause formula L clause (assignmentOfSupport support) := by
  simp only [clausePolynomial, CountingPolynomial.deformedClause,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, MvPolynomial.eval₂_prod,
    literalPolynomial_eval]

theorem factorPolynomial_eval {n : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (support : Finset (Fin n)) :
    (factorPolynomial formula).eval₂ Polynomial.C
        (DeformationTaylor.linearValue Finset.univ (coefficients formula L) support) =
      CountingPolynomial.deformedFormula formula L (assignmentOfSupport support) := by
  simp only [factorPolynomial, CountingPolynomial.deformedFormula,
    MvPolynomial.eval₂_prod, clausePolynomial_eval]

/-- The full subset sum and the full Boolean-assignment sum are exactly equal. -/
theorem countingPolynomial_eq {n : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) :
    DeformationTaylor.countingPolynomial Finset.univ (factorPolynomial formula)
        (coefficients formula L) = CountingPolynomial.countingPolynomial formula L := by
  simp only [DeformationTaylor.countingPolynomial, Finset.powerset_univ,
    factorPolynomial_eval, CountingPolynomial.countingPolynomial]
  exact (supportAssignmentEquiv n).sum_comp (CountingPolynomial.deformedFormula formula L)

/-- The number of literal occurrences, counting repeated literals separately. -/
def incidenceCount {n : ℕ} (formula : Formula n) : ℕ :=
  ∑ clause : Fin formula.clauses.length, (formula.clauses[clause]).literals.length

theorem literalPolynomial_degree {n : ℕ} (formula : Formula n)
    (inc : Incidence formula) :
    (literalPolynomial (K := K) formula inc).totalDegree ≤ 1 := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · letI := hK
    have hz : literalPolynomial (K := K) formula inc = 0 := Subsingleton.elim _ _
    rw [hz, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  letI := hK
  unfold literalPolynomial
  split_ifs
  · simp
  · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)

/-- A finite product's total degree is bounded by the sum of factor degrees. -/
theorem totalDegree_product {I Var : Type*} (set : Finset I)
    (factor : I → MvPolynomial Var K) :
    (∏ i ∈ set, factor i).totalDegree ≤ ∑ i ∈ set, (factor i).totalDegree := by
  classical
  induction set using Finset.induction_on with
  | empty => simp
  | @insert i set hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

theorem clausePolynomial_degree {n : ℕ} (formula : Formula n)
    (clause : Fin formula.clauses.length) :
    (clausePolynomial (K := K) formula clause).totalDegree ≤
      (formula.clauses[clause]).literals.length := by
  unfold clausePolynomial
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  simp only [MvPolynomial.totalDegree_one, zero_le, max_eq_right]
  refine (totalDegree_product _ _).trans ?_
  calc
    _ ≤ ∑ _literal : Fin (formula.clauses[clause]).literals.length, 1 := by
      apply Finset.sum_le_sum
      intro literal _
      exact (MvPolynomial.totalDegree_sub _ _).trans
        (max_le (by simp) (literalPolynomial_degree formula ⟨clause, literal⟩))
    _ = _ := by simp

theorem factorPolynomial_degree {n : ℕ} (formula : Formula n) :
    (factorPolynomial (K := K) formula).totalDegree ≤ incidenceCount formula := by
  refine (totalDegree_product _ _).trans ?_
  exact Finset.sum_le_sum (fun clause _ => clausePolynomial_degree formula clause)

theorem incidenceCount_le_three_clauses {n : ℕ} (formula : Formula n) :
    incidenceCount formula ≤ 3 * formula.clauses.length := by
  calc
    _ ≤ ∑ _clause : Fin formula.clauses.length, 3 :=
      Finset.sum_le_sum (fun clause _ => (formula.clauses[clause]).width_le_three)
    _ = _ := by simp [Nat.mul_comm]

variable {p : ℕ} [Fact p.Prime]

def scalarFormulaExpression {n : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula (ZMod p))
    (nodes : Finset (ZMod p)) (order : ℕ) : ZMod p :=
  AlgebraicCounter.scalarExpression Finset.univ (factorPolynomial formula)
    (coefficients formula L) nodes order

/-- Scalar recovery of the actual CNF count, with degree hypotheses stated
using the concrete factor polynomial. -/
theorem scalarFormulaExpression_correct {n : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula (ZMod p))
    (origin : CountingPolynomial.OriginCondition formula L)
    (nodes : Finset (ZMod p)) (order bound : ℕ)
    (positive : 0 < order) (below_prime : order < p)
    (nonzero_nodes : ∀ node ∈ nodes, node ≠ 0)
    (degrees : ∀ clause literal v, (L clause literal v).natDegree ≤ bound)
    (interpolation_capacity :
      (factorPolynomial (K := ZMod p) formula).totalDegree * bound < nodes.card * order)
    (no_alias : (factorPolynomial (K := ZMod p) formula).totalDegree * bound ≤ p - 2) :
    scalarFormulaExpression formula L nodes order = (satisfyingCount formula : ZMod p) := by
  unfold scalarFormulaExpression
  rw [AlgebraicCounter.scalarExpression_correct Finset.univ (factorPolynomial formula)
    (coefficients formula L) nodes order bound positive below_prime nonzero_nodes
    (fun inc v _ => degrees inc.1 inc.2 v) interpolation_capacity no_alias,
    countingPolynomial_eq]
  exact CountingPolynomial.countingPolynomial_origin formula L origin

/-- A simpler sufficient condition uses the proved literal-incidence degree
bound, so no separate factor-polynomial degree premise remains. Degree bounds
for the supplied deformation coefficients are still explicit hypotheses. -/
theorem scalarFormulaExpression_correct_of_incidence_budget {n : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula (ZMod p))
    (origin : CountingPolynomial.OriginCondition formula L)
    (nodes : Finset (ZMod p)) (order bound : ℕ)
    (positive : 0 < order) (below_prime : order < p)
    (nonzero_nodes : ∀ node ∈ nodes, node ≠ 0)
    (degrees : ∀ clause literal v, (L clause literal v).natDegree ≤ bound)
    (interpolation_capacity : incidenceCount formula * bound < nodes.card * order)
    (no_alias : incidenceCount formula * bound ≤ p - 2) :
    scalarFormulaExpression formula L nodes order = (satisfyingCount formula : ZMod p) := by
  apply scalarFormulaExpression_correct formula L origin nodes order bound
    positive below_prime nonzero_nodes degrees
  · exact (Nat.mul_le_mul_right bound (factorPolynomial_degree formula)).trans_lt
      interpolation_capacity
  · exact (Nat.mul_le_mul_right bound (factorPolynomial_degree formula)).trans no_alias

end

end NtimeDspace.FormulaCounter
