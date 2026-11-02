import NtimeDspace.PolynomialFacts
import NtimeDspace.Counting
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.List.OfFn

/-!
The manuscript's actual clause-polynomial indicator and count at the origin.
The algebra works over every commutative ring. Deformation coefficients are
indexed by clause position, literal position, and declared variable, so separate
incidences can use distinct forms even if they involve the same variable.

The origin identity is proved from the Kronecker-delta coefficients; it is not
an assumed correctness statement. Every declared Boolean assignment is summed,
including values for unused variables. Empty clauses contribute zero. No
deformation degree bound or machine resource theorem is asserted here.
-/

namespace NtimeDspace.CountingPolynomial

open scoped BigOperators

variable {K : Type*} [CommRing K]

def boolValue (b : Bool) : K := if b then 1 else 0

/-- A literal is x for positive polarity, and 1-x for negative polarity. -/
def literalValue {n : ℕ} (literal : Literal n) (values : Fin n → K) : K :=
  if literal.positive then values literal.index else 1 - values literal.index

def clauseValue {n : ℕ} (clause : Clause n) (values : Fin n → K) : K :=
  1 - (clause.literals.map fun literal => 1 - literalValue literal values).prod

def formulaValue {n : ℕ} (formula : Formula n) (values : Fin n → K) : K :=
  (formula.clauses.map fun clause => clauseValue clause values).prod

theorem literalValue_bool {n : ℕ} (literal : Literal n) (assignment : Assignment n) :
    literalValue literal (fun v => boolValue (assignment v)) =
      (boolValue (literal.eval assignment) : K) := by
  cases hp : literal.positive <;> cases hv : assignment literal.index <;>
    simp [literalValue, Literal.eval, boolValue, hp, hv]

theorem complement_product_bool {α : Type*} (values : List α) (truth : α → Bool) :
    1 - (values.map fun value => 1 - (boolValue (truth value) : K)).prod =
      boolValue (values.any truth) := by
  induction values with
  | nil => simp [boolValue]
  | cons value values ih =>
    cases h : truth value <;> simp [h, boolValue] at *
    exact ih

theorem product_bool {α : Type*} (values : List α) (truth : α → Bool) :
    (values.map fun value => (boolValue (truth value) : K)).prod =
      boolValue (values.all truth) := by
  induction values with
  | nil => simp [boolValue]
  | cons value values ih =>
    cases h : truth value <;> simp [h, boolValue] at *
    exact ih

theorem clauseValue_bool {n : ℕ} (clause : Clause n) (assignment : Assignment n) :
    clauseValue clause (fun v => boolValue (assignment v)) =
      (boolValue (clause.eval assignment) : K) := by
  simp only [clauseValue, literalValue_bool, Clause.eval]
  exact complement_product_bool clause.literals (fun literal => literal.eval assignment)

theorem formulaValue_bool {n : ℕ} (formula : Formula n) (assignment : Assignment n) :
    formulaValue formula (fun v => boolValue (assignment v)) =
      (boolValue (formula.eval assignment) : K) := by
  simp only [formulaValue, clauseValue_bool, Formula.eval]
  exact product_bool formula.clauses (fun clause => clause.eval assignment)

theorem clauseValue_empty {n : ℕ} (clause : Clause n) (empty : clause.literals = [])
    (values : Fin n → K) : clauseValue clause values = 0 := by
  simp [clauseValue, empty]

/-- Direct algebraic counting identity against the independent CNF count. -/
theorem sum_formulaValue_eq_count {n : ℕ} (formula : Formula n) :
    (∑ assignment : Assignment n,
      formulaValue formula (fun v => boolValue (assignment v))) =
      (satisfyingCount formula : K) := by
  rw [satisfyingCount_eq_sum]
  simp only [Nat.cast_sum, Formula.contribution, formulaValue_bool]
  apply Finset.sum_congr rfl
  intro assignment _
  cases formula.eval assignment <;> simp [boolValue]

noncomputable section

/-- Positions rather than literal identities distinguish the incidences. -/
abbrev Coefficients {n : ℕ} (formula : Formula n) (K : Type*) [CommRing K] :=
  (clause : Fin formula.clauses.length) →
    Fin (formula.clauses[clause]).literals.length → Fin n → Polynomial K

def incidenceForm {n : ℕ} (formula : Formula n) (L : Coefficients formula K)
    (clause : Fin formula.clauses.length)
    (literal : Fin (formula.clauses[clause]).literals.length)
    (assignment : Assignment n) : Polynomial K :=
  ∑ v, L clause literal v * Polynomial.C (boolValue (assignment v))

def deformedLiteral {n : ℕ} (formula : Formula n) (L : Coefficients formula K)
    (clause : Fin formula.clauses.length)
    (literal : Fin (formula.clauses[clause]).literals.length)
    (assignment : Assignment n) : Polynomial K :=
  if ((formula.clauses[clause]).literals[literal]).positive then
    incidenceForm formula L clause literal assignment
  else 1 - incidenceForm formula L clause literal assignment

def deformedClause {n : ℕ} (formula : Formula n) (L : Coefficients formula K)
    (clause : Fin formula.clauses.length) (assignment : Assignment n) : Polynomial K :=
  1 - ∏ literal : Fin (formula.clauses[clause]).literals.length,
    (1 - deformedLiteral formula L clause literal assignment)

def deformedFormula {n : ℕ} (formula : Formula n) (L : Coefficients formula K)
    (assignment : Assignment n) : Polynomial K :=
  ∏ clause : Fin formula.clauses.length, deformedClause formula L clause assignment

/-- The counting polynomial H(T), evaluated on all declared Boolean assignments. -/
def countingPolynomial {n : ℕ} (formula : Formula n) (L : Coefficients formula K) :
    Polynomial K :=
  ∑ assignment : Assignment n, deformedFormula formula L assignment

/-- The incidence form is the original variable at parameter zero. -/
def OriginCondition {n : ℕ} (formula : Formula n) (L : Coefficients formula K) : Prop :=
  ∀ clause literal v, (L clause literal v).eval 0 =
    if v = ((formula.clauses[clause]).literals[literal]).index then 1 else 0

theorem incidenceForm_origin {n : ℕ} (formula : Formula n) (L : Coefficients formula K)
    (origin : OriginCondition formula L)
    (clause : Fin formula.clauses.length)
    (literal : Fin (formula.clauses[clause]).literals.length)
    (assignment : Assignment n) :
    (incidenceForm formula L clause literal assignment).eval 0 =
      (boolValue (assignment ((formula.clauses[clause]).literals[literal]).index) : K) := by
  unfold OriginCondition at origin
  simp [incidenceForm, NtimeDspace.PolynomialFacts.eval_finset_sum, origin]

theorem deformedLiteral_origin {n : ℕ} (formula : Formula n) (L : Coefficients formula K)
    (origin : OriginCondition formula L)
    (clause : Fin formula.clauses.length)
    (literal : Fin (formula.clauses[clause]).literals.length)
    (assignment : Assignment n) :
    (deformedLiteral formula L clause literal assignment).eval 0 =
      literalValue ((formula.clauses[clause]).literals[literal])
        (fun v => (boolValue (assignment v) : K)) := by
  unfold deformedLiteral literalValue
  split_ifs <;> simp [incidenceForm_origin formula L origin]

theorem prod_positions_eq_list {α : Type*} (values : List α) (weight : α → K) :
    (∏ position : Fin values.length, weight values[position]) =
      (values.map weight).prod := by
  rw [← List.prod_ofFn]
  change (List.ofFn (fun position : Fin values.length => weight values[(position : ℕ)])).prod = _
  rw [List.ofFn_getElem_eq_map]

theorem deformedClause_origin {n : ℕ} (formula : Formula n) (L : Coefficients formula K)
    (origin : OriginCondition formula L)
    (clause : Fin formula.clauses.length) (assignment : Assignment n) :
    (deformedClause formula L clause assignment).eval 0 =
      clauseValue formula.clauses[clause] (fun v => (boolValue (assignment v) : K)) := by
  simp only [deformedClause, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_prod, deformedLiteral_origin formula L origin]
  unfold clauseValue
  congr 1
  exact prod_positions_eq_list (formula.clauses[clause]).literals
    (fun literal => 1 - literalValue literal (fun v => boolValue (assignment v)))

theorem deformedFormula_origin {n : ℕ} (formula : Formula n) (L : Coefficients formula K)
    (origin : OriginCondition formula L) (assignment : Assignment n) :
    (deformedFormula formula L assignment).eval 0 =
      formulaValue formula (fun v => (boolValue (assignment v) : K)) := by
  simp only [deformedFormula, Polynomial.eval_prod,
    deformedClause_origin formula L origin]
  exact prod_positions_eq_list formula.clauses
    (fun clause => clauseValue clause (fun v => boolValue (assignment v)))

/-- The actual deformation counting polynomial has the satisfying-assignment
count at the origin, using only the explicit incidence origin condition. -/
theorem countingPolynomial_origin {n : ℕ} (formula : Formula n) (L : Coefficients formula K)
    (origin : OriginCondition formula L) :
    (countingPolynomial formula L).eval 0 = (satisfyingCount formula : K) := by
  simp only [countingPolynomial, NtimeDspace.PolynomialFacts.eval_finset_sum,
    deformedFormula_origin formula L origin]
  exact sum_formulaValue_eq_count formula

end

end NtimeDspace.CountingPolynomial
