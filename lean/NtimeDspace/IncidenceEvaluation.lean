import NtimeDspace.GroupedAssignmentEvaluation
import NtimeDspace.IncidenceDeformation
import NtimeDspace.FiniteFieldCounter
import NtimeDspace.DeformationEvaluation

/-!
Scalar clause/literal scans for the formula's incidence coefficients. The
executing procedures read the existing formula lists and retain scalar sums.
They do not construct a list of all incidences, a finite set of incidences, or
a polynomial. Every literal position is visited independently, so repeated
occurrences contribute separately; an empty clause contributes no incidence.

Copy and label accessors, formula input parsing, label-coefficient evaluation,
and machine time/space costs are separate interfaces. Polynomial expressions
below serve only as specifications of the scalar coefficient values.
-/

namespace NtimeDspace.IncidenceEvaluation

open scoped BigOperators
open GroupedAssignmentEvaluation

variable {n : ℕ}

/-- Two nested scalar counters visit exactly the formula's clause/literal
positions. Only the formula's original lists are accessed. -/
def scanIncidences {R : Type*} [AddMonoid R] (formula : Formula n)
    (term : FormulaCounter.Incidence formula → R) (accumulator : R) : R :=
  scanSum (fun clause : Fin formula.clauses.length =>
    scanSum (fun literal : Fin (formula.clauses[clause]).literals.length =>
      term ⟨clause, literal⟩) 0) accumulator

theorem scanIncidences_correct {R : Type*} [AddCommMonoid R] (formula : Formula n)
    (term : FormulaCounter.Incidence formula → R) (accumulator : R) :
    scanIncidences formula term accumulator =
      (∑ inc : FormulaCounter.Incidence formula, term inc) + accumulator := by
  simp only [scanIncidences, scanSum_correct, add_zero]
  rw [Fintype.sum_sigma]

/-- Numeric formula-variable access, without relying on a noncomputable
polynomial construction to retrieve the literal's declared index. -/
def variableOf (formula : Formula n) (inc : FormulaCounter.Incidence formula) : Fin n :=
  (formula.clauses[inc.1].literals[inc.2]).index

theorem variableOf_eq (formula : Formula n) (inc : FormulaCounter.Incidence formula) :
    variableOf formula inc = IncidenceDeformation.incidenceVariable formula inc := rfl

variable {Copy Label K : Type*} [DecidableEq Copy] [CommRing K]

/-- Sum exactly those occupied positions in the same copy that carry the
requested variable. No sign is applied here: literal polarity belongs to the
clause polynomial, while this coefficient substitutes variable values. -/
def coefficientValue (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label)
    (labelCoefficient : Label → Label → K)
    (inc : FormulaCounter.Incidence formula) (v : Fin n) : K :=
  scanIncidences formula (fun other =>
    if copyOf other = copyOf inc ∧ variableOf formula other = v then
      labelCoefficient (labelOf inc) (labelOf other) else 0) 0

theorem coefficientValue_eq_sum (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label)
    (labelCoefficient : Label → Label → K)
    (inc : FormulaCounter.Incidence formula) (v : Fin n) :
    coefficientValue formula copyOf labelOf labelCoefficient inc v =
      ∑ other : FormulaCounter.Incidence formula,
        if copyOf other = copyOf inc ∧ variableOf formula other = v then
          labelCoefficient (labelOf inc) (labelOf other) else 0 := by
  simp only [coefficientValue, scanIncidences_correct, add_zero]

/-- The scalar occupied-position sum agrees with the actual incidence
coefficient polynomial whenever its label-value accessor is correct. -/
theorem coefficientValue_correct (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label)
    (coefficient : Label → Label → Polynomial K)
    (labelCoefficient : Label → Label → K) (point : K)
    (agrees : ∀ first second, labelCoefficient first second = (coefficient first second).eval point)
    (inc : FormulaCounter.Incidence formula) (v : Fin n) :
    coefficientValue formula copyOf labelOf labelCoefficient inc v =
      (IncidenceDeformation.incidenceCoefficient
        (IncidenceDeformation.incidenceVariable formula) copyOf labelOf coefficient inc v).eval point := by
  rw [coefficientValue_eq_sum, IncidenceDeformation.incidenceCoefficient,
    PolynomialFacts.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro other _
  rw [variableOf_eq]
  by_cases selected : copyOf other = copyOf inc ∧
      IncidenceDeformation.incidenceVariable formula other = v
  · simp only [ite_eq_left selected, agrees]
  · simp only [ite_eq_right selected, Polynomial.eval_zero]

/-- Coefficient-value accessor in the incidence/variable/point order used by
the sparse Taylor correction and compressed counting loops. -/
def evaluate (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label)
    (evaluateLabel : Label → Label → K → K)
    (inc : FormulaCounter.Incidence formula) (v : Fin n) (point : K) : K :=
  coefficientValue formula copyOf labelOf (fun first second => evaluateLabel first second point) inc v

theorem evaluate_correct (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label)
    (coefficient : Label → Label → Polynomial K)
    (evaluateLabel : Label → Label → K → K)
    (agrees : ∀ first second point,
      evaluateLabel first second point = (coefficient first second).eval point)
    (inc : FormulaCounter.Incidence formula) (v : Fin n) (point : K) :
    evaluate formula copyOf labelOf evaluateLabel inc v point =
      (IncidenceDeformation.formulaCoefficients formula copyOf labelOf coefficient
        inc.1 inc.2 v).eval point :=
  coefficientValue_correct formula copyOf labelOf coefficient
    (fun first second => evaluateLabel first second point) point
    (fun first second => agrees first second point) inc v

section FiniteField

variable (p : ℕ) [Fact p.Prime] {r Q : ℕ}

/-- Fully scalar finite-field coefficient access. The spectral label routine
is numeric too; no polynomial-evaluation oracle remains in this wrapper. -/
def finiteField (positive : 0 < r) (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (nodeValue : Fin Q → ZMod p) (start : ℤ) (width : ℕ)
    (inc : FormulaCounter.Incidence formula) (v : Fin n) (point : ZMod p) : ZMod p :=
  evaluate formula copyOf labelOf
    (DeformationEvaluation.coefficient p positive nodeValue start width) inc v point

/-- The actual `FiniteFieldCounter.coefficients` accessor contract, discharged
by explicit clause/literal and spectral arithmetic scans. Copy, label, and node
accessors are still supplied inputs; their construction and costs are separate. -/
theorem finiteField_correct (positive : 0 < r) (two_nonzero : (2 : ZMod p) ≠ 0)
    (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (nodeValue : Fin Q → ZMod p) (start : ℤ) (width : ℕ) (small : width < p)
    (inc : FormulaCounter.Incidence formula) (v : Fin n) (point : ZMod p) :
    finiteField p positive formula copyOf labelOf nodeValue start width inc v point =
      (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width
        inc.1 inc.2 v).eval point :=
  evaluate_correct formula copyOf labelOf
    (FiniteFieldDeformation.coefficient nodeValue start width)
    (DeformationEvaluation.coefficient p positive nodeValue start width)
    (DeformationEvaluation.coefficient_correct p positive two_nonzero nodeValue start width small)
    inc v point

end FiniteField

end NtimeDspace.IncidenceEvaluation
