import NtimeDspace.WeightedSystem
import NtimeDspace.WSchedulePlacement
import NtimeDspace.WGroupedAssignmentEvaluation
import NtimeDspace.WIncidenceDeformation
import NtimeDspace.WFiniteFieldCounter
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

namespace NtimeDspace.WIncidenceEvaluation

open scoped BigOperators
open WGroupedAssignmentEvaluation

variable {n : ℕ}

/-- Two nested scalar counters visit exactly the formula's clause/literal
positions. Only the formula's original lists are accessed. -/
def scanIncidences {R : Type*} [AddMonoid R] (formula : WeightedSystem.System n)
    (term : WeightedSystem.Incidence formula → R) (accumulator : R) : R :=
  scanSum (fun clause : Fin formula.constraints.length =>
    scanSum (fun literal : Fin (formula.constraints[clause]).scope.length =>
      term ⟨clause, literal⟩) 0) accumulator

theorem scanIncidences_correct {R : Type*} [AddCommMonoid R] (formula : WeightedSystem.System n)
    (term : WeightedSystem.Incidence formula → R) (accumulator : R) :
    scanIncidences formula term accumulator =
      (∑ inc : WeightedSystem.Incidence formula, term inc) + accumulator := by
  simp only [scanIncidences, scanSum_correct, add_zero]
  rw [Fintype.sum_sigma]

/-- Numeric formula-variable access, without relying on a noncomputable
polynomial construction to retrieve the literal's declared index. -/
def variableOf (formula : WeightedSystem.System n) (inc : WeightedSystem.Incidence formula) : Fin n :=
  (formula.constraints[inc.1]).scope[inc.2]

theorem variableOf_eq (formula : WeightedSystem.System n) (inc : WeightedSystem.Incidence formula) :
    variableOf formula inc = WIncidenceDeformation.incidenceVariable formula inc := rfl

variable {Copy Label K : Type*} [DecidableEq Copy] [CommRing K]

/-- Sum exactly those occupied positions in the same copy that carry the
requested variable. No sign is applied here: literal polarity belongs to the
clause polynomial, while this coefficient substitutes variable values. -/
def coefficientValue (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label)
    (labelCoefficient : Label → Label → K)
    (inc : WeightedSystem.Incidence formula) (v : Fin n) : K :=
  scanIncidences formula (fun other =>
    if copyOf other = copyOf inc ∧ variableOf formula other = v then
      labelCoefficient (labelOf inc) (labelOf other) else 0) 0

theorem coefficientValue_eq_sum (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label)
    (labelCoefficient : Label → Label → K)
    (inc : WeightedSystem.Incidence formula) (v : Fin n) :
    coefficientValue formula copyOf labelOf labelCoefficient inc v =
      ∑ other : WeightedSystem.Incidence formula,
        if copyOf other = copyOf inc ∧ variableOf formula other = v then
          labelCoefficient (labelOf inc) (labelOf other) else 0 := by
  simp only [coefficientValue, scanIncidences_correct, add_zero]

/-- The scalar occupied-position sum agrees with the actual incidence
coefficient polynomial whenever its label-value accessor is correct. -/
theorem coefficientValue_correct (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label)
    (coefficient : Label → Label → Polynomial K)
    (labelCoefficient : Label → Label → K) (point : K)
    (agrees : ∀ first second, labelCoefficient first second = (coefficient first second).eval point)
    (inc : WeightedSystem.Incidence formula) (v : Fin n) :
    coefficientValue formula copyOf labelOf labelCoefficient inc v =
      (WIncidenceDeformation.incidenceCoefficient
        (WIncidenceDeformation.incidenceVariable formula) copyOf labelOf coefficient inc v).eval point := by
  rw [coefficientValue_eq_sum, WIncidenceDeformation.incidenceCoefficient,
    PolynomialFacts.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro other _
  rw [variableOf_eq]
  by_cases selected : copyOf other = copyOf inc ∧
      WIncidenceDeformation.incidenceVariable formula other = v
  · simp only [ite_eq_left selected, agrees]
  · simp only [ite_eq_right selected, Polynomial.eval_zero]

/-- Coefficient-value accessor in the incidence/variable/point order used by
the sparse Taylor correction and compressed counting loops. -/
def evaluate (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label)
    (evaluateLabel : Label → Label → K → K)
    (inc : WeightedSystem.Incidence formula) (v : Fin n) (point : K) : K :=
  coefficientValue formula copyOf labelOf (fun first second => evaluateLabel first second point) inc v

theorem evaluate_correct (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label)
    (coefficient : Label → Label → Polynomial K)
    (evaluateLabel : Label → Label → K → K)
    (agrees : ∀ first second point,
      evaluateLabel first second point = (coefficient first second).eval point)
    (inc : WeightedSystem.Incidence formula) (v : Fin n) (point : K) :
    evaluate formula copyOf labelOf evaluateLabel inc v point =
      (WIncidenceDeformation.formulaCoefficients formula copyOf labelOf coefficient
        inc.1 inc.2 v).eval point :=
  coefficientValue_correct formula copyOf labelOf coefficient
    (fun first second => evaluateLabel first second point) point
    (fun first second => agrees first second point) inc v

section FiniteField

variable (p : ℕ) [Fact p.Prime] {r Q : ℕ}

/-- Fully scalar finite-field coefficient access. The spectral label routine
is numeric too; no polynomial-evaluation oracle remains in this wrapper. -/
def finiteField (positive : 0 < r) (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → TensorEvaluation.Label r Q)
    (nodeValue : Fin Q → ZMod p) (start : ℤ) (width : ℕ)
    (inc : WeightedSystem.Incidence formula) (v : Fin n) (point : ZMod p) : ZMod p :=
  evaluate formula copyOf labelOf
    (DeformationEvaluation.coefficient p positive nodeValue start width) inc v point

/-- The actual `WFiniteFieldCounter.coefficients` accessor contract, discharged
by explicit clause/literal and spectral arithmetic scans. Copy, label, and node
accessors are still supplied inputs; their construction and costs are separate. -/
theorem finiteField_correct (positive : 0 < r) (two_nonzero : (2 : ZMod p) ≠ 0)
    (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → TensorEvaluation.Label r Q)
    (nodeValue : Fin Q → ZMod p) (start : ℤ) (width : ℕ) (small : width < p)
    (inc : WeightedSystem.Incidence formula) (v : Fin n) (point : ZMod p) :
    finiteField p positive formula copyOf labelOf nodeValue start width inc v point =
      (WFiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width
        inc.1 inc.2 v).eval point :=
  evaluate_correct formula copyOf labelOf
    (FiniteFieldDeformation.coefficient nodeValue start width)
    (DeformationEvaluation.coefficient p positive nodeValue start width)
    (DeformationEvaluation.coefficient_correct p positive two_nonzero nodeValue start width small)
    inc v point

end FiniteField

end NtimeDspace.WIncidenceEvaluation
