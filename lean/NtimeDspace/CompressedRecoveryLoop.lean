import NtimeDspace.ScalarRecoveryLoop
import NtimeDspace.CompressedTaylorLoop

/-!
# Recovery from the compressed grouped counting loops

The running procedure composes indexed scalar Hermite recovery with the
compressed support, exact-width subset, measurement, group, and assignment
loops. Its inputs are scalar accessors and finite index maps; polynomial and
finite-set constructions occur only in its refinement statements.

The concrete theorem derives the Taylor-data callback contract. Integer-row,
local-coefficient, measurement-coefficient, and incidence-polynomial evaluation
accessors still need concrete implementations satisfying the stated contracts.
Row numbering must be bijective. No machine-resource bound is asserted here.
-/

namespace NtimeDspace.CompressedRecoveryLoop

open scoped BigOperators
open GroupedDeformation ConcreteGroupedDeformation

variable {n Q groups rows coordinates p : ℕ} {Row : Type*} [Fact p.Prime]

/-- Entire arithmetic counting loop, with one node and one scalar point passed
to the compressed Taylor evaluator at a time. -/
def evaluate (formula : Formula n)
    (variableGroup : Fin Q → Fin n → Fin groups)
    (clauseGroup : Fin Q → Fin formula.clauses.length → Fin groups)
    (rowAt : Fin Q → Fin rows → Row)
    (rowNumber : Fin Q → (Σ _ : Fin groups, Row) → Fin coordinates)
    (bound k : ℕ) (nodeValue : Fin Q → ZMod p)
    (measurement : ∀ node g, Row → LocalVariable (variableGroup node) g → ℤ)
    (localCoefficient : Fin Q → FormulaCounter.Incidence formula → Fin n → ZMod p)
    (measurementCoefficient : Fin Q → FormulaCounter.Incidence formula → Fin groups → Row → ZMod p)
    (evaluateCoefficient : FormulaCounter.Incidence formula → Fin n → ZMod p → ZMod p) : ZMod p :=
  ScalarRecoveryLoop.recover nodeValue (Parameters.q n k + 1) (fun node point =>
    CompressedTaylorLoop.evaluate formula (variableGroup node) (clauseGroup node)
      (rowAt node) (rowNumber node) bound k (measurement node) (localCoefficient node)
      (measurementCoefficient node) evaluateCoefficient (nodeValue node) point)

section Concrete

variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
variable {start : ℤ} {width : ℕ}

set_option maxHeartbeats 1500000 in
/-- Concrete grouped-expression refinement. There is no assumed Taylor-data
equality or measurement norm premise: both are proved by composition. -/
theorem evaluate_eq_groupedScalarExpression
    (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label (Fin Q) groups)
    (variableGroup : Fin Q → Fin n → Fin groups)
    (clauseGroup : Fin Q → Fin formula.clauses.length → Fin groups)
    (rowAt : Fin Q → Fin rows → ConcreteGroupedDeformation.Row (Fin Q) Copy groups start width)
    (rows_bijective : ∀ node, Function.Bijective (rowAt node))
    (rowNumber : Fin Q →
      (Σ _ : Fin groups, ConcreteGroupedDeformation.Row (Fin Q) Copy groups start width) →
        Fin coordinates)
    (numbering : ∀ node, Function.Bijective (rowNumber node))
    (k : ℕ) (large : 6 ≤ k) (nodeValue : Fin Q → ZMod p)
    (distinct : Function.Injective nodeValue) (nonzero : ∀ node, nodeValue node ≠ 0)
    (within : Parameters.q n k + 1 ≤ p)
    (measurement : ∀ node g, ConcreteGroupedDeformation.Row (Fin Q) Copy groups start width →
      LocalVariable (variableGroup node) g → ℤ)
    (measurements_correct : ∀ node g row v, measurement node g row v =
      measurementRow (occupiedPositions copyOf labelOf)
        (storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
        (variableGroup node) start width g row v)
    (localCoefficient : Fin Q → FormulaCounter.Incidence formula → Fin n → ZMod p)
    (local_correct : ∀ node inc v, localCoefficient node inc v =
      formulaLocalCoefficient formula copyOf labelOf (occupiedPositions copyOf labelOf)
        (storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
        nodeValue start width node inc v)
    (measurementCoefficient : Fin Q → FormulaCounter.Incidence formula → Fin groups →
      ConcreteGroupedDeformation.Row (Fin Q) Copy groups start width → ZMod p)
    (coefficients_correct : ∀ node inc g row, measurementCoefficient node inc g row =
      formulaMeasurementCoefficient formula copyOf labelOf start width inc g row)
    (evaluateCoefficient : FormulaCounter.Incidence formula → Fin n → ZMod p → ZMod p)
    (evaluation : ∀ inc v x, evaluateCoefficient inc v x =
      ((FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)
        inc.1 inc.2 v).eval x) :
    evaluate formula variableGroup clauseGroup rowAt rowNumber (groups ^ (2 * Q)) k nodeValue
        measurement localCoefficient measurementCoefficient evaluateCoefficient =
      GroupedCounter.groupedScalarExpression formula fallback copyOf labelOf variableGroup
        clauseGroup nodeValue start width (Parameters.q n k + 1) := by
  classical
  have measurement_eq : measurement = fun node =>
      measurementRow (occupiedPositions copyOf labelOf)
        (storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
        (variableGroup node) start width := by
    funext node g row v
    exact measurements_correct node g row v
  have local_eq : localCoefficient = fun node =>
      formulaLocalCoefficient formula copyOf labelOf (occupiedPositions copyOf labelOf)
        (storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
        nodeValue start width node := by
    funext node inc v
    exact local_correct node inc v
  have coefficients_eq : measurementCoefficient = fun _node =>
      formulaMeasurementCoefficient formula copyOf labelOf start width := by
    funext node inc g row
    exact coefficients_correct node inc g row
  rw [measurement_eq, local_eq, coefficients_eq]
  unfold evaluate
  apply ScalarRecoveryLoop.recover_eq_groupedScalarExpression formula fallback copyOf labelOf
    variableGroup clauseGroup nodeValue distinct nonzero start width (Parameters.q n k + 1)
    (Nat.succ_pos _) within
  intro node point
  have norm : ∀ g row, (∑ v,
      |measurementRow (occupiedPositions copyOf labelOf)
        (storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
        (variableGroup node) start width g row v|) ≤ (groups ^ (2 * Q) : ℕ) := by
    intro g row
    simpa only [Fintype.card_fin] using measurementRow_norm (occupiedPositions copyOf labelOf)
      (storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
      (variableGroup node) start width g row
  have correct := CompressedTaylorLoop.evaluate_correct formula
    (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)
    (variableGroup node) (clauseGroup node) (rowAt node) (rows_bijective node)
    (rowNumber node) (numbering node) (groups ^ (2 * Q)) k large
    (measurementRow (occupiedPositions copyOf labelOf)
      (storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
      (variableGroup node) start width) norm
    (formulaLocalCoefficient formula copyOf labelOf (occupiedPositions copyOf labelOf)
      (storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
      nodeValue start width node)
    (formulaMeasurementCoefficient formula copyOf labelOf start width)
    evaluateCoefficient evaluation (nodeValue node) point
  simpa only [GroupedCounter.groupedNodePolynomial, Fintype.card_fin] using correct

end Concrete

end NtimeDspace.CompressedRecoveryLoop
