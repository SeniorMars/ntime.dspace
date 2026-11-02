import NtimeDspace.WeightedSystem
import NtimeDspace.WFiniteFieldCounter
import NtimeDspace.RestrictedMeasurements
import NtimeDspace.ConcreteGroupedDeformation
import NtimeDspace.WGroupedDeformation
import NtimeDspace.WFiniteFieldCounter

namespace NtimeDspace.WConcreteGroupedDeformation

noncomputable section

open NtimeDspace.ConcreteGroupedDeformation hiding formulaLocalCoefficient formulaMeasurementCoefficient formula_incidenceForm_eq_occupied formula_localRepresentation formula_localRepresentation_of_placement taylorData_eq_concrete_grouped
open NtimeDspace.GroupedDeformation hiding LocalRepresentation clausePolynomial_eval_congr expandedPolynomial_formula_eval factorPolynomial_eq_product_groupFactor groupFactor groupedFormulaSum groupedTaylorData grouped_formula_identity localInputs support_subset_iff_assignment taylorCorrection taylorData_eq_groupedTaylorData taylor_inner_eq_groupedFormulaSum
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open WGroupedDeformation
variable {Node Var Copy : Type*} [Fintype Node] [DecidableEq Node]
variable [Fintype Var] {r p : ℕ} [Fact p.Prime]
variable [Fintype Copy] [DecidableEq Copy]

section Formula

variable {n : ℕ}

def formulaLocalCoefficient (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label Node r)
    (occupied : Copy → Finset (Label Node r)) (variableAt : Copy → Label Node r → Fin n)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (inc : WeightedSystem.Incidence formula) (v : Fin n) : ZMod p :=
  localCoefficient (occupied (copyOf inc)) (variableAt (copyOf inc)) nodeValue start width node
    (labelOf inc) v

def formulaMeasurementCoefficient (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label Node r)
    (start : ℤ) (width : ℕ) (inc : WeightedSystem.Incidence formula)
    (group : Fin r) (row : Row Node Copy r start width) : ZMod p :=
  measurementCoefficient start width (copyOf inc) (labelOf inc) group row

omit [Fintype Copy] in
theorem formula_incidenceForm_eq_occupied (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (occupied : Copy → Finset (Label Node r))
    (occupied_eq : ∀ copy, occupied copy = (Finset.univ.filter (fun inc => copyOf inc = copy)).image labelOf)
    (variableAt : Copy → Label Node r → Fin n)
    (stored : ∀ inc, variableAt (copyOf inc) (labelOf inc) = WIncidenceDeformation.incidenceVariable formula inc)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ)
    (inc : WeightedSystem.Incidence formula) (assignment : Assignment n) :
    WeightedSystem.incidenceForm formula
        (WFiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width) inc.1 inc.2 assignment =
      ∑ w ∈ occupied (copyOf inc),
        FiniteFieldDeformation.coefficient nodeValue start width (labelOf inc) w *
          Polynomial.C (CountingPolynomial.boolValue (assignment (variableAt (copyOf inc) w))) := by
  rw [WFiniteFieldCounter.coefficients, WIncidenceDeformation.formula_incidenceForm_eq_occupied_sum]
  exact incidence_sum_eq_occupied copyOf labelOf (WIncidenceDeformation.incidenceVariable formula)
    placement occupied occupied_eq variableAt stored (copyOf inc)
    (fun w v => FiniteFieldDeformation.coefficient nodeValue start width (labelOf inc) w *
      Polynomial.C (CountingPolynomial.boolValue (assignment v)))

set_option maxHeartbeats 1000000 in
/-- D4 for the actual formula coefficients, derived from the spectral node
identity and the concrete integer rows. The assumptions are only the explicit
placement inverse and schedule-coordinate compatibility. -/
theorem formula_localRepresentation (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (occupied : Copy → Finset (Label Node r))
    (occupied_eq : ∀ copy, occupied copy = (Finset.univ.filter (fun inc => copyOf inc = copy)).image labelOf)
    (variableAt : Copy → Label Node r → Fin n)
    (stored : ∀ inc, variableAt (copyOf inc) (labelOf inc) = WIncidenceDeformation.incidenceVariable formula inc)
    (groupOf : Fin n → Fin r) (clauseGroup : Fin formula.constraints.length → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (nonzero : nodeValue node ≠ 0)
    (groups_match : ∀ copy w, w ∈ occupied copy → groupOf (variableAt copy w) = (w node).1)
    (clauses_match : ∀ inc, (labelOf inc node).2 = clauseGroup inc.1) :
    LocalRepresentation formula
      (WFiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)
      (nodeValue node) groupOf clauseGroup (r ^ (2 * Fintype.card Node))
      (measurementRow occupied variableAt groupOf start width)
      (measurementRow_norm occupied variableAt groupOf start width)
      (formulaLocalCoefficient formula copyOf labelOf occupied variableAt nodeValue start width node)
      (formulaMeasurementCoefficient formula copyOf labelOf start width) := by
  intro assignment inc
  rw [formula_incidenceForm_eq_occupied formula copyOf labelOf placement occupied occupied_eq
    variableAt stored nodeValue start width inc assignment]
  have h := occupied_localRepresentation occupied variableAt groupOf nodeValue start width node
    nonzero groups_match (copyOf inc) (labelOf inc) assignment
  let value := fun group => localLinearValue groupOf (r ^ (2 * Fintype.card Node))
    (formulaLocalCoefficient formula copyOf labelOf occupied variableAt nodeValue start width node)
    (formulaMeasurementCoefficient formula copyOf labelOf start width)
    group inc (partitionAssignmentEquiv groupOf assignment group)
    (measurements groupOf (r ^ (2 * Fintype.card Node))
      (measurementRow occupied variableAt groupOf start width)
      (measurementRow_norm occupied variableAt groupOf start width) assignment)
  change _ = value (clauseGroup inc.1)
  change _ = value (labelOf inc node).2 at h
  exact h.trans (congrArg value (clauses_match inc))

set_option maxHeartbeats 1000000 in
/-- The formula's complete Taylor-data polynomial equals the concrete grouped
sum. In particular, the former D4 premise is discharged, and every measurement
norm bound is supplied by the actual tensor rows. -/
theorem taylorData_eq_concrete_grouped (formula : WeightedSystem.System n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (occupied : Copy → Finset (Label Node r))
    (occupied_eq : ∀ copy, occupied copy = (Finset.univ.filter (fun inc => copyOf inc = copy)).image labelOf)
    (variableAt : Copy → Label Node r → Fin n)
    (stored : ∀ inc, variableAt (copyOf inc) (labelOf inc) = WIncidenceDeformation.incidenceVariable formula inc)
    (groupOf : Fin n → Fin r) (clauseGroup : Fin formula.constraints.length → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (nonzero : nodeValue node ≠ 0)
    (groups_match : ∀ copy w, w ∈ occupied copy → groupOf (variableAt copy w) = (w node).1)
    (clauses_match : ∀ inc, (labelOf inc node).2 = clauseGroup inc.1) (order : ℕ) :
    TaylorTruncation.taylorData Finset.univ
      (DeformationTaylor.expandedPolynomial Finset.univ (WeightedSystem.factorPolynomial formula)
        (WeightedSystem.coefficients formula
          (WFiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)) (nodeValue node))
      Polynomial.X order =
    groupedTaylorData formula
      (WFiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width) (nodeValue node)
      groupOf clauseGroup (r ^ (2 * Fintype.card Node))
      (measurementRow occupied variableAt groupOf start width)
      (measurementRow_norm occupied variableAt groupOf start width)
      (formulaLocalCoefficient formula copyOf labelOf occupied variableAt nodeValue start width node)
      (formulaMeasurementCoefficient formula copyOf labelOf start width) order := by
  apply WGroupedDeformation.taylorData_eq_groupedTaylorData
  exact formula_localRepresentation formula copyOf labelOf placement occupied occupied_eq
    variableAt stored groupOf clauseGroup nodeValue start width node nonzero groups_match clauses_match

set_option maxHeartbeats 1000000 in
/-- The occupied sets and stored-variable inverse can themselves be constructed
from injective placement. The only remaining schedule hypotheses are the two
label-coordinate identities. No D4 or inverse-accessor equality is assumed. -/
theorem formula_localRepresentation_of_placement (formula : WeightedSystem.System n) (fallback : Fin n)
    (copyOf : WeightedSystem.Incidence formula → Copy)
    (labelOf : WeightedSystem.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (groupOf : Fin n → Fin r) (clauseGroup : Fin formula.constraints.length → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (nonzero : nodeValue node ≠ 0)
    (variables_match : ∀ inc, groupOf (WIncidenceDeformation.incidenceVariable formula inc) = (labelOf inc node).1)
    (clauses_match : ∀ inc, (labelOf inc node).2 = clauseGroup inc.1) :
    let occupied := occupiedPositions copyOf labelOf
    let variableAt := storedVariable fallback (WIncidenceDeformation.incidenceVariable formula) copyOf labelOf
    LocalRepresentation formula
      (WFiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)
      (nodeValue node) groupOf clauseGroup (r ^ (2 * Fintype.card Node))
      (measurementRow occupied variableAt groupOf start width)
      (measurementRow_norm occupied variableAt groupOf start width)
      (formulaLocalCoefficient formula copyOf labelOf occupied variableAt nodeValue start width node)
      (formulaMeasurementCoefficient formula copyOf labelOf start width) := by
  dsimp only
  apply formula_localRepresentation formula copyOf labelOf placement
    (occupiedPositions copyOf labelOf) (fun _ => rfl)
    (storedVariable fallback (WIncidenceDeformation.incidenceVariable formula) copyOf labelOf)
    (storedVariable_at fallback (WIncidenceDeformation.incidenceVariable formula) copyOf labelOf placement)
    groupOf clauseGroup nodeValue start width node nonzero
  · exact occupiedPositions_groups_match fallback (WIncidenceDeformation.incidenceVariable formula)
      copyOf labelOf placement groupOf node variables_match
  · exact clauses_match

end Formula

end

end NtimeDspace.WConcreteGroupedDeformation
