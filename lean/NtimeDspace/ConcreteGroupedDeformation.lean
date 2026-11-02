import NtimeDspace.FiniteFieldCounter
import NtimeDspace.RestrictedMeasurements

/-!
# Concrete restricted measurements and node representations

The local representation is derived from the constructed spectral polynomial.
Integer measurement rows aggregate repeated variables and have norm at most
the label-space dimension. All position-to-variable compatibility conditions
are explicit; no D4 equality or resource bound is assumed.
-/

namespace NtimeDspace.ConcreteGroupedDeformation

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open GroupedDeformation

variable {Node Var Copy : Type*} [Fintype Node] [DecidableEq Node]
variable [Fintype Var] {r p : ℕ} [Fact p.Prime]

abbrev Label (Node : Type*) (r : ℕ) := FiniteFieldDeformation.Label Node r

def positionWeight (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ)
    (node : Node) (u w : Label Node r) : ZMod p :=
  FiniteFieldDeformation.entry start width u w *
    (DeformationConstruction.phi nodeValue
      (fun label t => (label t).1) (fun label t => (label t).2) u w).eval (nodeValue node)

/-- The local variable coefficient retains all occupied positions carrying
that variable; no injectivity of `variableAt` is required. -/
def localCoefficient (occupied : Finset (Label Node r)) (variableAt : Label Node r → Var)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (u : Label Node r) (v : Var) : ZMod p :=
  ∑ w ∈ occupied with variableAt w = v, positionWeight nodeValue start width node u w

theorem localCoefficient_sum (occupied : Finset (Label Node r))
    (variableAt : Label Node r → Var) (groupOf : Var → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (u : Label Node r) (group : Fin r) (assignment : Var → Bool) :
    (∑ v : LocalVariable groupOf group,
      localCoefficient occupied variableAt nodeValue start width node u v.val *
        CountingPolynomial.boolValue (assignment v.val)) =
      ∑ w ∈ occupied with groupOf (variableAt w) = group,
        positionWeight nodeValue start width node u w *
          CountingPolynomial.boolValue (assignment (variableAt w)) := by
  rw [← RestrictedMeasurements.sum_local_fibers occupied variableAt groupOf group
    (fun w => positionWeight nodeValue start width node u w *
      CountingPolynomial.boolValue (assignment (variableAt w)))]
  unfold localCoefficient
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext w; simp)
  intro w hw
  rw [(Finset.mem_filter.mp hw).2]

/-- D4 for one occupied copy, with the actual tensor measurement rows and
the local term regrouped by declared variable. -/
theorem occupied_at_node_grouped (occupied : Finset (Label Node r))
    (variableAt : Label Node r → Var) (groupOf : Var → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (nonzero : nodeValue node ≠ 0)
    (groups_match : ∀ w ∈ occupied, groupOf (variableAt w) = (w node).1)
    (u : Label Node r) (assignment : Var → Bool) :
    (∑ w ∈ occupied,
      FiniteFieldDeformation.coefficient nodeValue start width u w *
        Polynomial.C (CountingPolynomial.boolValue (assignment (variableAt w)))).eval (nodeValue node) =
      (∑ v : LocalVariable groupOf (u node).2,
        localCoefficient occupied variableAt nodeValue start width node u v.val *
          CountingPolynomial.boolValue (assignment v.val)) +
      ∑ group : Fin r, ∑ index ∈ FiniteFieldDeformation.bad (Node := Node) (r := r) start width,
        FiniteFieldDeformation.residualCoefficient start width u index *
          (integerMeasurement groupOf group
            (RestrictedMeasurements.coefficient occupied variableAt RestrictedMeasurements.tensorSign
              index groupOf group)
            (partitionAssignmentEquiv groupOf assignment group) : ZMod p) := by
  rw [FiniteFieldDeformation.occupied_at_node nodeValue start width occupied
    (fun w => CountingPolynomial.boolValue (assignment (variableAt w))) u node nonzero]
  rw [localCoefficient_sum]
  have hfilter : occupied.filter (fun w => (w node).1 = (u node).2) =
      occupied.filter (fun w => groupOf (variableAt w) = (u node).2) := by
    apply Finset.filter_congr
    intro w hw
    rw [groups_match w hw]
  rw [hfilter]
  simp only [positionWeight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, RestrictedMeasurements.sum_groups_tensor_integerMeasurement_cast]
  exact add_comm _ _

variable [Fintype Copy] [DecidableEq Copy]

/-- There is one row for each occupied-copy/bad-basis-index pair in every group. -/
abbrev Row (Node Copy : Type*) [Fintype Node] [DecidableEq Node] (r : ℕ) (start : ℤ) (width : ℕ) :=
  Copy × {index : Label Node r // index ∈ FiniteFieldDeformation.bad start width}

def measurementRow (occupied : Copy → Finset (Label Node r))
    (variableAt : Copy → Label Node r → Var) (groupOf : Var → Fin r)
    (start : ℤ) (width : ℕ) (group : Fin r) (row : Row Node Copy r start width) :
    LocalVariable groupOf group → ℤ :=
  RestrictedMeasurements.coefficient (occupied row.1) (variableAt row.1)
    RestrictedMeasurements.tensorSign row.2.val groupOf group

omit [Fintype Copy] [DecidableEq Copy] in
theorem measurementRow_norm (occupied : Copy → Finset (Label Node r))
    (variableAt : Copy → Label Node r → Var) (groupOf : Var → Fin r)
    (start : ℤ) (width : ℕ) (group : Fin r) (row : Row Node Copy r start width) :
    (∑ v, |measurementRow occupied variableAt groupOf start width group row v|) ≤
      (r ^ (2 * Fintype.card Node) : ℕ) :=
  RestrictedMeasurements.tensor_coefficient_norm_le_dimension
    (occupied row.1) (variableAt row.1) row.2.val groupOf group

def measurementCoefficient (start : ℤ) (width : ℕ) (copy : Copy)
    (u : Label Node r) (_group : Fin r) (row : Row Node Copy r start width) : ZMod p :=
  if row.1 = copy then FiniteFieldDeformation.residualCoefficient start width u row.2.val else 0

set_option maxHeartbeats 1000000 in
theorem measurement_term_eq (occupied : Copy → Finset (Label Node r))
    (variableAt : Copy → Label Node r → Var) (groupOf : Var → Fin r)
    (start : ℤ) (width : ℕ) (copy : Copy) (u : Label Node r) (assignment : Var → Bool) :
    (∑ group, ∑ row : Row Node Copy r start width,
      measurementCoefficient (p := p) start width copy u group row *
        ((measurements groupOf (r ^ (2 * Fintype.card Node))
          (measurementRow occupied variableAt groupOf start width)
          (measurementRow_norm occupied variableAt groupOf start width) assignment group row).val : ZMod p)) =
      ∑ group : Fin r, ∑ index ∈ FiniteFieldDeformation.bad (Node := Node) (r := r) start width,
        FiniteFieldDeformation.residualCoefficient start width u index *
          (integerMeasurement groupOf group
            (RestrictedMeasurements.coefficient (occupied copy) (variableAt copy)
              RestrictedMeasurements.tensorSign index groupOf group)
            (partitionAssignmentEquiv groupOf assignment group) : ZMod p) := by
  apply Finset.sum_congr rfl
  intro group _
  simp only [Row, Fintype.sum_prod_type, measurementCoefficient, measurements, boundedMeasurement,
    measurementRow, ite_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  let weight : Label Node r → ZMod p := fun index =>
    FiniteFieldDeformation.residualCoefficient start width u index *
      (integerMeasurement groupOf group
        (RestrictedMeasurements.coefficient (occupied copy) (variableAt copy)
          RestrictedMeasurements.tensorSign index groupOf group)
        (partitionAssignmentEquiv groupOf assignment group) : ZMod p)
  change (∑ index : {i : Label Node r // i ∈ FiniteFieldDeformation.bad start width}, weight index.val) =
    ∑ index ∈ FiniteFieldDeformation.bad start width, weight index
  exact (Finset.sum_subtype (FiniteFieldDeformation.bad (Node := Node) (r := r) start width)
    (fun _ => Iff.rfl) weight).symm

/-- A single local-linear-value expression using the global tuple of all
copy/group measurements. Rows for every other copy have coefficient zero. -/
theorem occupied_localRepresentation (occupied : Copy → Finset (Label Node r))
    (variableAt : Copy → Label Node r → Var) (groupOf : Var → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (nonzero : nodeValue node ≠ 0)
    (groups_match : ∀ copy w, w ∈ occupied copy → groupOf (variableAt copy w) = (w node).1)
    (copy : Copy) (u : Label Node r) (assignment : Var → Bool) :
    (∑ w ∈ occupied copy,
      FiniteFieldDeformation.coefficient nodeValue start width u w *
        Polynomial.C (CountingPolynomial.boolValue (assignment (variableAt copy w)))).eval
          (nodeValue node) =
      localLinearValue groupOf (r ^ (2 * Fintype.card Node))
        (fun pair v => localCoefficient (occupied pair.1) (variableAt pair.1)
          nodeValue start width node pair.2 v)
        (fun pair group row => measurementCoefficient start width pair.1 pair.2 group row)
        (u node).2 (copy, u) (partitionAssignmentEquiv groupOf assignment (u node).2)
        (measurements groupOf (r ^ (2 * Fintype.card Node))
          (measurementRow occupied variableAt groupOf start width)
          (measurementRow_norm occupied variableAt groupOf start width) assignment) := by
  unfold localLinearValue
  rw [measurement_term_eq]
  exact occupied_at_node_grouped (occupied copy) (variableAt copy) groupOf nodeValue start width node
    nonzero (groups_match copy) u assignment

omit [Fintype Copy] [DecidableEq Node] [Fintype Var] in
/-- The exact image/inverse connector for one occupied copy. Placement is
injective in `(copy,label)`; variable identities need not be injective. -/
theorem incidence_sum_eq_occupied {Inc A : Type*} [Fintype Inc] [AddCommMonoid A]
    (copyOf : Inc → Copy) (labelOf : Inc → Label Node r) (variableOf : Inc → Var)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (occupied : Copy → Finset (Label Node r))
    (occupied_eq : ∀ copy, occupied copy = (Finset.univ.filter (fun inc => copyOf inc = copy)).image labelOf)
    (variableAt : Copy → Label Node r → Var)
    (stored : ∀ inc, variableAt (copyOf inc) (labelOf inc) = variableOf inc)
    (copy : Copy) (weight : Label Node r → Var → A) :
    (∑ inc, if copyOf inc = copy then weight (labelOf inc) (variableOf inc) else 0) =
      ∑ w ∈ occupied copy, weight w (variableAt copy w) := by
  rw [occupied_eq copy, Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro inc _
    by_cases hcopy : copyOf inc = copy
    · have hstored : variableAt copy (labelOf inc) = variableOf inc := by
        rw [← hcopy]
        exact stored inc
      simp [hcopy, hstored]
    · simp [hcopy]
  · intro first hfirst second hsecond hlabel
    apply placement
    exact Prod.ext ((Finset.mem_filter.mp hfirst).2.trans
      (Finset.mem_filter.mp hsecond).2.symm) hlabel

/-- The occupied positions are the literal image of the incidences in a copy. -/
def occupiedPositions {Inc : Type*} [Fintype Inc]
    (copyOf : Inc → Copy) (labelOf : Inc → Label Node r) (copy : Copy) : Finset (Label Node r) :=
  (Finset.univ.filter (fun inc => copyOf inc = copy)).image labelOf

/-- The stored variable is obtained from a placement inverse. The fallback is
used only at unoccupied positions and never contributes to a sum. This is a
finite mathematical accessor, with no asserted implementation cost. -/
def storedVariable {Inc : Type*} (fallback : Var) (variableOf : Inc → Var)
    (copyOf : Inc → Copy) (labelOf : Inc → Label Node r)
    (copy : Copy) (label : Label Node r) : Var :=
  if h : ∃ inc, (copyOf inc, labelOf inc) = (copy, label)
    then variableOf (Classical.choose h) else fallback

omit [Fintype Var] [Fintype Copy] [DecidableEq Copy] [DecidableEq Node] [Fintype Node] in
theorem storedVariable_at {Inc : Type*} (fallback : Var) (variableOf : Inc → Var)
    (copyOf : Inc → Copy) (labelOf : Inc → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc))) (inc : Inc) :
    storedVariable fallback variableOf copyOf labelOf (copyOf inc) (labelOf inc) = variableOf inc := by
  unfold storedVariable
  split_ifs with h
  · exact congrArg variableOf (placement (Classical.choose_spec h))
  · exact False.elim (h ⟨inc, rfl⟩)

omit [Fintype Copy] [DecidableEq Node] [Fintype Var] in
theorem occupiedPositions_groups_match {Inc : Type*} [Fintype Inc]
    (fallback : Var) (variableOf : Inc → Var)
    (copyOf : Inc → Copy) (labelOf : Inc → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (groupOf : Var → Fin r) (node : Node)
    (coordinates : ∀ inc, groupOf (variableOf inc) = (labelOf inc node).1)
    (copy : Copy) (w : Label Node r) (included : w ∈ occupiedPositions copyOf labelOf copy) :
    groupOf (storedVariable fallback variableOf copyOf labelOf copy w) = (w node).1 := by
  obtain ⟨inc, hinc, rfl⟩ := Finset.mem_image.mp included
  have hcopy : copyOf inc = copy := (Finset.mem_filter.mp hinc).2
  rw [← hcopy, storedVariable_at fallback variableOf copyOf labelOf placement]
  exact coordinates inc

section Formula

variable {n : ℕ}

def formulaLocalCoefficient (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (occupied : Copy → Finset (Label Node r)) (variableAt : Copy → Label Node r → Fin n)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (inc : FormulaCounter.Incidence formula) (v : Fin n) : ZMod p :=
  localCoefficient (occupied (copyOf inc)) (variableAt (copyOf inc)) nodeValue start width node
    (labelOf inc) v

def formulaMeasurementCoefficient (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (start : ℤ) (width : ℕ) (inc : FormulaCounter.Incidence formula)
    (group : Fin r) (row : Row Node Copy r start width) : ZMod p :=
  measurementCoefficient start width (copyOf inc) (labelOf inc) group row

omit [Fintype Copy] in
theorem formula_incidenceForm_eq_occupied (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (occupied : Copy → Finset (Label Node r))
    (occupied_eq : ∀ copy, occupied copy = (Finset.univ.filter (fun inc => copyOf inc = copy)).image labelOf)
    (variableAt : Copy → Label Node r → Fin n)
    (stored : ∀ inc, variableAt (copyOf inc) (labelOf inc) = IncidenceDeformation.incidenceVariable formula inc)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ)
    (inc : FormulaCounter.Incidence formula) (assignment : Assignment n) :
    CountingPolynomial.incidenceForm formula
        (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width) inc.1 inc.2 assignment =
      ∑ w ∈ occupied (copyOf inc),
        FiniteFieldDeformation.coefficient nodeValue start width (labelOf inc) w *
          Polynomial.C (CountingPolynomial.boolValue (assignment (variableAt (copyOf inc) w))) := by
  rw [FiniteFieldCounter.coefficients, IncidenceDeformation.formula_incidenceForm_eq_occupied_sum]
  exact incidence_sum_eq_occupied copyOf labelOf (IncidenceDeformation.incidenceVariable formula)
    placement occupied occupied_eq variableAt stored (copyOf inc)
    (fun w v => FiniteFieldDeformation.coefficient nodeValue start width (labelOf inc) w *
      Polynomial.C (CountingPolynomial.boolValue (assignment v)))

set_option maxHeartbeats 1000000 in
/-- D4 for the actual formula coefficients, derived from the spectral node
identity and the concrete integer rows. The assumptions are only the explicit
placement inverse and schedule-coordinate compatibility. -/
theorem formula_localRepresentation (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (occupied : Copy → Finset (Label Node r))
    (occupied_eq : ∀ copy, occupied copy = (Finset.univ.filter (fun inc => copyOf inc = copy)).image labelOf)
    (variableAt : Copy → Label Node r → Fin n)
    (stored : ∀ inc, variableAt (copyOf inc) (labelOf inc) = IncidenceDeformation.incidenceVariable formula inc)
    (groupOf : Fin n → Fin r) (clauseGroup : Fin formula.clauses.length → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (nonzero : nodeValue node ≠ 0)
    (groups_match : ∀ copy w, w ∈ occupied copy → groupOf (variableAt copy w) = (w node).1)
    (clauses_match : ∀ inc, (labelOf inc node).2 = clauseGroup inc.1) :
    LocalRepresentation formula
      (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)
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
theorem taylorData_eq_concrete_grouped (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (occupied : Copy → Finset (Label Node r))
    (occupied_eq : ∀ copy, occupied copy = (Finset.univ.filter (fun inc => copyOf inc = copy)).image labelOf)
    (variableAt : Copy → Label Node r → Fin n)
    (stored : ∀ inc, variableAt (copyOf inc) (labelOf inc) = IncidenceDeformation.incidenceVariable formula inc)
    (groupOf : Fin n → Fin r) (clauseGroup : Fin formula.clauses.length → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (nonzero : nodeValue node ≠ 0)
    (groups_match : ∀ copy w, w ∈ occupied copy → groupOf (variableAt copy w) = (w node).1)
    (clauses_match : ∀ inc, (labelOf inc node).2 = clauseGroup inc.1) (order : ℕ) :
    TaylorTruncation.taylorData Finset.univ
      (DeformationTaylor.expandedPolynomial Finset.univ (FormulaCounter.factorPolynomial formula)
        (FormulaCounter.coefficients formula
          (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)) (nodeValue node))
      Polynomial.X order =
    groupedTaylorData formula
      (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width) (nodeValue node)
      groupOf clauseGroup (r ^ (2 * Fintype.card Node))
      (measurementRow occupied variableAt groupOf start width)
      (measurementRow_norm occupied variableAt groupOf start width)
      (formulaLocalCoefficient formula copyOf labelOf occupied variableAt nodeValue start width node)
      (formulaMeasurementCoefficient formula copyOf labelOf start width) order := by
  apply GroupedDeformation.taylorData_eq_groupedTaylorData
  exact formula_localRepresentation formula copyOf labelOf placement occupied occupied_eq
    variableAt stored groupOf clauseGroup nodeValue start width node nonzero groups_match clauses_match

set_option maxHeartbeats 1000000 in
/-- The occupied sets and stored-variable inverse can themselves be constructed
from injective placement. The only remaining schedule hypotheses are the two
label-coordinate identities. No D4 or inverse-accessor equality is assumed. -/
theorem formula_localRepresentation_of_placement (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (groupOf : Fin n → Fin r) (clauseGroup : Fin formula.clauses.length → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (node : Node)
    (nonzero : nodeValue node ≠ 0)
    (variables_match : ∀ inc, groupOf (IncidenceDeformation.incidenceVariable formula inc) = (labelOf inc node).1)
    (clauses_match : ∀ inc, (labelOf inc node).2 = clauseGroup inc.1) :
    let occupied := occupiedPositions copyOf labelOf
    let variableAt := storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf
    LocalRepresentation formula
      (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)
      (nodeValue node) groupOf clauseGroup (r ^ (2 * Fintype.card Node))
      (measurementRow occupied variableAt groupOf start width)
      (measurementRow_norm occupied variableAt groupOf start width)
      (formulaLocalCoefficient formula copyOf labelOf occupied variableAt nodeValue start width node)
      (formulaMeasurementCoefficient formula copyOf labelOf start width) := by
  dsimp only
  apply formula_localRepresentation formula copyOf labelOf placement
    (occupiedPositions copyOf labelOf) (fun _ => rfl)
    (storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
    (storedVariable_at fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf placement)
    groupOf clauseGroup nodeValue start width node nonzero
  · exact occupiedPositions_groups_match fallback (IncidenceDeformation.incidenceVariable formula)
      copyOf labelOf placement groupOf node variables_match
  · exact clauses_match

end Formula

end

end NtimeDspace.ConcreteGroupedDeformation
