import NtimeDspace.WeightedSystem
import NtimeDspace.FormulaCounter
import NtimeDspace.GroupedCounting
import Mathlib.Data.Int.Interval
import NtimeDspace.GroupedDeformation

namespace NtimeDspace.WGroupedDeformation

noncomputable section

open NtimeDspace.GroupedDeformation hiding LocalRepresentation clausePolynomial_eval_congr expandedPolynomial_formula_eval factorPolynomial_eq_product_groupFactor groupFactor groupedFormulaSum groupedTaylorData grouped_formula_identity localInputs support_subset_iff_assignment taylorCorrection taylorData_eq_groupedTaylorData taylor_inner_eq_groupedFormulaSum
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {Var Group : Type*}

section Clauses

variable {n : ℕ} {K : Type*} [CommRing K]

/-- A concrete clause polynomial depends only on its own incidence positions. -/
theorem clausePolynomial_eval_congr (formula : WeightedSystem.System n)
    (clause : Fin formula.constraints.length)
    (first second : WeightedSystem.Incidence formula → Polynomial K)
    (agreement : ∀ literal, first ⟨clause, literal⟩ = second ⟨clause, literal⟩) :
    (WeightedSystem.constraintPolynomial formula clause).eval₂ Polynomial.C first =
      (WeightedSystem.constraintPolynomial formula clause).eval₂ Polynomial.C second := by
  simp only [WeightedSystem.constraintPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_prod]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.prod_congr rfl
  intro literal _
  simp only [WeightedSystem.selector]
  split_ifs <;> simp [agreement]

end Clauses

section FormulaRegrouping

variable {n : ℕ} {Group : Type*} [Fintype Group] [DecidableEq Group]
variable {Row : Group → Type*} [∀ group, Fintype (Row group)]
variable {K : Type*} [CommRing K]

/-- Local incidence values after inserting a fixed measurement tuple and the
assignment-independent Taylor correction. -/
def localInputs (formula : WeightedSystem.System n) (groupOf : Fin n → Group) (bound : ℕ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K)
    (correction : WeightedSystem.Incidence formula → Polynomial K)
    (group : Group) (assignment : LocalAssignment groupOf group)
    (measured : MeasurementTuple Row bound) : WeightedSystem.Incidence formula → Polynomial K :=
  fun inc => Polynomial.C
    (localLinearValue groupOf bound localCoefficient measurementCoefficient group inc
      assignment measured) + correction inc

/-- A group's factor is the product of precisely the clauses assigned to it. -/
def groupFactor (formula : WeightedSystem.System n) (groupOf : Fin n → Group)
    (clauseGroup : Fin formula.constraints.length → Group) (bound : ℕ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K)
    (correction : WeightedSystem.Incidence formula → Polynomial K)
    (group : Group) (assignment : LocalAssignment groupOf group)
    (measured : MeasurementTuple Row bound) : Polynomial K :=
  ∏ clause : {clause // clauseGroup clause = group},
    (WeightedSystem.constraintPolynomial formula clause.val).eval₂ Polynomial.C
      (localInputs formula groupOf bound localCoefficient measurementCoefficient correction
        group assignment measured)

/-- D4 is a pointwise equality of specified linear forms at the chosen node.
It contains neither a counting identity nor a computational resource claim. -/
def LocalRepresentation (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.constraints.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K) : Prop :=
  ∀ (assignment : Assignment n) (inc : WeightedSystem.Incidence formula),
    (WeightedSystem.incidenceForm formula L inc.1 inc.2 assignment).eval node =
      localLinearValue groupOf bound localCoefficient measurementCoefficient (clauseGroup inc.1) inc
        (partitionAssignmentEquiv groupOf assignment (clauseGroup inc.1))
        (measurements groupOf bound measurement norm_bound assignment)

theorem factorPolynomial_eq_product_groupFactor (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.constraints.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K)
    (representation : LocalRepresentation formula L node groupOf clauseGroup bound
      measurement norm_bound localCoefficient measurementCoefficient)
    (correction : WeightedSystem.Incidence formula → Polynomial K)
    (assignment : Assignment n) :
    (WeightedSystem.factorPolynomial formula).eval₂ Polynomial.C
        (fun inc => Polynomial.C
          ((WeightedSystem.incidenceForm formula L inc.1 inc.2 assignment).eval node) +
          correction inc) =
      ∏ group, groupFactor formula groupOf clauseGroup bound localCoefficient
        measurementCoefficient correction group (partitionAssignmentEquiv groupOf assignment group)
          (measurements groupOf bound measurement norm_bound assignment) := by
  simp only [WeightedSystem.factorPolynomial, MvPolynomial.eval₂_prod, groupFactor]
  rw [← Fintype.prod_fiberwise clauseGroup]
  apply Finset.prod_congr rfl
  intro group _
  apply Finset.prod_congr rfl
  intro clause _
  apply clausePolynomial_eval_congr
  intro literal
  simp only [localInputs]
  rw [representation assignment ⟨clause.val, literal⟩]
  exact congrArg (fun g => Polynomial.C
    (localLinearValue groupOf bound localCoefficient measurementCoefficient g ⟨clause.val, literal⟩
      (partitionAssignmentEquiv groupOf assignment g)
      (measurements groupOf bound measurement norm_bound assignment)) +
      correction ⟨clause.val, literal⟩) clause.property

/-- The manuscript's exact grouped identity, instantiated with declared
Boolean variables, clause-assignment fibers, bounded integer measurements, and
the actual formula incidence polynomial. No polynomial truncation is used. -/
theorem grouped_formula_identity (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.constraints.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K)
    (representation : LocalRepresentation formula L node groupOf clauseGroup bound
      measurement norm_bound localCoefficient measurementCoefficient)
    (correction : WeightedSystem.Incidence formula → Polynomial K)
    (support : Finset (Fin n)) :
    (∑ assignment : Assignment n,
      if ∀ v ∈ support, assignment v = true then
        (WeightedSystem.factorPolynomial formula).eval₂ Polynomial.C
          (fun inc => Polynomial.C
            ((WeightedSystem.incidenceForm formula L inc.1 inc.2 assignment).eval node) +
            correction inc)
      else 0) =
    ∑ measured : MeasurementTuple Row bound,
      ∏ group, ∑ assignment : LocalAssignment groupOf group,
        if (fun row => boundedMeasurement groupOf group bound (measurement group row)
              (norm_bound group row) assignment) = measured group ∧
            localSupport groupOf support group assignment
        then groupFactor formula groupOf clauseGroup bound localCoefficient
          measurementCoefficient correction group assignment measured
        else 0 := by
  classical
  let measure : ∀ group, LocalAssignment groupOf group → (Row group → BoundedValue bound) :=
    fun group assignment row => boundedMeasurement groupOf group bound (measurement group row)
      (norm_bound group row) assignment
  let allowed := localSupport groupOf support
  let weight := groupFactor formula groupOf clauseGroup bound localCoefficient
    measurementCoefficient correction
  let summand := fun assignment : ∀ group, LocalAssignment groupOf group =>
    if ∀ group, allowed group (assignment group)
    then ∏ group, weight group (assignment group) (fun g => measure g (assignment g))
    else 0
  calc
    _ = ∑ assignment : Assignment n, summand (partitionAssignmentEquiv groupOf assignment) := by
      apply Finset.sum_congr rfl
      intro assignment _
      dsimp [summand, allowed, weight, measure]
      simp only [← support_constraint_iff groupOf support assignment]
      split_ifs
      · exact factorPolynomial_eq_product_groupFactor formula L node groupOf clauseGroup bound
          measurement norm_bound localCoefficient measurementCoefficient representation correction assignment
      · rfl
    _ = ∑ assignment : ∀ group, LocalAssignment groupOf group, summand assignment :=
      (partitionAssignmentEquiv groupOf).sum_comp summand
    _ = _ := GroupedCounting.grouped_counting_identity measure allowed weight

/-- The right-hand side of the grouped identity, with all enumeration domains
and measurement constraints explicit. -/
def groupedFormulaSum (formula : WeightedSystem.System n)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.constraints.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K)
    (correction : WeightedSystem.Incidence formula → Polynomial K)
    (support : Finset (Fin n)) : Polynomial K :=
  ∑ measured : MeasurementTuple Row bound,
    ∏ group, ∑ assignment : LocalAssignment groupOf group,
      if (fun row => boundedMeasurement groupOf group bound (measurement group row)
            (norm_bound group row) assignment) = measured group ∧
          localSupport groupOf support group assignment
      then groupFactor formula groupOf clauseGroup bound localCoefficient
        measurementCoefficient correction group assignment measured
      else 0

/-- The correction polynomial `b^U`, independent of the summed assignment. -/
def taylorCorrection (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K) (node : K)
    (subset : Finset (Fin n)) (inc : WeightedSystem.Incidence formula) : Polynomial K :=
  ∑ v, if v ∈ subset then
    Polynomial.taylor node (L inc.1 inc.2 v) - Polynomial.C ((L inc.1 inc.2 v).eval node)
    else 0

/-- The generic expanded polynomial used by scalar recovery is exactly the
concrete clause-factor expression with correction `b^U`. -/
theorem expandedPolynomial_formula_eval (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K) (node : K)
    (assigned subset : Finset (Fin n)) :
    TaylorTruncation.scaledEval
        (DeformationTaylor.expandedPolynomial Finset.univ (WeightedSystem.factorPolynomial formula)
          (WeightedSystem.coefficients formula L) node assigned) Polynomial.X subset =
      (WeightedSystem.factorPolynomial formula).eval₂ Polynomial.C
        (fun inc => Polynomial.C
          ((WeightedSystem.incidenceForm formula L inc.1 inc.2
            (FormulaCounter.assignmentOfSupport assigned)).eval node) +
          taylorCorrection formula L node subset inc) := by
  rw [DeformationTaylor.expandedPolynomial_eval]
  congr 1
  funext inc
  rw [DeformationTaylor.correctedForm_eval, WeightedSystem.linearValue_eq_incidenceForm]
  rfl

theorem support_subset_iff_assignment (support assigned : Finset (Fin n)) :
    support ⊆ assigned ↔
      ∀ v ∈ support, FormulaCounter.assignmentOfSupport assigned v = true := by
  simp [FormulaCounter.assignmentOfSupport, Finset.subset_iff]

/-- Exact replacement of the inner assignment loop appearing in
`WeightedSystem.scalarExpression` through `TaylorTruncation.taylorData`.
The support and correction subset need not satisfy any extra relation. -/
theorem taylor_inner_eq_groupedFormulaSum (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.constraints.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K)
    (representation : LocalRepresentation formula L node groupOf clauseGroup bound
      measurement norm_bound localCoefficient measurementCoefficient)
    (support subset : Finset (Fin n)) :
    (∑ assigned ∈ (Finset.univ : Finset (Fin n)).powerset,
      if support ⊆ assigned then
        TaylorTruncation.scaledEval
          (DeformationTaylor.expandedPolynomial Finset.univ (WeightedSystem.factorPolynomial formula)
            (WeightedSystem.coefficients formula L) node assigned) Polynomial.X subset
      else 0) =
      groupedFormulaSum formula groupOf clauseGroup bound measurement norm_bound
        localCoefficient measurementCoefficient (taylorCorrection formula L node subset) support := by
  let f : Assignment n → Polynomial K := fun assignment =>
    if ∀ v ∈ support, assignment v = true then
      (WeightedSystem.factorPolynomial formula).eval₂ Polynomial.C
        (fun inc => Polynomial.C
          ((WeightedSystem.incidenceForm formula L inc.1 inc.2 assignment).eval node) +
          taylorCorrection formula L node subset inc)
    else 0
  simp only [Finset.powerset_univ]
  calc
    _ = ∑ assigned : Finset (Fin n), f (FormulaCounter.supportAssignmentEquiv n assigned) := by
      apply Finset.sum_congr rfl
      intro assigned _
      simp only [expandedPolynomial_formula_eval, support_subset_iff_assignment]
      rfl
    _ = ∑ assignment : Assignment n, f assignment :=
      (FormulaCounter.supportAssignmentEquiv n).sum_comp f
    _ = _ := grouped_formula_identity formula L node groupOf clauseGroup bound measurement norm_bound
      localCoefficient measurementCoefficient representation (taylorCorrection formula L node subset) support

/-- The complete untruncated Taylor-data polynomial in the grouped loop order. -/
def groupedTaylorData (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.constraints.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K)
    (order : ℕ) : Polynomial K :=
  ∑ support ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun support => support.card < order),
    ∑ subset ∈ support.powerset,
      (-1 : Polynomial K) ^ (support.card - subset.card) *
        groupedFormulaSum formula groupOf clauseGroup bound measurement norm_bound
          localCoefficient measurementCoefficient (taylorCorrection formula L node subset) support

theorem taylorData_eq_groupedTaylorData (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.constraints.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K)
    (representation : LocalRepresentation formula L node groupOf clauseGroup bound
      measurement norm_bound localCoefficient measurementCoefficient)
    (order : ℕ) :
    TaylorTruncation.taylorData Finset.univ
        (DeformationTaylor.expandedPolynomial Finset.univ (WeightedSystem.factorPolynomial formula)
          (WeightedSystem.coefficients formula L) node) Polynomial.X order =
      groupedTaylorData formula L node groupOf clauseGroup bound measurement norm_bound
        localCoefficient measurementCoefficient order := by
  unfold TaylorTruncation.taylorData groupedTaylorData
  simp_rw [taylor_inner_eq_groupedFormulaSum formula L node groupOf clauseGroup bound
    measurement norm_bound localCoefficient measurementCoefficient representation]

end FormulaRegrouping

end

end NtimeDspace.WGroupedDeformation
