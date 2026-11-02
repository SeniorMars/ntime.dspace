import NtimeDspace.FormulaCounter
import NtimeDspace.GroupedCounting
import Mathlib.Data.Int.Interval

/-!
# Concrete partitions and grouped deformation sums

Variable groups are the fibers of an explicit finite partition map. Integer
measurement rows are supported on those fibers, and their norm bound places
every Boolean measurement in the finite interval `[-D,D]`.

The clause regrouping below uses the actual incidence clause polynomials.
Its D4 hypothesis states the exact local linear-form representation; it does
not assume the grouped-counting equality or any resource guarantee.
-/

namespace NtimeDspace.GroupedDeformation

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators

variable {Var Group : Type*}

/-- One part of the declared-variable partition. Empty groups are permitted. -/
abbrev LocalVariable (groupOf : Var → Group) (group : Group) :=
  {v : Var // groupOf v = group}

abbrev LocalAssignment (groupOf : Var → Group) (group : Group) :=
  LocalVariable groupOf group → Bool

/-- Restriction to disjoint fibers is an equivalence, including unused variables. -/
def partitionAssignmentEquiv (groupOf : Var → Group) :
    (Var → Bool) ≃ (∀ group, LocalAssignment groupOf group) where
  toFun assignment _ v := assignment v
  invFun assignments v := assignments (groupOf v) ⟨v, rfl⟩
  left_inv _ := rfl
  right_inv assignments := by
    funext group v
    rcases v with ⟨v, hv⟩
    cases hv
    rfl

def localSupport (groupOf : Var → Group) (support : Finset Var)
    (group : Group) (assignment : LocalAssignment groupOf group) : Prop :=
  ∀ v, v.val ∈ support → assignment v = true

theorem support_constraint_iff (groupOf : Var → Group) (support : Finset Var)
    (assignment : Var → Bool) :
    (∀ v ∈ support, assignment v = true) ↔
      ∀ group, localSupport groupOf support group (partitionAssignmentEquiv groupOf assignment group) := by
  constructor
  · intro h group v hv
    exact h v.val hv
  · intro h v hv
    exact h (groupOf v) ⟨v, rfl⟩ hv

section Measurements

variable [Fintype Var] [DecidableEq Group]

/-- A measurement value is an integer in the manuscript's finite range. -/
abbrev BoundedValue (bound : ℕ) :=
  {value : ℤ // value ∈ Finset.Icc (-(bound : ℤ)) (bound : ℤ)}

def integerMeasurement (groupOf : Var → Group) (group : Group)
    (coefficient : LocalVariable groupOf group → ℤ)
    (assignment : LocalAssignment groupOf group) : ℤ :=
  ∑ v, coefficient v * CountingPolynomial.boolValue (assignment v)

theorem integerMeasurement_abs_le (groupOf : Var → Group) (group : Group)
    (coefficient : LocalVariable groupOf group → ℤ)
    (assignment : LocalAssignment groupOf group) :
    |integerMeasurement groupOf group coefficient assignment| ≤ ∑ v, |coefficient v| := by
  unfold integerMeasurement
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro v _
  cases assignment v <;> simp [CountingPolynomial.boolValue]

/-- The norm hypothesis proves that no possible Boolean measurement is lost
when the outer sum enumerates only `[-D,D]`. -/
def boundedMeasurement (groupOf : Var → Group) (group : Group) (bound : ℕ)
    (coefficient : LocalVariable groupOf group → ℤ)
    (norm_bound : ∑ v, |coefficient v| ≤ (bound : ℤ))
    (assignment : LocalAssignment groupOf group) : BoundedValue bound :=
  ⟨integerMeasurement groupOf group coefficient assignment,
    Finset.mem_Icc.mpr (abs_le.mp
      ((integerMeasurement_abs_le groupOf group coefficient assignment).trans norm_bound))⟩

theorem boundedMeasurement_eq_iff (groupOf : Var → Group) (group : Group) (bound : ℕ)
    (coefficient : LocalVariable groupOf group → ℤ)
    (norm_bound : ∑ v, |coefficient v| ≤ (bound : ℤ))
    (assignment : LocalAssignment groupOf group) (value : BoundedValue bound) :
    boundedMeasurement groupOf group bound coefficient norm_bound assignment = value ↔
      integerMeasurement groupOf group coefficient assignment = value.val :=
  Subtype.ext_iff

theorem boundedValue_card (bound : ℕ) :
    Fintype.card (BoundedValue bound) = 2 * bound + 1 := by
  simp only [BoundedValue, Fintype.card_coe, Int.card_Icc]
  omega

end Measurements

section Representations

variable [Fintype Var] [Fintype Group] [DecidableEq Group]
variable {Row : Group → Type*} [∀ group, Fintype (Row group)]
variable {K Inc : Type*} [CommRing K]

abbrev MeasurementTuple (Row : Group → Type*) (bound : ℕ) :=
  ∀ group, Row group → BoundedValue bound

theorem measurementTuple_card (bound : ℕ) :
    Fintype.card (MeasurementTuple Row bound) =
      (2 * bound + 1) ^ (∑ group, Fintype.card (Row group)) := by
  simp only [MeasurementTuple, Fintype.card_pi, boundedValue_card,
    Finset.prod_const, Finset.card_univ]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- All measurements are computed group by group from the given assignment. -/
def measurements (groupOf : Var → Group) (bound : ℕ)
    (coefficient : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |coefficient group row v| ≤ (bound : ℤ))
    (assignment : Var → Bool) : MeasurementTuple Row bound :=
  fun group row => boundedMeasurement groupOf group bound (coefficient group row)
    (norm_bound group row) (partitionAssignmentEquiv groupOf assignment group)

/-- The explicit D4 expression: a linear form in one group's variables plus
a linear combination of the full finite measurement tuple. -/
def localLinearValue (groupOf : Var → Group) (bound : ℕ)
    (localCoefficient : Inc → Var → K)
    (measurementCoefficient : Inc → ∀ group, Row group → K)
    (group : Group) (inc : Inc) (assignment : LocalAssignment groupOf group)
    (measured : MeasurementTuple Row bound) : K :=
  (∑ v : LocalVariable groupOf group,
    localCoefficient inc v * CountingPolynomial.boolValue (assignment v)) +
  ∑ g, ∑ row, measurementCoefficient inc g row * (measured g row).val

end Representations

section Clauses

variable {n : ℕ} {K : Type*} [CommRing K]

/-- A concrete clause polynomial depends only on its own incidence positions. -/
theorem clausePolynomial_eval_congr (formula : Formula n)
    (clause : Fin formula.clauses.length)
    (first second : FormulaCounter.Incidence formula → Polynomial K)
    (agreement : ∀ literal, first ⟨clause, literal⟩ = second ⟨clause, literal⟩) :
    (FormulaCounter.clausePolynomial formula clause).eval₂ Polynomial.C first =
      (FormulaCounter.clausePolynomial formula clause).eval₂ Polynomial.C second := by
  simp only [FormulaCounter.clausePolynomial, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro literal _
  simp only [FormulaCounter.literalPolynomial]
  split_ifs <;> simp [agreement]

end Clauses

section FormulaRegrouping

variable {n : ℕ} {Group : Type*} [Fintype Group] [DecidableEq Group]
variable {Row : Group → Type*} [∀ group, Fintype (Row group)]
variable {K : Type*} [CommRing K]

/-- Local incidence values after inserting a fixed measurement tuple and the
assignment-independent Taylor correction. -/
def localInputs (formula : Formula n) (groupOf : Fin n → Group) (bound : ℕ)
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K)
    (correction : FormulaCounter.Incidence formula → Polynomial K)
    (group : Group) (assignment : LocalAssignment groupOf group)
    (measured : MeasurementTuple Row bound) : FormulaCounter.Incidence formula → Polynomial K :=
  fun inc => Polynomial.C
    (localLinearValue groupOf bound localCoefficient measurementCoefficient group inc
      assignment measured) + correction inc

/-- A group's factor is the product of precisely the clauses assigned to it. -/
def groupFactor (formula : Formula n) (groupOf : Fin n → Group)
    (clauseGroup : Fin formula.clauses.length → Group) (bound : ℕ)
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K)
    (correction : FormulaCounter.Incidence formula → Polynomial K)
    (group : Group) (assignment : LocalAssignment groupOf group)
    (measured : MeasurementTuple Row bound) : Polynomial K :=
  ∏ clause : {clause // clauseGroup clause = group},
    (FormulaCounter.clausePolynomial formula clause.val).eval₂ Polynomial.C
      (localInputs formula groupOf bound localCoefficient measurementCoefficient correction
        group assignment measured)

/-- D4 is a pointwise equality of specified linear forms at the chosen node.
It contains neither a counting identity nor a computational resource claim. -/
def LocalRepresentation (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.clauses.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K) : Prop :=
  ∀ (assignment : Assignment n) (inc : FormulaCounter.Incidence formula),
    (CountingPolynomial.incidenceForm formula L inc.1 inc.2 assignment).eval node =
      localLinearValue groupOf bound localCoefficient measurementCoefficient (clauseGroup inc.1) inc
        (partitionAssignmentEquiv groupOf assignment (clauseGroup inc.1))
        (measurements groupOf bound measurement norm_bound assignment)

theorem factorPolynomial_eq_product_groupFactor (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.clauses.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K)
    (representation : LocalRepresentation formula L node groupOf clauseGroup bound
      measurement norm_bound localCoefficient measurementCoefficient)
    (correction : FormulaCounter.Incidence formula → Polynomial K)
    (assignment : Assignment n) :
    (FormulaCounter.factorPolynomial formula).eval₂ Polynomial.C
        (fun inc => Polynomial.C
          ((CountingPolynomial.incidenceForm formula L inc.1 inc.2 assignment).eval node) +
          correction inc) =
      ∏ group, groupFactor formula groupOf clauseGroup bound localCoefficient
        measurementCoefficient correction group (partitionAssignmentEquiv groupOf assignment group)
          (measurements groupOf bound measurement norm_bound assignment) := by
  simp only [FormulaCounter.factorPolynomial, MvPolynomial.eval₂_prod, groupFactor]
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
theorem grouped_formula_identity (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.clauses.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K)
    (representation : LocalRepresentation formula L node groupOf clauseGroup bound
      measurement norm_bound localCoefficient measurementCoefficient)
    (correction : FormulaCounter.Incidence formula → Polynomial K)
    (support : Finset (Fin n)) :
    (∑ assignment : Assignment n,
      if ∀ v ∈ support, assignment v = true then
        (FormulaCounter.factorPolynomial formula).eval₂ Polynomial.C
          (fun inc => Polynomial.C
            ((CountingPolynomial.incidenceForm formula L inc.1 inc.2 assignment).eval node) +
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
def groupedFormulaSum (formula : Formula n)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.clauses.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K)
    (correction : FormulaCounter.Incidence formula → Polynomial K)
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
def taylorCorrection (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (node : K)
    (subset : Finset (Fin n)) (inc : FormulaCounter.Incidence formula) : Polynomial K :=
  ∑ v, if v ∈ subset then
    Polynomial.taylor node (L inc.1 inc.2 v) - Polynomial.C ((L inc.1 inc.2 v).eval node)
    else 0

/-- The generic expanded polynomial used by scalar recovery is exactly the
concrete clause-factor expression with correction `b^U`. -/
theorem expandedPolynomial_formula_eval (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (node : K)
    (assigned subset : Finset (Fin n)) :
    TaylorTruncation.scaledEval
        (DeformationTaylor.expandedPolynomial Finset.univ (FormulaCounter.factorPolynomial formula)
          (FormulaCounter.coefficients formula L) node assigned) Polynomial.X subset =
      (FormulaCounter.factorPolynomial formula).eval₂ Polynomial.C
        (fun inc => Polynomial.C
          ((CountingPolynomial.incidenceForm formula L inc.1 inc.2
            (FormulaCounter.assignmentOfSupport assigned)).eval node) +
          taylorCorrection formula L node subset inc) := by
  rw [DeformationTaylor.expandedPolynomial_eval]
  congr 1
  funext inc
  rw [DeformationTaylor.correctedForm_eval, FormulaCounter.linearValue_eq_incidenceForm]
  rfl

theorem support_subset_iff_assignment (support assigned : Finset (Fin n)) :
    support ⊆ assigned ↔
      ∀ v ∈ support, FormulaCounter.assignmentOfSupport assigned v = true := by
  simp [FormulaCounter.assignmentOfSupport, Finset.subset_iff]

/-- Exact replacement of the inner assignment loop appearing in
`FormulaCounter.scalarFormulaExpression` through `TaylorTruncation.taylorData`.
The support and correction subset need not satisfy any extra relation. -/
theorem taylor_inner_eq_groupedFormulaSum (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.clauses.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K)
    (representation : LocalRepresentation formula L node groupOf clauseGroup bound
      measurement norm_bound localCoefficient measurementCoefficient)
    (support subset : Finset (Fin n)) :
    (∑ assigned ∈ (Finset.univ : Finset (Fin n)).powerset,
      if support ⊆ assigned then
        TaylorTruncation.scaledEval
          (DeformationTaylor.expandedPolynomial Finset.univ (FormulaCounter.factorPolynomial formula)
            (FormulaCounter.coefficients formula L) node assigned) Polynomial.X subset
      else 0) =
      groupedFormulaSum formula groupOf clauseGroup bound measurement norm_bound
        localCoefficient measurementCoefficient (taylorCorrection formula L node subset) support := by
  let f : Assignment n → Polynomial K := fun assignment =>
    if ∀ v ∈ support, assignment v = true then
      (FormulaCounter.factorPolynomial formula).eval₂ Polynomial.C
        (fun inc => Polynomial.C
          ((CountingPolynomial.incidenceForm formula L inc.1 inc.2 assignment).eval node) +
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
def groupedTaylorData (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.clauses.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K)
    (order : ℕ) : Polynomial K :=
  ∑ support ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun support => support.card < order),
    ∑ subset ∈ support.powerset,
      (-1 : Polynomial K) ^ (support.card - subset.card) *
        groupedFormulaSum formula groupOf clauseGroup bound measurement norm_bound
          localCoefficient measurementCoefficient (taylorCorrection formula L node subset) support

theorem taylorData_eq_groupedTaylorData (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K) (node : K)
    (groupOf : Fin n → Group) (clauseGroup : Fin formula.clauses.length → Group) (bound : ℕ)
    (measurement : ∀ group, Row group → LocalVariable groupOf group → ℤ)
    (norm_bound : ∀ group row, ∑ v, |measurement group row v| ≤ (bound : ℤ))
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K)
    (representation : LocalRepresentation formula L node groupOf clauseGroup bound
      measurement norm_bound localCoefficient measurementCoefficient)
    (order : ℕ) :
    TaylorTruncation.taylorData Finset.univ
        (DeformationTaylor.expandedPolynomial Finset.univ (FormulaCounter.factorPolynomial formula)
          (FormulaCounter.coefficients formula L) node) Polynomial.X order =
      groupedTaylorData formula L node groupOf clauseGroup bound measurement norm_bound
        localCoefficient measurementCoefficient order := by
  unfold TaylorTruncation.taylorData groupedTaylorData
  simp_rw [taylor_inner_eq_groupedFormulaSum formula L node groupOf clauseGroup bound
    measurement norm_bound localCoefficient measurementCoefficient representation]

end FormulaRegrouping

end

end NtimeDspace.GroupedDeformation
