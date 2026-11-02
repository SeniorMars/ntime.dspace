import NtimeDspace.WeightedSystem
import NtimeDspace.WSchedulePlacement
import NtimeDspace.WGroupedInnerLoop
import NtimeDspace.MeasurementEnumeration

/-!
The nested measurement/group/local-assignment loops for a fixed support and
Taylor correction, implemented by scalar accumulators and indexed accessors.
The result agrees with evaluation of the actual grouped formula polynomial.
The coefficient, support, row, and correction accessors remain explicit inputs;
this is not yet an unconditional implementation or a tape-resource theorem.
-/

namespace NtimeDspace.WGroupedFormulaLoop

open scoped BigOperators
open WGroupedDeformation WGroupedAssignmentEvaluation
open NtimeDspace.GroupedDeformation hiding LocalRepresentation clausePolynomial_eval_congr expandedPolynomial_formula_eval factorPolynomial_eq_product_groupFactor groupFactor groupedFormulaSum groupedTaylorData grouped_formula_identity localInputs support_subset_iff_assignment taylorCorrection taylorData_eq_groupedTaylorData taylor_inner_eq_groupedFormulaSum

variable {n groups rows width : ℕ} {Row : Type*}
variable {K : Type*} [CommRing K]

/-- Evaluate all measurement tuples and multiply their local assignment sums.
No list of assignments, measurement tuples, or polynomials is constructed. -/
def evaluate (formula : WeightedSystem.System n) (groupOf : Fin n → Fin groups)
    (clauseGroup : Fin formula.constraints.length → Fin groups)
    (rowAt : Fin rows → Row)
    (rowNumber : (Σ _ : Fin groups, Row) → Fin width) (bound : ℕ)
    (measurement : ∀ g, Row → LocalVariable groupOf g → ℤ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin groups → Row → K)
    (supportBit : Fin n → Bool) (correctionValue : WeightedSystem.Incidence formula → K) : K :=
  MeasurementEnumeration.sumGrouped rowNumber bound (fun target =>
    scanProduct (fun group => WGroupedInnerLoop.sumGroup formula groupOf clauseGroup group rowAt
      measurement localCoefficient measurementCoefficient (fun g row => (target g row).val)
      supportBit correctionValue) 1) 0

set_option maxHeartbeats 1000000 in
theorem evaluate_correct [Fintype Row] [DecidableEq Row]
    (formula : WeightedSystem.System n) (groupOf : Fin n → Fin groups)
    (clauseGroup : Fin formula.constraints.length → Fin groups)
    (rowAt : Fin rows → Row) (rows_bijective : Function.Bijective rowAt)
    (rowNumber : (Σ _ : Fin groups, Row) → Fin width)
    (numbering : Function.Bijective rowNumber) (bound : ℕ)
    (measurement : ∀ g, Row → LocalVariable groupOf g → ℤ)
    (norm : ∀ g row, ∑ v, |measurement g row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin groups → Row → K)
    (support : Finset (Fin n)) (supportBit : Fin n → Bool)
    (membership : ∀ v, supportBit v = decide (v ∈ support))
    (correction : WeightedSystem.Incidence formula → Polynomial K) (point : K) :
    evaluate formula groupOf clauseGroup rowAt rowNumber bound measurement localCoefficient
      measurementCoefficient supportBit (fun inc => (correction inc).eval point) =
    (groupedFormulaSum formula groupOf clauseGroup bound measurement norm localCoefficient
      measurementCoefficient correction support).eval point := by
  classical
  rw [evaluate, MeasurementEnumeration.sumGrouped_correct rowNumber numbering, add_zero,
    groupedFormulaSum, PolynomialFacts.eval_finset_sum]
  refine Finset.sum_congr ?_ ?_
  · ext target
    simp
  · intro target _
    rw [scanProduct_correct, mul_one, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro group _
    exact WGroupedInnerLoop.sumGroup_correct formula groupOf clauseGroup group rowAt rows_bijective
      bound measurement norm localCoefficient measurementCoefficient target support supportBit
      membership correction point

/-- A scalar correction accessor can be substituted after its own correctness
proof. Equality of its returned field values is sufficient. -/
theorem evaluate_correct_of_accessors [Fintype Row] [DecidableEq Row]
    (formula : WeightedSystem.System n) (groupOf : Fin n → Fin groups)
    (clauseGroup : Fin formula.constraints.length → Fin groups)
    (rowAt : Fin rows → Row) (rows_bijective : Function.Bijective rowAt)
    (rowNumber : (Σ _ : Fin groups, Row) → Fin width)
    (numbering : Function.Bijective rowNumber) (bound : ℕ)
    (measurement : ∀ g, Row → LocalVariable groupOf g → ℤ)
    (norm : ∀ g row, ∑ v, |measurement g row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin groups → Row → K)
    (support : Finset (Fin n)) (supportBit : Fin n → Bool)
    (membership : ∀ v, supportBit v = decide (v ∈ support))
    (correction : WeightedSystem.Incidence formula → Polynomial K) (point : K)
    (correctionValue : WeightedSystem.Incidence formula → K)
    (correct : ∀ inc, correctionValue inc = (correction inc).eval point) :
    evaluate formula groupOf clauseGroup rowAt rowNumber bound measurement localCoefficient
      measurementCoefficient supportBit correctionValue =
    (groupedFormulaSum formula groupOf clauseGroup bound measurement norm localCoefficient
      measurementCoefficient correction support).eval point := by
  have same : correctionValue = fun inc => (correction inc).eval point := funext correct
  rw [same]
  exact evaluate_correct formula groupOf clauseGroup rowAt rows_bijective rowNumber numbering
    bound measurement norm localCoefficient measurementCoefficient support supportBit membership
    correction point

end NtimeDspace.WGroupedFormulaLoop
