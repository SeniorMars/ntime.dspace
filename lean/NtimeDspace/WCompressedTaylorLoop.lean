import NtimeDspace.WeightedSystem
import NtimeDspace.WSchedulePlacement
import NtimeDspace.WGroupedFormulaLoop
import NtimeDspace.SupportCardinality
import NtimeDspace.SupportSubsetLoop
import NtimeDspace.SupportBudget
import NtimeDspace.WSparseCorrection

/-!
The compressed-support, subset-mask, measurement, group, and local-assignment
loops for Taylor-data evaluation. Canonical support length is parsed at run time
and supplies the actual subset-mask width. Invalid codes contribute zero.
All polynomial expressions below occur only in correctness statements.

The running loop still receives coefficient, row, and measurement accessors.
Their concrete implementations and simultaneous machine-resource bounds remain
separate obligations; a finite-field scalar loop is not a tape-space proof.
-/

namespace NtimeDspace.WCompressedTaylorLoop

open scoped BigOperators
open WGroupedDeformation
open NtimeDspace.GroupedDeformation hiding LocalRepresentation clausePolynomial_eval_congr expandedPolynomial_formula_eval factorPolynomial_eq_product_groupFactor groupFactor groupedFormulaSum groupedTaylorData grouped_formula_identity localInputs support_subset_iff_assignment taylorCorrection taylorData_eq_groupedTaylorData taylor_inner_eq_groupedFormulaSum

variable {n groups rows width : ℕ} {Row : Type*}
variable {K : Type*} [CommRing K]

def membershipBit (capacity : ℕ) (code : List Bool) (v : Fin n) : Bool :=
  (BoundedSupportParser.lookup n capacity (SupportAssignment.query v) code).getD false

theorem membershipBit_encode (capacity : ℕ) (support : List (Fin n))
    (valid : SupportAssignment.Valid capacity support) (v : Fin n) :
    membershipBit capacity (SupportAssignment.encode support) v =
      decide (v ∈ support.toFinset) := by
  have positive := (SupportAssignment.positiveSupport_valid_iff support).mpr valid
  have parsed := BoundedSupportParser.lookup_encodeSupport n capacity (SupportAssignment.query v)
    (SupportAssignment.positiveSupport support) positive.1 positive.2.1 positive.2.2.1 positive.2.2.2
  unfold membershipBit SupportAssignment.encode
  rw [parsed, Option.getD_some]
  simp only [SupportAssignment.query, Fin.val_mk, SupportAssignment.positiveSupport_mem,
    List.mem_toFinset]

/-- One canonical support contribution. Its parser result determines the mask
width; unused capacity slots never introduce extra subset choices. -/
def supportValue (formula : WeightedSystem.System n) (groupOf : Fin n → Fin groups)
    (clauseGroup : Fin formula.constraints.length → Fin groups)
    (rowAt : Fin rows → Row) (rowNumber : (Σ _ : Fin groups, Row) → Fin width)
    (bound capacity : ℕ)
    (measurement : ∀ g, Row → LocalVariable groupOf g → ℤ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin groups → Row → K)
    (evaluateCoefficient : WeightedSystem.Incidence formula → Fin n → K → K)
    (node point : K) (code : List Bool) : K :=
  match SupportCardinality.count n capacity code with
  | none => 0
  | some size =>
    SupportSubsetLoop.sumSignedSubsets size.val (fun mask =>
      WGroupedFormulaLoop.evaluate formula groupOf clauseGroup rowAt rowNumber bound
        measurement localCoefficient measurementCoefficient (membershipBit capacity code)
        (fun inc => (SparseCorrection.compressed evaluateCoefficient
          (SupportAssignment.extendMask (Nat.le_of_lt_succ size.isLt) mask)
          code node point inc).getD 0)) 0

set_option maxHeartbeats 1000000 in
theorem supportValue_correct [Fintype Row] [DecidableEq Row]
    (formula : WeightedSystem.System n) (L : WeightedSystem.Coefficients formula K)
    (groupOf : Fin n → Fin groups) (clauseGroup : Fin formula.constraints.length → Fin groups)
    (rowAt : Fin rows → Row) (rows_bijective : Function.Bijective rowAt)
    (rowNumber : (Σ _ : Fin groups, Row) → Fin width)
    (numbering : Function.Bijective rowNumber) (bound capacity : ℕ)
    (measurement : ∀ g, Row → LocalVariable groupOf g → ℤ)
    (norm : ∀ g row, ∑ v, |measurement g row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin groups → Row → K)
    (evaluateCoefficient : WeightedSystem.Incidence formula → Fin n → K → K)
    (evaluation : ∀ inc v x, evaluateCoefficient inc v x = (L inc.1 inc.2 v).eval x)
    (support : List (Fin n)) (valid : SupportAssignment.Valid capacity support) (node point : K) :
    supportValue formula groupOf clauseGroup rowAt rowNumber bound capacity measurement
      localCoefficient measurementCoefficient evaluateCoefficient node point
      (SupportAssignment.encode support) =
    (∑ subset ∈ support.toFinset.powerset,
      (-1 : Polynomial K) ^ (support.toFinset.card - subset.card) *
        groupedFormulaSum formula groupOf clauseGroup bound measurement norm localCoefficient
          measurementCoefficient (taylorCorrection formula L node subset) support.toFinset).eval point := by
  classical
  rcases valid with ⟨ordered, count⟩
  simp only [supportValue, SupportCardinality.count_encode support ⟨ordered, count⟩]
  rw [SupportSubsetLoop.sumSignedSubsets_correct support ordered.nodup
    (weight := fun subset =>
      (groupedFormulaSum formula groupOf clauseGroup bound measurement norm localCoefficient
        measurementCoefficient (taylorCorrection formula L node subset) support.toFinset).eval point)]
  · simp only [add_zero, PolynomialFacts.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one]
  · intro mask
    apply WGroupedFormulaLoop.evaluate_correct_of_accessors formula groupOf clauseGroup rowAt
      rows_bijective rowNumber numbering bound measurement norm localCoefficient measurementCoefficient
      support.toFinset (membershipBit capacity (SupportAssignment.encode support))
      (membershipBit_encode capacity support ⟨ordered, count⟩)
      (taylorCorrection formula L node (SparseCorrection.maskSubset support (Nat.le_refl _) mask)) point
    intro inc
    rw [WSparseCorrection.compressed_taylor_correct formula L evaluateCoefficient evaluation
      support ⟨ordered, count⟩ mask node point inc, Option.getD_some]

/-- Full support loop at the manuscript's support budget and cutoff. -/
def evaluate (formula : WeightedSystem.System n) (groupOf : Fin n → Fin groups)
    (clauseGroup : Fin formula.constraints.length → Fin groups)
    (rowAt : Fin rows → Row) (rowNumber : (Σ _ : Fin groups, Row) → Fin width)
    (bound k : ℕ)
    (measurement : ∀ g, Row → LocalVariable groupOf g → ℤ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin groups → Row → K)
    (evaluateCoefficient : WeightedSystem.Incidence formula → Fin n → K → K)
    (node point : K) : K :=
  SupportEnumeration.enumerateValid n (Parameters.q n k) (SupportBudget.limit n k)
    (supportValue formula groupOf clauseGroup rowAt rowNumber bound (Parameters.q n k)
      measurement localCoefficient measurementCoefficient evaluateCoefficient node point) 0

set_option maxHeartbeats 1000000 in
theorem evaluate_correct [Fintype Row] [DecidableEq Row]
    (formula : WeightedSystem.System n) (L : WeightedSystem.Coefficients formula K)
    (groupOf : Fin n → Fin groups) (clauseGroup : Fin formula.constraints.length → Fin groups)
    (rowAt : Fin rows → Row) (rows_bijective : Function.Bijective rowAt)
    (rowNumber : (Σ _ : Fin groups, Row) → Fin width)
    (numbering : Function.Bijective rowNumber) (bound k : ℕ) (large : 6 ≤ k)
    (measurement : ∀ g, Row → LocalVariable groupOf g → ℤ)
    (norm : ∀ g row, ∑ v, |measurement g row v| ≤ (bound : ℤ))
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin groups → Row → K)
    (evaluateCoefficient : WeightedSystem.Incidence formula → Fin n → K → K)
    (evaluation : ∀ inc v x, evaluateCoefficient inc v x = (L inc.1 inc.2 v).eval x)
    (node point : K) :
    evaluate formula groupOf clauseGroup rowAt rowNumber bound k measurement localCoefficient
      measurementCoefficient evaluateCoefficient node point =
    (groupedTaylorData formula L node groupOf clauseGroup bound measurement norm localCoefficient
      measurementCoefficient (Parameters.q n k + 1)).eval point := by
  classical
  unfold evaluate
  rw [SupportBudget.limit_eq_supportLimit]
  rw [SupportEnumeration.enumerateValid_parameter_sum n k large
    (weight := fun support =>
      (∑ subset ∈ support.powerset,
        (-1 : Polynomial K) ^ (support.card - subset.card) *
          groupedFormulaSum formula groupOf clauseGroup bound measurement norm localCoefficient
            measurementCoefficient (taylorCorrection formula L node subset) support).eval point)]
  · simp only [zero_add, groupedTaylorData, Finset.powerset_univ,
      PolynomialFacts.eval_finset_sum, Nat.lt_succ_iff]
  · intro support count
    have correct := supportValue_correct formula L groupOf clauseGroup rowAt rows_bijective
      rowNumber numbering bound (Parameters.q n k) measurement norm localCoefficient
      measurementCoefficient evaluateCoefficient evaluation support.sort
      ⟨support.sortedLT_sort.pairwise, by simpa using count⟩ node point
    simpa only [Finset.sort_toFinset] using correct

end NtimeDspace.WCompressedTaylorLoop
