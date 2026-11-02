import NtimeDspace.GroupedAssignmentEvaluation

/-!
The local assignment loop of the grouped counter, with scalar scans for its
support test, measurement tests, local linear values, and clause products.
Rows are supplied by an explicit indexed accessor. Its bijectivity is a proof
obligation, not a run-time inverse. Coefficient, support, row, measurement-tuple,
and correction accessors still require concrete implementations and costs.
-/

namespace NtimeDspace.GroupedInnerLoop

open scoped BigOperators
open GroupedDeformation GroupedAssignmentEvaluation

def allLoop (test : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | count + 1 => test count && allLoop test count

theorem allLoop_correct (test : ℕ → Bool) (count : ℕ) :
    allLoop test count = true ↔ ∀ i < count, test i = true := by
  induction count with
  | zero => simp [allLoop]
  | succ count ih =>
    rw [allLoop, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨last, previous⟩ i hi
      by_cases same : i = count
      · simpa [same] using last
      · exact previous i (by omega)
    · intro all
      exact ⟨all count (by omega), fun i hi => all i (by omega)⟩

def scanAll {count : ℕ} (test : Fin count → Bool) : Bool :=
  allLoop (fun i => if within : i < count then test ⟨i, within⟩ else false) count

theorem scanAll_correct {count : ℕ} (test : Fin count → Bool) :
    scanAll test = true ↔ ∀ i, test i = true := by
  rw [scanAll, allLoop_correct]
  constructor
  · intro h i
    simpa only [dite_eq_left i.isLt] using h i.val i.isLt
  · intro h i hi
    simpa only [dite_eq_left hi] using h ⟨i, hi⟩

variable {n groups rows : ℕ} {Row : Type*} [Fintype Row]
variable {K : Type*} [CommRing K]

def supportTest (groupOf : Fin n → Fin groups) (group : Fin groups)
    (supportBit : Fin n → Bool) (mask : ℕ) : Bool :=
  scanAll (fun v => if sameGroup : groupOf v = group then
    !supportBit v || LocalAssignmentLoop.assignment groupOf group mask ⟨v, sameGroup⟩
    else true)

theorem supportTest_correct (groupOf : Fin n → Fin groups) (group : Fin groups)
    (support : Finset (Fin n)) (supportBit : Fin n → Bool)
    (membership : ∀ v, supportBit v = decide (v ∈ support)) (mask : ℕ) :
    supportTest groupOf group supportBit mask = true ↔
      localSupport groupOf support group (LocalAssignmentLoop.assignment groupOf group mask) := by
  rw [supportTest, scanAll_correct]
  constructor
  · intro h v member
    have hv := h v.val
    simpa [v.property, membership, member] using hv
  · intro h v
    by_cases sameGroup : groupOf v = group
    · by_cases member : v ∈ support
      · simpa [sameGroup, membership, member] using h ⟨v, sameGroup⟩ member
      · simp [sameGroup, membership, member]
    · simp [sameGroup]

/-- Test rows by recomputing one integer measurement at a time. -/
def measurementTest (groupOf : Fin n → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row)
    (coefficient : Row → LocalVariable groupOf group → ℤ)
    (target : Row → ℤ) (mask : ℕ) : Bool :=
  scanAll (fun row => decide
    (measurement groupOf group (coefficient (rowAt row)) mask = target (rowAt row)))

omit [Fintype Row] in
theorem measurementTest_correct (groupOf : Fin n → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row) (covers : Function.Surjective rowAt)
    (coefficient : Row → LocalVariable groupOf group → ℤ)
    (target : Row → ℤ) (mask : ℕ) :
    measurementTest groupOf group rowAt coefficient target mask = true ↔
      ∀ row, integerMeasurement groupOf group (coefficient row)
        (LocalAssignmentLoop.assignment groupOf group mask) = target row := by
  simp only [measurementTest, scanAll_correct, decide_eq_true_eq, measurement_correct]
  constructor
  · intro h row
    obtain ⟨index, rfl⟩ := covers row
    exact h index
  · intro h index
    exact h (rowAt index)

def allowed (groupOf : Fin n → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row)
    (coefficient : Row → LocalVariable groupOf group → ℤ)
    (target : Row → ℤ) (supportBit : Fin n → Bool) (mask : ℕ) : Bool :=
  measurementTest groupOf group rowAt coefficient target mask &&
    supportTest groupOf group supportBit mask

omit [Fintype Row] in
theorem allowed_correct (groupOf : Fin n → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row) (covers : Function.Surjective rowAt)
    (bound : ℕ) (coefficient : Row → LocalVariable groupOf group → ℤ)
    (norm : ∀ row, ∑ v, |coefficient row v| ≤ (bound : ℤ))
    (target : Row → BoundedValue bound)
    (support : Finset (Fin n)) (supportBit : Fin n → Bool)
    (membership : ∀ v, supportBit v = decide (v ∈ support)) (mask : ℕ) :
    allowed groupOf group rowAt coefficient (fun row => (target row).val) supportBit mask = true ↔
      (fun row => boundedMeasurement groupOf group bound (coefficient row) (norm row)
        (LocalAssignmentLoop.assignment groupOf group mask)) = target ∧
      localSupport groupOf support group (LocalAssignmentLoop.assignment groupOf group mask) := by
  rw [allowed, Bool.and_eq_true, measurementTest_correct _ _ _ covers,
    supportTest_correct _ _ _ _ membership]
  have equal_iff : (∀ row, integerMeasurement groupOf group (coefficient row)
        (LocalAssignmentLoop.assignment groupOf group mask) = (target row).val) ↔
      (fun row => boundedMeasurement groupOf group bound (coefficient row) (norm row)
        (LocalAssignmentLoop.assignment groupOf group mask)) = target := by
    rw [funext_iff]
    apply forall_congr'
    intro row
    exact (boundedMeasurement_eq_iff _ _ _ _ _ _ _).symm
  rw [equal_iff]

/-- A scalar evaluation of D4's right-hand side by variable/group/row scans. -/
def linearValue (groupOf : Fin n → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row) (localCoefficient : Fin n → K)
    (measurementCoefficient : Fin groups → Row → K)
    (target : Fin groups → Row → ℤ) (mask : ℕ) : K :=
  localSum groupOf group (fun v => localCoefficient v.val *
    CountingPolynomial.boolValue (LocalAssignmentLoop.assignment groupOf group mask v)) +
  scanSum (fun g => scanSum (fun row =>
    measurementCoefficient g (rowAt row) * (target g (rowAt row) : K)) 0) 0

theorem linearValue_correct (groupOf : Fin n → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row) (bijective : Function.Bijective rowAt) (bound : ℕ)
    {Inc : Type*} (localCoefficient : Inc → Fin n → K)
    (measurementCoefficient : Inc → Fin groups → Row → K)
    (target : MeasurementTuple (fun _ : Fin groups => Row) bound) (mask : ℕ) (inc : Inc) :
    linearValue groupOf group rowAt (localCoefficient inc) (measurementCoefficient inc)
      (fun g row => (target g row).val) mask =
      localLinearValue groupOf bound localCoefficient measurementCoefficient group inc
        (LocalAssignmentLoop.assignment groupOf group mask) target := by
  simp only [linearValue, localSum_correct, scanSum_correct, add_zero, localLinearValue]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact (Equiv.ofBijective rowAt bijective).sum_comp
    (fun row => measurementCoefficient inc g row * ((target g row).val : K))

/-- One complete local assignment sum with Boolean filters and scalar factors.
The input formula is accessed by its clause/literal indices. -/
def sumGroup (formula : Formula n) (groupOf : Fin n → Fin groups)
    (clauseGroup : Fin formula.clauses.length → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row)
    (measurement : ∀ g, Row → LocalVariable groupOf g → ℤ)
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → Fin groups → Row → K)
    (target : Fin groups → Row → ℤ) (supportBit : Fin n → Bool)
    (correctionValue : FormulaCounter.Incidence formula → K) : K :=
  sumLoop (fun mask =>
    if allowed groupOf group rowAt (measurement group) (target group) supportBit mask then
      groupValue formula clauseGroup group (fun inc =>
        linearValue groupOf group rowAt (localCoefficient inc) (measurementCoefficient inc)
          target mask + correctionValue inc)
    else 0) (2 ^ LocalAssignmentLoop.groupSize groupOf group) 0

open Classical in
theorem sumGroup_correct (formula : Formula n) (groupOf : Fin n → Fin groups)
    (clauseGroup : Fin formula.clauses.length → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row) (bijective : Function.Bijective rowAt)
    (bound : ℕ) (measurement : ∀ g, Row → LocalVariable groupOf g → ℤ)
    (norm : ∀ g row, ∑ v, |measurement g row v| ≤ (bound : ℤ))
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → Fin groups → Row → K)
    (target : MeasurementTuple (fun _ : Fin groups => Row) bound)
    (support : Finset (Fin n)) (supportBit : Fin n → Bool)
    (membership : ∀ v, supportBit v = decide (v ∈ support))
    (correction : FormulaCounter.Incidence formula → Polynomial K) (point : K) :
    sumGroup formula groupOf clauseGroup group rowAt measurement localCoefficient
      measurementCoefficient (fun g row => (target g row).val) supportBit
      (fun inc => (correction inc).eval point) =
    (∑ assignment : LocalAssignment groupOf group,
      if (fun row => boundedMeasurement groupOf group bound (measurement group row)
            (norm group row) assignment) = target group ∧
          localSupport groupOf support group assignment
      then groupFactor formula groupOf clauseGroup bound localCoefficient
        measurementCoefficient correction group assignment target else 0).eval point := by
  classical
  rw [sumGroup, sumLoop_correct, add_zero, PolynomialFacts.eval_finset_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← (LocalAssignmentLoop.assignmentEquiv groupOf group).sum_comp
    (fun assignment =>
      (if (fun row => boundedMeasurement groupOf group bound (measurement group row)
            (norm group row) assignment) = target group ∧
          localSupport groupOf support group assignment
      then groupFactor formula groupOf clauseGroup bound localCoefficient
        measurementCoefficient correction group assignment target else 0).eval point)]
  apply Finset.sum_congr rfl
  intro mask _
  change _ = (if
    (fun row => boundedMeasurement groupOf group bound (measurement group row)
      (norm group row) (LocalAssignmentLoop.assignment groupOf group mask.val)) = target group ∧
      localSupport groupOf support group (LocalAssignmentLoop.assignment groupOf group mask.val)
    then groupFactor formula groupOf clauseGroup bound localCoefficient measurementCoefficient
      correction group (LocalAssignmentLoop.assignment groupOf group mask.val) target
    else (0 : Polynomial K)).eval point
  have accepts_iff := allowed_correct groupOf group rowAt bijective.2 bound
    (measurement group) (norm group) (target group) support supportBit membership mask.val
  by_cases accepts : allowed groupOf group rowAt (measurement group)
      (fun row => (target group row).val) supportBit mask.val = true
  · have yes := accepts_iff.mp accepts
    simp only [ite_eq_left accepts, ite_eq_left yes]
    simp_rw [linearValue_correct _ _ _ bijective bound localCoefficient measurementCoefficient]
    exact groupValue_eq_groupFactor_eval _ _ _ _ _ _ _ _ _ _ _
  · have no := mt accepts_iff.mpr accepts
    simp only [ite_eq_right accepts, ite_eq_right no, Polynomial.eval_zero]

end NtimeDspace.GroupedInnerLoop
