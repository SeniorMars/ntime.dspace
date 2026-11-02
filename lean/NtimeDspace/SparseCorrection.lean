import NtimeDspace.GroupedAssignmentEvaluation
import NtimeDspace.SupportAssignment

/-!
Scalar evaluation of the sparse Taylor correction. The executing scan receives
only a selected-variable bit accessor and an accessor for coefficient values.
It evaluates each selected coefficient at `node + point` and at `node`, and
accumulates their difference. Polynomial objects and the selected finite set
occur only in the specification and refinement proofs.

The compressed variant first validates the complete support code, including
when there are no declared variables, then recomputes each selected bit through
the streaming ordinal parser. It never constructs a decoded support or subset.
The exact-width theorem uses one mask bit per actual support entry, independently
of the parser's capacity. Coefficient evaluation, parser, and arithmetic costs
still need a work-tape implementation and a resource proof.
-/

namespace NtimeDspace.SparseCorrection

open scoped BigOperators
open GroupedAssignmentEvaluation

variable {n : ℕ} {Inc K : Type*} [CommRing K]

/-- One scalar variable scan, with no polynomial or subset-list input. -/
def correction (evaluateCoefficient : Inc → Fin n → K → K)
    (selected : Fin n → Bool) (node point : K) (inc : Inc) : K :=
  scanSum (fun v => if selected v then
    evaluateCoefficient inc v (node + point) - evaluateCoefficient inc v node else 0) 0

theorem correction_eq_sum (evaluateCoefficient : Inc → Fin n → K → K)
    (selected : Fin n → Bool) (node point : K) (inc : Inc) :
    correction evaluateCoefficient selected node point inc =
      ∑ v, if selected v then
        evaluateCoefficient inc v (node + point) - evaluateCoefficient inc v node else 0 := by
  simp only [correction, scanSum_correct, add_zero]

/-- The polynomial equality is proved from the two accessor contracts; it is
not a premise of the running scalar procedure. -/
theorem correction_correct (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K)
    (evaluateCoefficient : FormulaCounter.Incidence formula → Fin n → K → K)
    (evaluation : ∀ inc v x, evaluateCoefficient inc v x = (L inc.1 inc.2 v).eval x)
    (subset : Finset (Fin n)) (selected : Fin n → Bool)
    (membership : ∀ v, selected v = decide (v ∈ subset))
    (node point : K) (inc : FormulaCounter.Incidence formula) :
    correction evaluateCoefficient selected node point inc =
      (GroupedDeformation.taylorCorrection formula L node subset inc).eval point := by
  rw [correction_eq_sum, GroupedDeformation.taylorCorrection, PolynomialFacts.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro v _
  simp only [membership, decide_eq_true_eq]
  by_cases member : v ∈ subset
  · simp [member, evaluation, Polynomial.taylor_eval, add_comm]
  · simp [member]

/-- The finite set selected by a support mask is a specification, not a
structure constructed by the compressed evaluator. -/
def maskSubset {capacity : ℕ} (support : List (Fin n)) (count : support.length ≤ capacity)
    (mask : Fin capacity → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => SupportAssignment.assignmentBit support count mask v = true)

theorem maskSubset_membership {capacity : ℕ} (support : List (Fin n))
    (count : support.length ≤ capacity) (mask : Fin capacity → Bool) (v : Fin n) :
    SupportAssignment.assignmentBit support count mask v =
      decide (v ∈ maskSubset support count mask) := by
  simp [maskSubset]

theorem maskSubset_subset {capacity : ℕ} (support : List (Fin n))
    (count : support.length ≤ capacity) (mask : Fin capacity → Bool) :
    maskSubset support count mask ⊆ support.toFinset := by
  intro v member
  have selected : SupportAssignment.assignmentBit support count mask v = true :=
    (Finset.mem_filter.mp member).2
  by_contra absent
  have not_member : v ∉ support := by simpa using absent
  simp [SupportAssignment.assignmentBit, not_member] at selected

theorem maskSubset_extendMask {capacity : ℕ} (support : List (Fin n))
    (count : support.length ≤ capacity) (mask : Fin support.length → Bool) :
    maskSubset support count (SupportAssignment.extendMask count mask) =
      maskSubset support (Nat.le_refl _) mask := by
  simp only [maskSubset, SupportAssignment.assignmentBit_extendMask]

/-- Validate even an empty-universe input before querying its variables.
After successful validation all bit queries are defined; `getD false` is used
only to make the scalar accessor total and never rescues an invalid code. -/
def compressed {capacity : ℕ} (evaluateCoefficient : Inc → Fin n → K → K)
    (mask : Fin capacity → Bool) (input : List Bool) (node point : K) (inc : Inc) : Option K :=
  (BoundedSupportParser.lookup n capacity 0 input).map (fun _ =>
    correction evaluateCoefficient
      (fun v => (SupportAssignment.lookupBit mask v input).getD false) node point inc)

/-- Correctness of the compressed scalar evaluator before introducing any
polynomial specification. Both source lists here are proof-side witnesses. -/
theorem compressed_encode {capacity : ℕ} (evaluateCoefficient : Inc → Fin n → K → K)
    (support : List (Fin n)) (valid : SupportAssignment.Valid capacity support)
    (mask : Fin capacity → Bool) (node point : K) (inc : Inc) :
    compressed evaluateCoefficient mask (SupportAssignment.encode support) node point inc =
      some (correction evaluateCoefficient
        (SupportAssignment.assignmentBit support valid.2 mask) node point inc) := by
  have code_valid := (SupportAssignment.positiveSupport_valid_iff support).mpr valid
  have parsed := BoundedSupportParser.lookup_encodeSupport n capacity 0
    (SupportAssignment.positiveSupport support) code_valid.1 code_valid.2.1
    code_valid.2.2.1 code_valid.2.2.2
  unfold compressed
  change (BoundedSupportParser.lookup n capacity 0
    (SupportEncoding.encodeSupport (SupportAssignment.positiveSupport support))).map _ = _
  rw [parsed, Option.map_some]
  simp only [SupportAssignment.lookupBit_encode support valid, Option.getD_some]

/-- Every successful arbitrary code has a unique valid support interpretation;
the scalar result is precisely the correction for that support's mask. -/
theorem compressed_sound_unique {capacity : ℕ}
    (evaluateCoefficient : Inc → Fin n → K → K) (mask : Fin capacity → Bool)
    (input : List Bool) (node point : K) (inc : Inc) (answer : K)
    (accepted : compressed evaluateCoefficient mask input node point inc = some answer) :
    ∃! support : List (Fin n), ∃ valid : SupportAssignment.Valid capacity support,
      input = SupportAssignment.encode support ∧
      answer = correction evaluateCoefficient
        (SupportAssignment.assignmentBit support valid.2 mask) node point inc := by
  cases parsed : BoundedSupportParser.lookup n capacity 0 input with
  | none => simp only [compressed, parsed, Option.map_none] at accepted; contradiction
  | some found =>
      obtain ⟨indices, valid, encoded, _⟩ :=
        BoundedSupportParser.lookup_sound n capacity 0 input found parsed
      obtain ⟨support, support_valid, support_code⟩ :=
        SupportAssignment.exists_variableSupport indices valid
      have code : input = SupportAssignment.encode support := by
        rw [SupportAssignment.encode, support_code]
        exact encoded
      have computed := compressed_encode evaluateCoefficient support support_valid mask node point inc
      have returned : answer = correction evaluateCoefficient
          (SupportAssignment.assignmentBit support support_valid.2 mask) node point inc := by
        apply Option.some.inj
        exact accepted.symm.trans (code ▸ computed)
      refine ⟨support, ⟨support_valid, code, returned⟩, ?_⟩
      rintro other ⟨other_valid, other_code, _⟩
      exact SupportAssignment.encode_injective other_valid support_valid
        (other_code.symm.trans code)

/-- Exact support-width masks feed the polynomial correction without assigning
bits to unused parser-capacity positions. -/
theorem compressed_taylor_correct {capacity : ℕ} (formula : Formula n)
    (L : CountingPolynomial.Coefficients formula K)
    (evaluateCoefficient : FormulaCounter.Incidence formula → Fin n → K → K)
    (evaluation : ∀ inc v x, evaluateCoefficient inc v x = (L inc.1 inc.2 v).eval x)
    (support : List (Fin n)) (valid : SupportAssignment.Valid capacity support)
    (mask : Fin support.length → Bool) (node point : K) (inc : FormulaCounter.Incidence formula) :
    compressed evaluateCoefficient (SupportAssignment.extendMask valid.2 mask)
      (SupportAssignment.encode support) node point inc =
      some ((GroupedDeformation.taylorCorrection formula L node
        (maskSubset support (Nat.le_refl _) mask) inc).eval point) := by
  rcases valid with ⟨ordered, count⟩
  rw [compressed_encode evaluateCoefficient support ⟨ordered, count⟩]
  have selected : SupportAssignment.assignmentBit support count
      (SupportAssignment.extendMask count mask) =
      SupportAssignment.assignmentBit support (Nat.le_refl _) mask := by
    funext v
    exact SupportAssignment.assignmentBit_extendMask support count mask v
  rw [selected]
  congr 1
  exact correction_correct formula L evaluateCoefficient evaluation
    (maskSubset support (Nat.le_refl _) mask)
    (SupportAssignment.assignmentBit support (Nat.le_refl _) mask)
    (maskSubset_membership support (Nat.le_refl _) mask) node point inc

end NtimeDspace.SparseCorrection
