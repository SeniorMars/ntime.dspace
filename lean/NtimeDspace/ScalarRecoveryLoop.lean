import NtimeDspace.IntervalCoefficients
import NtimeDspace.GroupedCounter
import NtimeDspace.GroupedAssignmentEvaluation

/-!
# Indexed scalar Hermite recovery

The executing recovery procedure scans indexed nodes and the nonzero residues
`1, …, p-1`. Reciprocal weights use an indexed factor accessor and interval
coefficient recursion; no factor list, polynomial, or product tree is built.
Proof-side lists certify that the accessor supplies precisely the required
denominator factors. The Taylor-data callback remains an explicit contract.
These arithmetic procedures do not yet assert a machine-space bound.
-/

namespace NtimeDspace.ScalarRecoveryLoop

open scoped BigOperators
open GroupedAssignmentEvaluation

variable {Q p : ℕ} [Fact p.Prime]

/-- Arithmetic rank selection with one distinguished node omitted. -/
def skipNode (node : Fin Q) (slot : Fin (Q - 1)) : Fin Q :=
  ⟨if slot.val < node.val then slot.val else slot.val + 1, by
    have first := node.isLt
    have second := slot.isLt
    split <;> omega⟩

theorem skipNode_ne (node : Fin Q) (slot : Fin (Q - 1)) : skipNode node slot ≠ node := by
  intro same
  have equal := congrArg Fin.val same
  dsimp [skipNode] at equal
  split_ifs at equal <;> omega

theorem skipNode_injective (node : Fin Q) : Function.Injective (skipNode node) := by
  intro first second same
  have equal := congrArg Fin.val same
  apply Fin.ext
  dsimp [skipNode] at equal
  split_ifs at equal <;> omega

theorem skipNode_surjective (node other : Fin Q) (different : other ≠ node) :
    ∃ slot : Fin (Q - 1), skipNode node slot = other := by
  have node_bound := node.isLt
  have other_bound := other.isLt
  have different_values : other.val ≠ node.val := fun same => different (Fin.ext same)
  by_cases before : other.val < node.val
  · refine ⟨⟨other.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [skipNode, before, ite_true]
  · refine ⟨⟨other.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    have after : ¬other.val - 1 < node.val := by omega
    simp only [skipNode, after, ite_false]
    omega

/-- List used only to certify the indexed factors. -/
def otherNodes (nodeValue : Fin Q → ZMod p) (node : Fin Q) : List (ZMod p) :=
  List.ofFn (fun slot : Fin (Q - 1) => nodeValue (skipNode node slot))

omit [Fact p.Prime] in
theorem otherNodes_nodup (nodeValue : Fin Q → ZMod p)
    (distinct : Function.Injective nodeValue) (node : Fin Q) :
    (otherNodes nodeValue node).Nodup :=
  List.nodup_ofFn.mpr (distinct.comp (skipNode_injective node))

omit [Fact p.Prime] in
theorem otherNodes_toFinset (nodeValue : Fin Q → ZMod p)
    (distinct : Function.Injective nodeValue) (node : Fin Q) :
    (otherNodes nodeValue node).toFinset = (Finset.univ.image nodeValue).erase (nodeValue node) := by
  classical
  ext value
  simp only [List.mem_toFinset, otherNodes, List.mem_ofFn, Finset.mem_erase,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨slot, rfl⟩
    exact ⟨fun same => skipNode_ne node slot (distinct same), ⟨skipNode node slot, rfl⟩⟩
  · rintro ⟨different, other, rfl⟩
    obtain ⟨slot, same⟩ := skipNode_surjective node other (fun equal => different (congrArg nodeValue equal))
    exact ⟨slot, congrArg nodeValue same⟩

/-- Slot zero supplies `(node,1)`; subsequent slots skip the distinguished
index and supply `(node-other,order)`. Out-of-range requests have an unused default. -/
def factorAccessor (nodeValue : Fin Q → ZMod p) (node : Fin Q) (order : ℕ) :
    IntervalCoefficients.Factors p
  | 0 => (nodeValue node, 1)
  | slot + 1 =>
    if inside : slot < Q - 1 then
      (nodeValue node - nodeValue (skipNode node ⟨slot, inside⟩), order)
    else (1, 1)

theorem factorAccessor_reads (nodeValue : Fin Q → ZMod p) (node : Fin Q) (order : ℕ)
    (slot : Fin (((nodeValue node, 1) ::
      (otherNodes nodeValue node).map (fun other => (nodeValue node - other, order))).length)) :
    factorAccessor nodeValue node order slot.val =
      ((nodeValue node, 1) ::
        (otherNodes nodeValue node).map (fun other => (nodeValue node - other, order)))[slot.val] := by
  obtain ⟨slot, bound⟩ := slot
  cases slot with
  | zero => rfl
  | succ slot =>
    have inside : slot < Q - 1 := by
      simpa only [List.length_cons, List.length_map, otherNodes, List.length_ofFn,
        Nat.succ_lt_succ_iff] using bound
    simp only [factorAccessor, dite_eq_left inside, List.getElem_cons_succ,
      List.getElem_map, otherNodes, List.getElem_ofFn]

/-- Concrete reciprocal-weight evaluation from indexed scalar factor access. -/
def weight (nodeValue : Fin Q → ZMod p) (node : Fin Q) (order : ℕ) (z : ZMod p) : ZMod p :=
  IntervalCoefficients.weightEvaluation (factorAccessor nodeValue node order) Q order z

theorem weight_correct (nodeValue : Fin Q → ZMod p)
    (distinct : Function.Injective nodeValue) (node : Fin Q) (nonzero : nodeValue node ≠ 0)
    (order : ℕ) (positive : 0 < order) (within : order ≤ p) (z : ZMod p) :
    weight nodeValue node order z =
      (HermiteRecovery.nodeWeight (Finset.univ.image nodeValue) (nodeValue node) order).eval z := by
  have count : (otherNodes nodeValue node).length + 1 = Q := by
    simp only [otherNodes, List.length_ofFn]
    have := node.isLt
    omega
  have correct := IntervalCoefficients.weightEvaluation_correct _ _ nonzero order positive within
    (otherNodes nodeValue node) (otherNodes_nodup nodeValue distinct node)
    (otherNodes_toFinset nodeValue distinct node) (factorAccessor nodeValue node order)
    (factorAccessor_reads nodeValue node order) z
  simpa only [weight, count] using correct

/-- The executing nonzero-residue loop visits the ordinary representatives
`1` through `p-1`, with no finite-field collection stored. -/
def residue (index : Fin (p - 1)) : ZMod p := (index.val + 1 : ℕ)

theorem residue_nonzero (index : Fin (p - 1)) : residue index ≠ 0 := by
  have below : index.val + 1 < p := by have := index.isLt; omega
  intro zero
  have same := congrArg ZMod.val zero
  rw [residue, ZMod.val_natCast_of_lt below, ZMod.val_zero] at same
  omega

/-- Unit-valued version used only to justify the scalar residue loop. -/
def residueUnit (index : Fin (p - 1)) : (ZMod p)ˣ :=
  Units.mk0 (residue index) (residue_nonzero index)

def residueEquiv : Fin (p - 1) ≃ (ZMod p)ˣ where
  toFun := residueUnit
  invFun value := ⟨(value : ZMod p).val - 1, by
    have below := ZMod.val_lt (value : ZMod p)
    have positive : 0 < (value : ZMod p).val :=
      Nat.pos_of_ne_zero (fun zero => value.ne_zero ((ZMod.val_eq_zero _).mp zero))
    omega⟩
  left_inv index := by
    apply Fin.ext
    change (residue index).val - 1 = index.val
    have below : index.val + 1 < p := by have := index.isLt; omega
    rw [residue, ZMod.val_natCast_of_lt below]
    omega
  right_inv value := by
    apply Units.ext
    change (((value : ZMod p).val - 1 + 1 : ℕ) : ZMod p) = (value : ZMod p)
    have positive : 0 < (value : ZMod p).val :=
      Nat.pos_of_ne_zero (fun zero => value.ne_zero ((ZMod.val_eq_zero _).mp zero))
    rw [Nat.sub_add_cancel (by omega), ZMod.natCast_zmod_val]

def sumNonzero (callback : ZMod p → ZMod p) : ZMod p :=
  scanSum (fun index : Fin (p - 1) => callback (residue index)) 0

theorem sumNonzero_correct (callback : ZMod p → ZMod p) :
    sumNonzero callback = ∑ value : (ZMod p)ˣ, callback (value : ZMod p) := by
  rw [sumNonzero, scanSum_correct, add_zero]
  exact (residueEquiv (p := p)).sum_comp (fun value => callback (value : ZMod p))

/-- Scalar value of the node-vanishing product at zero, with its sign intact. -/
def omegaZero (nodeValue : Fin Q → ZMod p) (order : ℕ) : ZMod p :=
  scanProduct (fun node => (-nodeValue node) ^ order) 1

theorem omegaZero_correct (nodeValue : Fin Q → ZMod p)
    (distinct : Function.Injective nodeValue) (order : ℕ) :
    omegaZero nodeValue order =
      (HermiteRecovery.nodeProduct (Finset.univ.image nodeValue) order).eval 0 := by
  rw [omegaZero, scanProduct_correct, mul_one, HermiteRecovery.nodeProduct,
    Polynomial.eval_prod, Finset.prod_image distinct.injOn]
  apply Finset.prod_congr rfl
  intro node _
  simp

/-- The complete outer scalar recovery procedure. The data accessor evaluates
the grouped Taylor data at one node and one nonzero field element at a time. -/
def recover (nodeValue : Fin Q → ZMod p) (order : ℕ)
    (data : Fin Q → ZMod p → ZMod p) : ZMod p :=
  omegaZero nodeValue order *
    scanSum (fun node => sumNonzero (fun z =>
      z ^ (p - order) * weight nodeValue node order z * data node z)) 0

theorem recover_eq_scalar_sum (nodeValue : Fin Q → ZMod p)
    (distinct : Function.Injective nodeValue) (nonzero : ∀ node, nodeValue node ≠ 0)
    (order : ℕ) (positive : 0 < order) (within : order ≤ p)
    (data : Fin Q → ZMod p → ZMod p) :
    recover nodeValue order data =
      (HermiteRecovery.nodeProduct (Finset.univ.image nodeValue) order).eval 0 *
        ∑ node : Fin Q, ∑ z : (ZMod p)ˣ,
          (z : ZMod p) ^ (p - order) *
            (HermiteRecovery.nodeWeight (Finset.univ.image nodeValue) (nodeValue node) order).eval
              (z : ZMod p) * data node (z : ZMod p) := by
  rw [recover, omegaZero_correct nodeValue distinct, scanSum_correct, add_zero]
  apply congrArg (fun value : ZMod p =>
    (HermiteRecovery.nodeProduct (Finset.univ.image nodeValue) order).eval 0 * value)
  apply Finset.sum_congr rfl
  intro node _
  rw [sumNonzero_correct]
  apply Finset.sum_congr rfl
  intro z _
  rw [weight_correct nodeValue distinct node (nonzero node) order positive within]

set_option maxHeartbeats 1000000 in
/-- Accessor refinement into the paper's concrete grouped scalar expression.
Reciprocal-weight correctness, node-product evaluation, and nonzero-residue
enumeration are proved above; only the grouped-data callback needs a contract. -/
theorem recover_eq_groupedScalarExpression {n r : ℕ} {Copy : Type*}
    [Fintype Copy] [DecidableEq Copy]
    (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → ConcreteGroupedDeformation.Label (Fin Q) r)
    (variableGroup : Fin Q → Fin n → Fin r)
    (clauseGroup : Fin Q → Fin formula.clauses.length → Fin r)
    (nodeValue : Fin Q → ZMod p)
    (distinct : Function.Injective nodeValue) (nonzero : ∀ node, nodeValue node ≠ 0)
    (start : ℤ) (width order : ℕ) (positive : 0 < order) (within : order ≤ p)
    (data : Fin Q → ZMod p → ZMod p)
    (agrees : ∀ node z, data node z =
      (GroupedCounter.groupedNodePolynomial formula fallback copyOf labelOf variableGroup clauseGroup
        nodeValue start width order node).eval z) :
    recover nodeValue order data =
      GroupedCounter.groupedScalarExpression formula fallback copyOf labelOf
        variableGroup clauseGroup nodeValue start width order := by
  rw [recover_eq_scalar_sum nodeValue distinct nonzero order positive within data]
  unfold GroupedCounter.groupedScalarExpression
  apply congrArg (fun value : ZMod p =>
    (HermiteRecovery.nodeProduct (Finset.univ.image nodeValue) order).eval 0 * value)
  apply Finset.sum_congr rfl
  intro node _
  apply Finset.sum_congr rfl
  intro z _
  rw [agrees node (z : ZMod p)]

end NtimeDspace.ScalarRecoveryLoop
