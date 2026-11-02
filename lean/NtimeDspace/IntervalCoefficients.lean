import NtimeDspace.ModularBinomial
import NtimeDspace.BalancedCoefficients
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Reciprocal coefficient queries from indexed intervals

The arithmetic procedure stores neither a factor list nor a product tree.
It receives an indexed factor accessor and recursively divides a power-of-two
interval. Leaves outside the factor count contribute the neutral series;
other leaves use the modular binomial loop. The convolution uses a scalar
accumulator and requests just one coefficient at a time.

A tree and a finite product occur only in the specification and proofs. The
depth and query-count results measure this arithmetic recursion, not machine
steps or visited work-tape cells. Accessor costs and an explicit stack/machine
implementation remain separate obligations.
-/

namespace NtimeDspace.IntervalCoefficients

open scoped BigOperators
open HermiteRecovery

variable {p : ℕ} [Fact p.Prime]

/-- One indexed factor consists of its nonzero field constant and positive
multiplicity. Validity is required only for slots below `count`. -/
abbrev Factors (p : ℕ) := ℕ → ZMod p × ℕ

def Valid (factor : Factors p) (count : ℕ) : Prop :=
  ∀ slot < count, (factor slot).1 ≠ 0 ∧ 0 < (factor slot).2

/-- On-demand interval convolution. No list, polynomial, or tree is an input
or an intermediate object of this definition. -/
def coefficient (factor : Factors p) (count : ℕ) : ℕ → ℕ → ℕ → ZMod p
  | 0, start, index =>
      if start < count then
        modularReciprocalCoefficient (factor start).1 (factor start).2 index
      else if index = 0 then 1 else 0
  | height + 1, start, index =>
      sumLoop (fun split =>
        coefficient factor count height start split *
          coefficient factor count height (start + 2 ^ height) (index - split))
        (index + 1) 0

/-- Proof-only materialization into the existing reciprocal-tree semantics. -/
def specificationTree (factor : Factors p) (count : ℕ) : ℕ → ℕ → ReciprocalFactorTree (ZMod p)
  | 0, start =>
      if start < count then .leaf (factor start).1 (factor start).2 else .one
  | height + 1, start =>
      .branch (specificationTree factor count height start)
        (specificationTree factor count height (start + 2 ^ height))

theorem specificationTree_valid (factor : Factors p) (count : ℕ) (valid : Valid factor count)
    (height start : ℕ) : (specificationTree factor count height start).Valid := by
  induction height generalizing start with
  | zero =>
      simp only [specificationTree]
      split_ifs with inside
      · exact valid start inside
      · trivial
  | succ height ih => exact ⟨ih start, ih (start + 2 ^ height)⟩

/-- The interval procedure agrees with the existing arithmetic tree without
constructing that tree during the procedure. -/
theorem coefficient_eq_tree (factor : Factors p) (count : ℕ) (valid : Valid factor count)
    (height start index : ℕ) (below : index < p) :
    coefficient factor count height start index =
      (specificationTree factor count height start).oracle.coefficient index := by
  induction height generalizing start index with
  | zero =>
      by_cases inside : start < count
      · simpa only [coefficient, specificationTree, ite_eq_left inside,
          ReciprocalFactorTree.oracle, CoefficientTree.coefficient] using
          modularReciprocalCoefficient_eq (factor start).1 (factor start).2 index
            (valid start inside).2 below
      · simp [coefficient, specificationTree, inside, ReciprocalFactorTree.oracle,
          CoefficientTree.coefficient]
  | succ height ih =>
      simp only [coefficient, specificationTree, ReciprocalFactorTree.oracle,
        CoefficientTree.coefficient, sumLoop_correct, add_zero]
      apply Finset.sum_congr rfl
      intro split member
      have split_le : split ≤ index := by
        have := Finset.mem_range.mp member
        omega
      rw [ih start split (split_le.trans_lt below),
        ih (start + 2 ^ height) (index - split) ((Nat.sub_le _ _).trans_lt below)]

/-- Each occupied leaf's denominator; padding slots contribute one. -/
noncomputable def factorPolynomial (factor : Factors p) (count slot : ℕ) : Polynomial (ZMod p) :=
  if slot < count then (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2 else 1

theorem specificationTree_denominator (factor : Factors p) (count height start : ℕ) :
    (specificationTree factor count height start).denominator =
      ∏ slot ∈ Finset.Ico start (start + 2 ^ height), factorPolynomial factor count slot := by
  induction height generalizing start with
  | zero =>
      simp only [specificationTree, pow_zero, Nat.Ico_succ_singleton, Finset.prod_singleton]
      split_ifs with inside <;> simp [ReciprocalFactorTree.denominator, factorPolynomial, inside]
  | succ height ih =>
      rw [specificationTree, ReciprocalFactorTree.denominator, ih, ih]
      have split := Finset.prod_Ico_consecutive (factorPolynomial factor count)
        (m := start) (n := start + 2 ^ height) (k := start + 2 ^ height + 2 ^ height)
        (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      simpa only [pow_succ, Nat.mul_two, Nat.add_assoc] using split

/-- Correctness against an explicit finite product of reciprocal factors. -/
theorem coefficient_correct (factor : Factors p) (count : ℕ) (valid : Valid factor count)
    (height start index : ℕ) (below : index < p) :
    coefficient factor count height start index =
      PowerSeries.coeff index
        (((∏ slot ∈ Finset.Ico start (start + 2 ^ height),
          factorPolynomial factor count slot : Polynomial (ZMod p)) : PowerSeries (ZMod p))⁻¹) := by
  rw [coefficient_eq_tree factor count valid height start index below,
    ReciprocalFactorTree.coefficient_correct _ (specificationTree_valid factor count valid height start),
    specificationTree_denominator]

omit [Fact p.Prime] in
/-- Exact branch depth, including the neutral padding leaves. -/
theorem specificationTree_depth (factor : Factors p) (count height start : ℕ) :
    (specificationTree factor count height start).depth = height := by
  induction height generalizing start with
  | zero => simp only [specificationTree]; split_ifs <;> rfl
  | succ height ih => simp [specificationTree, ReciprocalFactorTree.depth, ih]

/-- Number of recursive coefficient invocations, counting the current call. -/
def queryCalls : ℕ → ℕ → ℕ
  | 0, _ => 1
  | height + 1, index =>
      1 + sumLoop (fun split => queryCalls height split + queryCalls height (index - split))
        (index + 1) 0

omit [Fact p.Prime] in
theorem queryCalls_eq_tree (factor : Factors p) (count height start index : ℕ) :
    queryCalls height index = (specificationTree factor count height start).queryCalls index := by
  induction height generalizing start index with
  | zero => simp only [specificationTree]; split_ifs <;> rfl
  | succ height ih =>
      simp only [queryCalls, specificationTree, ReciprocalFactorTree.queryCalls,
        sumLoop_correct, add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro split _
      rw [ih start split, ih (start + 2 ^ height) (index - split)]

/-- A direct bound on the actual interval recursion's coefficient invocations. -/
theorem queryCalls_le (height order index : ℕ) (below : index < order) :
    queryCalls height index ≤ (2 * order + 1) ^ height := by
  induction height generalizing index with
  | zero => simp [queryCalls]
  | succ height ih =>
      rw [queryCalls, sumLoop_correct, add_zero]
      have hsum :
          (∑ split ∈ Finset.range (index + 1),
            (queryCalls height split + queryCalls height (index - split))) ≤
          (index + 1) * (2 * (2 * order + 1) ^ height) := by
        calc
          _ ≤ ∑ _split ∈ Finset.range (index + 1), 2 * (2 * order + 1) ^ height := by
            apply Finset.sum_le_sum
            intro split member
            have left := ih split (by have := Finset.mem_range.mp member; omega)
            have right := ih (index - split) (by omega)
            omega
          _ = _ := by simp
      have hone : 1 ≤ (2 * order + 1) ^ height := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ]
      nlinarith [Nat.mul_le_mul_right (2 * (2 * order + 1) ^ height)
        (show index + 1 ≤ order by omega)]

/-- Query all factors, supplying the balancing depth as one small integer. -/
def allCoefficient (factor : Factors p) (count index : ℕ) : ZMod p :=
  coefficient factor count (Nat.clog 2 count) 0 index

/-- Padding the last interval with neutral factors does not change the product. -/
theorem padded_product (factor : Factors p) (count capacity : ℕ) (fits : count ≤ capacity) :
    (∏ slot ∈ Finset.range capacity, factorPolynomial factor count slot) =
      ∏ slot ∈ Finset.range count,
        (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2 := by
  calc
    _ = ∏ slot ∈ Finset.range count, factorPolynomial factor count slot := by
      symm
      apply Finset.prod_subset (Finset.range_mono fits)
      intro slot _ outside
      simp only [Finset.mem_range, not_lt] at outside
      simp [factorPolynomial, Nat.not_lt_of_ge outside]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro slot inside
      simp [factorPolynomial, Finset.mem_range.mp inside]

/-- The public indexed procedure returns the coefficient of the inverse of
the product of exactly the supplied factors, including the empty product. -/
theorem allCoefficient_correct (factor : Factors p) (count : ℕ) (valid : Valid factor count)
    (index : ℕ) (below : index < p) :
    allCoefficient factor count index =
      PowerSeries.coeff index
        (((∏ slot ∈ Finset.range count,
          (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2 :
          Polynomial (ZMod p)) : PowerSeries (ZMod p))⁻¹) := by
  rw [allCoefficient, coefficient_correct factor count valid _ _ index below]
  simp only [Nat.zero_add, Nat.Ico_zero_eq_range]
  rw [padded_product factor count _ (Nat.le_pow_clog Nat.one_lt_two count)]

theorem allCoefficient_queryCalls_le (count order index : ℕ) (below : index < order) :
    queryCalls (Nat.clog 2 count) index ≤ (2 * order + 1) ^ Nat.clog 2 count :=
  queryCalls_le _ _ _ below

/-- An accessor's product agrees with any list presenting the same factors.
The list is a semantic witness and is not passed to `allCoefficient`. -/
theorem factor_product_eq_list (factor : Factors p) (factors : List (ZMod p × ℕ))
    (reads : ∀ slot : Fin factors.length, factor slot.val = factors[slot.val]) :
    (∏ slot ∈ Finset.range factors.length,
      (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2) =
      (factors.map (fun item => (Polynomial.X + Polynomial.C item.1) ^ item.2)).prod := by
  rw [Finset.prod_range, ← List.prod_ofFn]
  have same :
      (fun slot : Fin factors.length =>
        (Polynomial.X + Polynomial.C (factor slot.val).1) ^ (factor slot.val).2) =
      (fun slot : Fin factors.length =>
        (Polynomial.X + Polynomial.C factors[slot.val].1) ^ factors[slot.val].2) := by
    funext slot
    rw [reads slot]
  rw [same]
  exact congrArg List.prod (List.ofFn_getElem_eq_map factors
    (fun item => (Polynomial.X + Polynomial.C item.1) ^ item.2))

/-- Direct replacement theorem for the earlier balanced-list coefficient
procedure. Its factor list and product tree are absent from the new procedure. -/
theorem allCoefficient_eq_balanced (factor : Factors p) (factors : List (ZMod p × ℕ))
    (valid : Valid factor factors.length)
    (reads : ∀ slot : Fin factors.length, factor slot.val = factors[slot.val])
    (index : ℕ) (below : index < p) :
    allCoefficient factor factors.length index =
      (ReciprocalFactorTree.balanced (Nat.clog 2 factors.length) factors).oracle.coefficient index := by
  have list_valid : ∀ item ∈ factors, item.1 ≠ 0 ∧ 0 < item.2 := by
    intro item member
    obtain ⟨slot, same⟩ := List.mem_iff_get.mp member
    have represented : factor slot.val = item := (reads slot).trans same
    simpa only [represented] using valid slot.val slot.isLt
  rw [ReciprocalFactorTree.balanced_coefficient_correct _ _
    (Nat.le_pow_clog Nat.one_lt_two factors.length) list_valid,
    ReciprocalFactorTree.coefficient_correct _ (ReciprocalFactorTree.ofList_valid factors list_valid),
    ReciprocalFactorTree.ofList_denominator,
    allCoefficient_correct factor factors.length valid index below,
    factor_product_eq_list factor factors reads]

/-- Evaluate the truncated reciprocal by computing one coefficient at a time.
The executable inputs remain just the accessor and scalar parameters. -/
def weightEvaluation (factor : Factors p) (count order : ℕ) (z : ZMod p) : ZMod p :=
  sumLoop (fun index => allCoefficient factor count index * z ^ index) order 0

/-- An accessor presenting the node's factors computes the exact Hermite
weight. `otherNodes` is a proof witness, not an input to `weightEvaluation`. -/
theorem weightEvaluation_correct (nodes : Finset (ZMod p)) (node : ZMod p)
    (nonzero : node ≠ 0) (order : ℕ) (positive : 0 < order) (within : order ≤ p)
    (otherNodes : List (ZMod p)) (distinct : otherNodes.Nodup)
    (enumerates : otherNodes.toFinset = nodes.erase node) (factor : Factors p)
    (reads : ∀ slot : Fin (((node, 1) :: otherNodes.map (fun other => (node - other, order))).length),
      factor slot.val = ((node, 1) :: otherNodes.map (fun other => (node - other, order)))[slot.val])
    (z : ZMod p) :
    weightEvaluation factor (otherNodes.length + 1) order z =
      (nodeWeight nodes node order).eval z := by
  let factors := (node, 1) :: otherNodes.map (fun other => (node - other, order))
  have valid_list : ∀ item ∈ factors, item.1 ≠ 0 ∧ 0 < item.2 :=
    nodeFactors_valid nodes node nonzero order positive otherNodes (by
      ext value
      simpa only [List.mem_toFinset, Finset.mem_erase] using Finset.ext_iff.mp enumerates value)
  have valid : Valid factor factors.length := by
    intro slot inside
    have same := reads ⟨slot, inside⟩
    rw [same]
    exact valid_list _ (List.getElem_mem inside)
  rw [← balancedNodeWeightEvaluation_correct nodes node nonzero order positive
    otherNodes distinct (by
      ext value
      simpa only [List.mem_toFinset, Finset.mem_erase] using Finset.ext_iff.mp enumerates value) z]
  simp only [weightEvaluation, balancedNodeWeightEvaluation, sumLoop_correct, add_zero]
  apply Finset.sum_congr rfl
  intro index member
  have below : index < p := (Finset.mem_range.mp member).trans_le within
  have equals := allCoefficient_eq_balanced factor factors valid reads index below
  simpa only [factors, List.length_cons, List.length_map, balancedNodeCoefficientTree] using
    congrArg (fun value => value * z ^ index) equals

/-! The following describe the requests and continuations of the recursion.
They provide bounded representations for a future explicit stack evaluator;
they are not themselves an operational machine simulation. -/

structure Request where
  height : ℕ
  start : ℕ
  degree : ℕ
  deriving DecidableEq

/-- Exactly the two recursive requests made for a valid convolution split. -/
inductive Child : Request → Request → Prop
  | left (height start degree split : ℕ) (bounded : split ≤ degree) :
      Child ⟨height + 1, start, degree⟩ ⟨height, start, split⟩
  | right (height start degree split : ℕ) (bounded : split ≤ degree) :
      Child ⟨height + 1, start, degree⟩ ⟨height, start + 2 ^ height, degree - split⟩

theorem Child.bounds {parent child : Request} (descends : Child parent child) :
    child.height + 1 = parent.height ∧ parent.start ≤ child.start ∧
      child.start + 2 ^ child.height ≤ parent.start + 2 ^ parent.height ∧
      child.degree ≤ parent.degree := by
  cases descends with
  | left height start degree split bounded =>
      change height + 1 = height + 1 ∧ start ≤ start ∧
        start + 2 ^ height ≤ start + 2 ^ (height + 1) ∧ split ≤ degree
      refine ⟨rfl, le_rfl, ?_, bounded⟩
      rw [pow_succ, Nat.mul_two]
      exact Nat.add_le_add_left (Nat.le_add_right _ _) _
  | right height start degree split bounded =>
      change height + 1 = height + 1 ∧ start ≤ start + 2 ^ height ∧
        start + 2 ^ height + 2 ^ height ≤ start + 2 ^ (height + 1) ∧ degree - split ≤ degree
      refine ⟨rfl, Nat.le_add_right _ _, ?_, Nat.sub_le _ _⟩
      simp only [pow_succ, Nat.mul_two, Nat.add_assoc, le_refl]

/-- An active root-to-leaf call chain, including the currently evaluated call. -/
inductive CallChain : Request → List Request → Prop
  | single (request : Request) : CallChain request [request]
  | descend {parent child : Request} {requests : List Request}
      (step : Child parent child) (rest : CallChain child requests) :
      CallChain parent (parent :: requests)

theorem CallChain.length_le {root : Request} {requests : List Request}
    (chain : CallChain root requests) : requests.length ≤ root.height + 1 := by
  induction chain with
  | single request => simp
  | @descend parent child requests step rest ih =>
      have height := step.bounds.1
      simp only [List.length_cons]
      omega

/-- Every descendant stays within the original interval and never increases
the requested coefficient degree. -/
theorem CallChain.request_bounds {root : Request} {requests : List Request}
    (chain : CallChain root requests) (request : Request) (member : request ∈ requests) :
    request.height ≤ root.height ∧ root.start ≤ request.start ∧
      request.start + 2 ^ request.height ≤ root.start + 2 ^ root.height ∧
      request.degree ≤ root.degree := by
  induction chain with
  | single root =>
      have same : request = root := List.mem_singleton.mp member
      subst request
      simp
  | @descend parent child requests step rest ih =>
      rcases List.mem_cons.mp member with same | tail
      · subst request
        simp
      · obtain ⟨height, start, finish, degree⟩ := ih tail
        obtain ⟨child_height, child_start, child_finish, child_degree⟩ := step.bounds
        exact ⟨by omega, child_start.trans start, finish.trans child_finish,
          degree.trans child_degree⟩

/-- A continuation needs a request, current split, accumulator, saved left
result, and a phase bit; all of these have finite bounded representations. -/
structure Frame (p : ℕ) where
  request : Request
  split : ℕ
  accumulator : ZMod p
  leftResult : ZMod p
  awaitingRight : Bool

abbrev EncodedFrame (height capacity order p : ℕ) :=
  Fin (height + 1) × Fin capacity × Fin order × Fin order × ZMod p × ZMod p × Bool

def decodeFrame {height capacity order : ℕ} (frame : EncodedFrame height capacity order p) : Frame p :=
  ⟨⟨frame.1.val, frame.2.1.val, frame.2.2.1.val⟩,
    frame.2.2.2.1.val, frame.2.2.2.2.1, frame.2.2.2.2.2.1, frame.2.2.2.2.2.2⟩

/-- The representation includes two field registers, rather than hiding a
left result in the recursion evaluator's call stack. -/
def encodeFrame {height capacity order : ℕ} (frame : Frame p)
    (bounds : frame.request.height ≤ height ∧ frame.request.start < capacity ∧
      frame.request.degree < order ∧ frame.split ≤ frame.request.degree) :
    EncodedFrame height capacity order p :=
  (⟨frame.request.height, by omega⟩, ⟨frame.request.start, bounds.2.1⟩,
    ⟨frame.request.degree, bounds.2.2.1⟩,
    ⟨frame.split, bounds.2.2.2.trans_lt bounds.2.2.1⟩,
    frame.accumulator, frame.leftResult, frame.awaitingRight)

omit [Fact p.Prime] in
theorem decodeFrame_encodeFrame {height capacity order : ℕ} (frame : Frame p)
    (bounds : frame.request.height ≤ height ∧ frame.request.start < capacity ∧
      frame.request.degree < order ∧ frame.split ≤ frame.request.degree) :
    decodeFrame (encodeFrame frame bounds) = frame := rfl

omit [Fact p.Prime] in
/-- Frames of every possible recursive call chain fit the same bounded
descriptor type; only scalar registers are added to the request coordinates. -/
theorem frame_encodable {root : Request} {requests : List Request}
    (chain : CallChain root requests) (frame : Frame p) (member : frame.request ∈ requests)
    (order : ℕ) (below : root.degree < order) (split_bound : frame.split ≤ frame.request.degree) :
    ∃ encoded : EncodedFrame root.height (root.start + 2 ^ root.height) order p,
      decodeFrame encoded = frame := by
  obtain ⟨height, start, finish, degree⟩ := chain.request_bounds frame.request member
  have width_positive : 0 < 2 ^ frame.request.height := Nat.two_pow_pos _
  have bounds : frame.request.height ≤ root.height ∧
      frame.request.start < root.start + 2 ^ root.height ∧
      frame.request.degree < order ∧ frame.split ≤ frame.request.degree := by
    exact ⟨height, by omega, degree.trans_lt below, split_bound⟩
  exact ⟨encodeFrame frame bounds, decodeFrame_encodeFrame frame bounds⟩

theorem encodedFrame_card (height capacity order : ℕ) :
    Fintype.card (EncodedFrame height capacity order p) =
      2 * (height + 1) * capacity * order ^ 2 * p ^ 2 := by
  simp only [EncodedFrame, Fintype.card_prod, Fintype.card_fin, ZMod.card, Fintype.card_bool]
  ring

end NtimeDspace.IntervalCoefficients
