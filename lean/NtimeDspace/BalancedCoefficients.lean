import NtimeDspace.ReciprocalCoefficients
import Mathlib.Data.Nat.Log

/-!
# Balanced reciprocal coefficient trees

The constructor below splits a finite list into two blocks of capacity `2^h`
and pads unused leaves with the neutral factor. Its depth is explicit, and its
denominator and scalar coefficient queries are verified. These are arithmetic
and recursion-tree results, not bounds on the work tape of a machine. In
particular, constructing the list or the tree is not claimed to use small space.
-/

namespace NtimeDspace.HermiteRecovery

open scoped BigOperators

variable {K : Type*} [Field K]

/-- Maximum number of branches on a root-to-leaf path. -/
def ReciprocalFactorTree.depth : ReciprocalFactorTree K → ℕ
  | .one => 0
  | .leaf _ _ => 0
  | .branch left right => max left.depth right.depth + 1

/-- A balanced product tree with `2^height` leaf slots. Extra slots contain the
neutral factor. Correctness requires the input length to fit in those slots. -/
def ReciprocalFactorTree.balanced : ℕ → List (K × ℕ) → ReciprocalFactorTree K
  | 0, [] => .one
  | 0, (a, e) :: _ => .leaf a e
  | height + 1, factors =>
      .branch (balanced height (factors.take (2 ^ height)))
        (balanced height (factors.drop (2 ^ height)))

omit [Field K] in
theorem ReciprocalFactorTree.balanced_depth (height : ℕ) (factors : List (K × ℕ)) :
    (balanced height factors).depth = height := by
  induction height generalizing factors with
  | zero => cases factors <;> rfl
  | succ height ih => simp [balanced, depth, ih]

theorem ReciprocalFactorTree.balanced_valid (height : ℕ) (factors : List (K × ℕ))
    (valid : ∀ factor ∈ factors, factor.1 ≠ 0 ∧ 0 < factor.2) :
    (balanced height factors).Valid := by
  induction height generalizing factors with
  | zero =>
      cases factors with
      | nil => trivial
      | cons factor factors => exact valid factor List.mem_cons_self
  | succ height ih =>
      constructor
      · exact ih _ (fun f hf => valid f (List.mem_of_mem_take hf))
      · exact ih _ (fun f hf => valid f (List.mem_of_mem_drop hf))

/-- Balancing and neutral padding preserve the complete product denominator. -/
theorem ReciprocalFactorTree.balanced_denominator (height : ℕ) (factors : List (K × ℕ))
    (capacity : factors.length ≤ 2 ^ height) :
    (balanced height factors).denominator =
      (factors.map (fun factor => (Polynomial.X + Polynomial.C factor.1) ^ factor.2)).prod := by
  induction height generalizing factors with
  | zero =>
      cases factors with
      | nil => rfl
      | cons factor factors =>
          have hnil : factors = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [pow_zero, List.length_cons] at capacity
            omega
          subst factors
          simp [balanced, denominator]
  | succ height ih =>
      have hleft : (factors.take (2 ^ height)).length ≤ 2 ^ height := by
        simp only [List.length_take]
        exact min_le_left _ _
      have hright : (factors.drop (2 ^ height)).length ≤ 2 ^ height := by
        simp only [List.length_drop]
        rw [pow_succ] at capacity
        omega
      simp only [balanced, denominator, ih _ hleft, ih _ hright]
      rw [← List.prod_append, ← List.map_append, List.take_append_drop]

theorem ReciprocalFactorTree.balanced_coefficient_correct (height : ℕ)
    (factors : List (K × ℕ)) (capacity : factors.length ≤ 2 ^ height)
    (valid : ∀ factor ∈ factors, factor.1 ≠ 0 ∧ 0 < factor.2) (index : ℕ) :
    (balanced height factors).oracle.coefficient index =
      (ofList factors).oracle.coefficient index := by
  rw [coefficient_correct _ (balanced_valid height factors valid),
    coefficient_correct _ (ofList_valid factors valid),
    balanced_denominator height factors capacity, ofList_denominator]

/-- Abstract number of recursive coefficient queries. A leaf counts as one;
each convolution counts itself and its two child queries for every split. This
does not count field operations, bit operations, or machine steps. -/
def ReciprocalFactorTree.queryCalls : ReciprocalFactorTree K → ℕ → ℕ
  | .one, _ => 1
  | .leaf _ _, _ => 1
  | .branch left right, m =>
      1 + sumLoop (fun i => left.queryCalls i + right.queryCalls (m - i)) (m + 1) 0

omit [Field K] in
/-- A depth bound on the actual convolution recursion, with indices restricted
below `order`. Its base `2*order+1` includes the current invocation. -/
theorem ReciprocalFactorTree.balanced_queryCalls_le (height : ℕ)
    (factors : List (K × ℕ)) (order index : ℕ) (below : index < order) :
    (balanced height factors).queryCalls index ≤ (2 * order + 1) ^ height := by
  induction height generalizing factors index with
  | zero => cases factors <;> simp [balanced, queryCalls]
  | succ height ih =>
      rw [balanced, queryCalls, sumLoop_correct, add_zero]
      have hsum :
          (∑ i ∈ Finset.range (index + 1),
            ((balanced height (factors.take (2 ^ height))).queryCalls i +
              (balanced height (factors.drop (2 ^ height))).queryCalls (index - i))) ≤
          (index + 1) * (2 * (2 * order + 1) ^ height) := by
        calc
          _ ≤ ∑ _i ∈ Finset.range (index + 1), 2 * (2 * order + 1) ^ height := by
            apply Finset.sum_le_sum
            intro i hi
            have hleft := ih (factors.take (2 ^ height)) i
              (by have := Finset.mem_range.mp hi; omega)
            have hright := ih (factors.drop (2 ^ height)) (index - i) (by omega)
            omega
          _ = _ := by simp
      have hone : 1 ≤ (2 * order + 1) ^ height := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ]
      nlinarith [Nat.mul_le_mul_right (2 * (2 * order + 1) ^ height)
        (show index + 1 ≤ order by omega)]

/-- Balance all the reciprocal factors of a node weight together, using the
ceiling binary logarithm of the number of factors as the height. -/
def balancedNodeCoefficientTree (node : K) (order : ℕ) (otherNodes : List K) :
    ReciprocalFactorTree K :=
  .balanced (Nat.clog 2 (otherNodes.length + 1))
    ((node, 1) :: otherNodes.map (fun other => (node - other, order)))

/-- Scalar evaluation using the balanced coefficient recursion. -/
def balancedNodeWeightEvaluation (node : K) (order : ℕ) (otherNodes : List K) (z : K) : K :=
  sumLoop (fun index =>
    (balancedNodeCoefficientTree node order otherNodes).oracle.coefficient index * z ^ index)
    order 0

theorem balancedNodeCoefficientTree_depth (node : K) (order : ℕ) (otherNodes : List K) :
    (balancedNodeCoefficientTree node order otherNodes).depth =
      Nat.clog 2 (otherNodes.length + 1) :=
  ReciprocalFactorTree.balanced_depth _ _

theorem balancedNodeCoefficientTree_queryCalls_le (node : K) (order : ℕ)
    (otherNodes : List K) (index : ℕ) (below : index < order) :
    (balancedNodeCoefficientTree node order otherNodes).queryCalls index ≤
      (2 * order + 1) ^ Nat.clog 2 (otherNodes.length + 1) :=
  ReciprocalFactorTree.balanced_queryCalls_le _ _ order index below

noncomputable section

local instance balancedCoefficientsDecidableEq : DecidableEq K := Classical.decEq K

theorem nodeFactors_valid (nodes : Finset K) (node : K) (nonzero : node ≠ 0)
    (order : ℕ) (positive : 0 < order) (otherNodes : List K)
    (enumerates : otherNodes.toFinset = nodes.erase node) :
    ∀ factor ∈ ((node, 1) :: otherNodes.map (fun other => (node - other, order))),
      factor.1 ≠ 0 ∧ 0 < factor.2 := by
  intro factor member
  rcases List.mem_cons.mp member with hhead | htail
  · subst factor
    exact ⟨nonzero, Nat.zero_lt_one⟩
  · obtain ⟨other, hother, rfl⟩ := List.mem_map.mp htail
    have hmem : other ∈ nodes.erase node := by
      rw [← enumerates]
      exact List.mem_toFinset.mpr hother
    exact ⟨sub_ne_zero.mpr (Finset.mem_erase.mp hmem).1.symm, positive⟩

/-- The balanced concrete recursion produces the exact coefficients of the
reciprocal weight used by the multi-node Hermite identity. -/
theorem balancedNodeCoefficientTree_correct (nodes : Finset K) (node : K)
    (nonzero : node ≠ 0) (order : ℕ) (positive : 0 < order)
    (otherNodes : List K) (distinct : otherNodes.Nodup)
    (enumerates : otherNodes.toFinset = nodes.erase node)
    (index : ℕ) (below : index < order) :
    (balancedNodeCoefficientTree node order otherNodes).oracle.coefficient index =
      (nodeWeight nodes node order).coeff index := by
  unfold balancedNodeCoefficientTree
  rw [ReciprocalFactorTree.balanced_coefficient_correct _ _
    (by simpa using Nat.le_pow_clog Nat.one_lt_two (otherNodes.length + 1))
    (nodeFactors_valid nodes node nonzero order positive otherNodes enumerates)]
  exact nodeCoefficientTree_correct nodes node nonzero order positive
    otherNodes distinct enumerates index below

theorem balancedNodeWeightEvaluation_correct (nodes : Finset K) (node : K)
    (nonzero : node ≠ 0) (order : ℕ) (positive : 0 < order)
    (otherNodes : List K) (distinct : otherNodes.Nodup)
    (enumerates : otherNodes.toFinset = nodes.erase node) (z : K) :
    balancedNodeWeightEvaluation node order otherNodes z =
      (nodeWeight nodes node order).eval z := by
  rw [balancedNodeWeightEvaluation, sumLoop_correct, add_zero,
    Polynomial.eval_eq_sum_range' (nodeWeight_degree_lt nodes node order positive)]
  apply Finset.sum_congr rfl
  intro index member
  rw [balancedNodeCoefficientTree_correct nodes node nonzero order positive
    otherNodes distinct enumerates index (Finset.mem_range.mp member)]

omit [Field K] in
theorem otherNodes_length_add_one (nodes : Finset K) (node : K) (member : node ∈ nodes)
    (otherNodes : List K) (distinct : otherNodes.Nodup)
    (enumerates : otherNodes.toFinset = nodes.erase node) :
    otherNodes.length + 1 = nodes.card := by
  rw [← List.toFinset_card_of_nodup distinct, enumerates, Finset.card_erase_of_mem member]
  have := Finset.card_pos.mpr ⟨node, member⟩
  omega

/-- For a `Q`-node interpolation problem, the actual coefficient tree has
exactly `ceil(log₂ Q)` branch levels, including the node's own linear factor. -/
theorem balancedNodeCoefficientTree_depth_eq_clog_card (nodes : Finset K) (node : K)
    (member : node ∈ nodes) (order : ℕ) (otherNodes : List K)
    (distinct : otherNodes.Nodup) (enumerates : otherNodes.toFinset = nodes.erase node) :
    (balancedNodeCoefficientTree node order otherNodes).depth = Nat.clog 2 nodes.card := by
  rw [balancedNodeCoefficientTree_depth,
    otherNodes_length_add_one nodes node member otherNodes distinct enumerates]

/-- The count of arithmetic coefficient invocations in the balanced weight
query. This is separate from machine time and work-tape usage. -/
theorem balancedNodeCoefficientTree_queryCalls_le_card (nodes : Finset K) (node : K)
    (member : node ∈ nodes) (order : ℕ) (otherNodes : List K)
    (distinct : otherNodes.Nodup) (enumerates : otherNodes.toFinset = nodes.erase node)
    (index : ℕ) (below : index < order) :
    (balancedNodeCoefficientTree node order otherNodes).queryCalls index ≤
      (2 * order + 1) ^ Nat.clog 2 nodes.card := by
  have h := balancedNodeCoefficientTree_queryCalls_le node order otherNodes index below
  rwa [otherNodes_length_add_one nodes node member otherNodes distinct enumerates] at h

end

end NtimeDspace.HermiteRecovery
