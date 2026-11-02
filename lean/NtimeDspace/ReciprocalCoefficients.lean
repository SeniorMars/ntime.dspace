import NtimeDspace.HermiteRecovery
import NtimeDspace.CoefficientRecursion
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Concrete reciprocal coefficients

This file connects finite arithmetic formulas for reciprocal coefficients to the
actual power-series inverses used by the Hermite weights. It proves arithmetic
correctness, without asserting a compiled machine or a workspace bound.
-/

namespace NtimeDspace.HermiteRecovery

open scoped BigOperators

variable {K : Type*} [Field K]

/-- The scalar leaf formula in the paper. The correctness theorem requires a
positive multiplicity; the zero-multiplicity case is not represented here. -/
def reciprocalCoefficient (a : K) (multiplicity index : ℕ) : K :=
  (-1) ^ index * (Nat.choose (multiplicity + index - 1) index : K) *
    (a⁻¹) ^ (multiplicity + index)

/-- A rescaled negative-binomial series is the actual inverse of `(a+X)^e`. -/
theorem linear_power_inverse_eq (a : K) (nonzero : a ≠ 0) (e : ℕ) :
    ((PowerSeries.C a + PowerSeries.X : PowerSeries K) ^ e)⁻¹ =
      PowerSeries.C ((a⁻¹) ^ e) *
        PowerSeries.rescale (-a⁻¹) (PowerSeries.invOneSubPow K e).val := by
  let r := PowerSeries.rescale (-a⁻¹)
  have hunit := (PowerSeries.invOneSubPow K e).val_inv
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at hunit
  have hr := congrArg r hunit
  simp only [map_mul, map_pow, map_one] at hr
  have hlinear : PowerSeries.C a * r (1 - PowerSeries.X) =
      (PowerSeries.C a + PowerSeries.X : PowerSeries K) := by
    dsimp [r]
    rw [map_sub, map_one, PowerSeries.rescale_X]
    calc
      _ = PowerSeries.C a + PowerSeries.C (a * a⁻¹) * PowerSeries.X := by
        simp only [map_neg, map_mul]
        ring
      _ = _ := by rw [mul_inv_cancel₀ nonzero, map_one, one_mul]
  have hfactor : (PowerSeries.C a + PowerSeries.X : PowerSeries K) ^ e =
      PowerSeries.C (a ^ e) * r (1 - PowerSeries.X) ^ e := by
    rw [← hlinear, mul_pow, map_pow]
  apply PowerSeries.inv_eq_iff_mul_eq_one
    (by simpa using pow_ne_zero e nonzero) |>.mpr
  rw [hfactor]
  change (PowerSeries.C ((a⁻¹) ^ e) * r (PowerSeries.invOneSubPow K e).val) *
    (PowerSeries.C (a ^ e) * r (1 - PowerSeries.X) ^ e) = 1
  calc
    _ = PowerSeries.C ((a⁻¹) ^ e * a ^ e) *
        (r (PowerSeries.invOneSubPow K e).val * r (1 - PowerSeries.X) ^ e) := by
      rw [map_mul]
      ring
    _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ nonzero, one_pow, map_one, hr, one_mul]

/-- The closed scalar formula computes every coefficient of the formal inverse
of a positive power of a nonzero linear factor, over any field. -/
theorem reciprocalCoefficient_correct (a : K) (nonzero : a ≠ 0)
    (multiplicity index : ℕ) (positive : 0 < multiplicity) :
    reciprocalCoefficient a multiplicity index =
      PowerSeries.coeff index
        (((PowerSeries.C a + PowerSeries.X : PowerSeries K) ^ multiplicity)⁻¹) := by
  rw [linear_power_inverse_eq a nonzero multiplicity,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos K multiplicity positive,
    PowerSeries.coeff_mk]
  have hindex : multiplicity + index - 1 = multiplicity - 1 + index := by omega
  rw [reciprocalCoefficient, hindex, Nat.choose_symm_add]
  rw [neg_pow, pow_add]
  ring

/-- The concrete scalar formula can be used as a leaf of the previously checked
coefficient recursion, agreeing with the truncated inverse below its order. -/
theorem reciprocalCoefficient_representsBelow (a : K) (nonzero : a ≠ 0)
    (multiplicity order : ℕ) (positive : 0 < multiplicity) :
    CoefficientTree.RepresentsBelow order
      (.leaf (reciprocalCoefficient a multiplicity))
      (truncatedInverse ((Polynomial.X + Polynomial.C a) ^ multiplicity) order) := by
  apply CoefficientTree.RepresentsBelow.leaf
  intro m hm
  rw [truncatedInverse, PowerSeries.coeff_trunc, if_pos hm,
    reciprocalCoefficient_correct a nonzero multiplicity m positive]
  simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X,
    Polynomial.coe_C, add_comm]

/-- A finite factorization with scalar data at its leaves. Unlike a polynomial
coefficient oracle, each leaf is specified by just a field element and an exponent. -/
inductive ReciprocalFactorTree (K : Type*) where
  | one : ReciprocalFactorTree K
  | leaf : K → ℕ → ReciprocalFactorTree K
  | branch : ReciprocalFactorTree K → ReciprocalFactorTree K → ReciprocalFactorTree K

/-- The arithmetic oracle uses the existing scalar-accumulator convolution. -/
def ReciprocalFactorTree.oracle : ReciprocalFactorTree K → CoefficientTree K
  | .one => .leaf (fun m => if m = 0 then 1 else 0)
  | .leaf a e => .leaf (reciprocalCoefficient a e)
  | .branch left right => .branch left.oracle right.oracle

/-- Polynomial semantics are used in proofs only, and are not passed to the
arithmetic coefficient procedure. -/
noncomputable def ReciprocalFactorTree.denominator : ReciprocalFactorTree K → Polynomial K
  | .one => 1
  | .leaf a e => (Polynomial.X + Polynomial.C a) ^ e
  | .branch left right => left.denominator * right.denominator

def ReciprocalFactorTree.Valid : ReciprocalFactorTree K → Prop
  | .one => True
  | .leaf a e => a ≠ 0 ∧ 0 < e
  | .branch left right => left.Valid ∧ right.Valid

/-- Every requested coefficient returned by the finite arithmetic tree equals
the coefficient of the actual reciprocal of its polynomial denominator. -/
theorem ReciprocalFactorTree.coefficient_correct (tree : ReciprocalFactorTree K)
    (valid : tree.Valid) (m : ℕ) :
    tree.oracle.coefficient m =
      PowerSeries.coeff m ((tree.denominator : PowerSeries K)⁻¹) := by
  induction tree generalizing m with
  | one => simp [oracle, CoefficientTree.coefficient, denominator, PowerSeries.coeff_one]
  | leaf a e =>
      rw [oracle, CoefficientTree.coefficient,
        reciprocalCoefficient_correct a valid.1 e m valid.2]
      simp only [denominator, Polynomial.coe_pow, Polynomial.coe_add,
        Polynomial.coe_X, Polynomial.coe_C, add_comm]
  | branch left right ihLeft ihRight =>
      simp only [oracle, CoefficientTree.coefficient, sumLoop_correct, add_zero,
        denominator, Polynomial.coe_mul, PowerSeries.mul_inv_rev]
      rw [mul_comm, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i ((left.denominator : PowerSeries K)⁻¹) *
            PowerSeries.coeff j ((right.denominator : PowerSeries K)⁻¹)) m]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ihLeft valid.1, ihRight valid.2]

/-- Build a product tree from an explicit list of factor data. This simple
constructor is not claimed to give the balanced shape used for the space bound. -/
def ReciprocalFactorTree.ofList : List (K × ℕ) → ReciprocalFactorTree K
  | [] => .one
  | (a, e) :: factors => .branch (.leaf a e) (ofList factors)

theorem ReciprocalFactorTree.ofList_valid (factors : List (K × ℕ))
    (valid : ∀ factor ∈ factors, factor.1 ≠ 0 ∧ 0 < factor.2) :
    (ofList factors).Valid := by
  induction factors with
  | nil => trivial
  | cons factor factors ih =>
      exact ⟨valid factor List.mem_cons_self, ih (fun f hf => valid f (List.mem_cons_of_mem _ hf))⟩

theorem ReciprocalFactorTree.ofList_denominator (factors : List (K × ℕ)) :
    (ofList factors).denominator =
      (factors.map (fun factor => (Polynomial.X + Polynomial.C factor.1) ^ factor.2)).prod := by
  induction factors with
  | nil => rfl
  | cons factor factors ih => simp [ofList, denominator, ih]

/-- A coefficient tree for the actual Hermite weight, given an explicit
enumeration of the other nodes. It has only finite scalar data at its leaves. -/
def nodeCoefficientTree (node : K) (order : ℕ) (otherNodes : List K) : ReciprocalFactorTree K :=
  .branch (.leaf node 1)
    (.ofList (otherNodes.map (fun other => (node - other, order))))

/-- Evaluate the truncated weight by accumulating scalar coefficient queries.
The definition never constructs a polynomial or a coefficient array. -/
def nodeWeightEvaluation (node : K) (order : ℕ) (otherNodes : List K) (z : K) : K :=
  sumLoop (fun index =>
    (nodeCoefficientTree node order otherNodes).oracle.coefficient index * z ^ index) order 0

noncomputable section

local instance reciprocalCoefficientsDecidableEq : DecidableEq K := Classical.decEq K

theorem nodeCoefficientTree_denominator (nodes : Finset K) (node : K) (order : ℕ)
    (otherNodes : List K) (distinct : otherNodes.Nodup)
    (enumerates : otherNodes.toFinset = nodes.erase node) :
    (nodeCoefficientTree node order otherNodes).denominator =
      nodeDenominator nodes node order := by
  simp only [nodeCoefficientTree, ReciprocalFactorTree.denominator,
    ReciprocalFactorTree.ofList_denominator, List.map_map,
    pow_one, nodeDenominator]
  rw [← enumerates, List.prod_toFinset _ distinct]
  rfl

theorem nodeCoefficientTree_valid (nodes : Finset K) (node : K)
    (nonzero : node ≠ 0) (order : ℕ) (positive : 0 < order)
    (otherNodes : List K) (enumerates : otherNodes.toFinset = nodes.erase node) :
    (nodeCoefficientTree node order otherNodes).Valid := by
  refine ⟨⟨nonzero, Nat.zero_lt_one⟩, ?_⟩
  apply ReciprocalFactorTree.ofList_valid
  intro factor member
  obtain ⟨other, hother, rfl⟩ := List.mem_map.mp member
  have hmem : other ∈ nodes.erase node := by
    rw [← enumerates]
    exact List.mem_toFinset.mpr hother
  exact ⟨sub_ne_zero.mpr (Finset.mem_erase.mp hmem).1.symm, positive⟩

/-- The concrete arithmetic tree returns exactly the coefficient used in the
Hermite recovery weights. Its inputs are an explicit enumeration of the other
nodes, the node, the order, and the requested coefficient index. The polynomial
inverse is present only in the theorem, not in the coefficient computation. -/
theorem nodeCoefficientTree_correct (nodes : Finset K) (node : K)
    (nonzero : node ≠ 0) (order : ℕ) (positive : 0 < order)
    (otherNodes : List K) (distinct : otherNodes.Nodup)
    (enumerates : otherNodes.toFinset = nodes.erase node)
    (index : ℕ) (below : index < order) :
    (nodeCoefficientTree node order otherNodes).oracle.coefficient index =
      (nodeWeight nodes node order).coeff index := by
  rw [ReciprocalFactorTree.coefficient_correct _
      (nodeCoefficientTree_valid nodes node nonzero order positive otherNodes enumerates),
    nodeCoefficientTree_denominator nodes node order otherNodes distinct enumerates,
    nodeWeight, truncatedInverse, PowerSeries.coeff_trunc, if_pos below]

/-- The finite scalar procedure evaluates the exact truncated weight appearing
in the multi-node Hermite identity. This is a functional-correctness result. -/
theorem nodeWeightEvaluation_correct (nodes : Finset K) (node : K)
    (nonzero : node ≠ 0) (order : ℕ) (positive : 0 < order)
    (otherNodes : List K) (distinct : otherNodes.Nodup)
    (enumerates : otherNodes.toFinset = nodes.erase node) (z : K) :
    nodeWeightEvaluation node order otherNodes z = (nodeWeight nodes node order).eval z := by
  rw [nodeWeightEvaluation, sumLoop_correct, add_zero,
    Polynomial.eval_eq_sum_range' (nodeWeight_degree_lt nodes node order positive)]
  apply Finset.sum_congr rfl
  intro index member
  rw [nodeCoefficientTree_correct nodes node nonzero order positive
    otherNodes distinct enumerates index (Finset.mem_range.mp member)]

end

end NtimeDspace.HermiteRecovery

