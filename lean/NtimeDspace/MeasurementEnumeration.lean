import NtimeDspace.GroupedDeformation
import NtimeDspace.CoefficientRecursion
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Scalar radix enumeration of integer measurement tuples

A measurement tuple is accessed through the digits of one natural-number
counter. The callback sees the integer digit minus the measurement bound.
No list of tuples is constructed. The equivalences below use inverse maps
only in proofs; the executable loops use division, remainder, and subtraction.

These are arithmetic-loop correctness and register-range results. Computing
the radix powers, implementing callbacks or row indexing, and compiling the
arithmetic to work tapes are separate obligations.
-/

namespace NtimeDspace.MeasurementEnumeration

open scoped BigOperators
open GroupedDeformation HermiteRecovery

/-- Uniqueness of a bounded natural number from its fixed-width radix digits.
The base may be one, in which case the only admissible counter value is zero. -/
theorem radix_unique (base width : ℕ) (positive : 0 < base) (first second : ℕ)
    (first_bound : first < base ^ width) (second_bound : second < base ^ width)
    (same : ∀ index < width, first / base ^ index % base = second / base ^ index % base) :
    first = second := by
  induction width generalizing first second with
  | zero => simp only [pow_zero] at first_bound second_bound; omega
  | succ width ih =>
    have first_tail : first / base < base ^ width :=
      (Nat.div_lt_iff_lt_mul positive).mpr (by simpa only [pow_succ] using first_bound)
    have second_tail : second / base < base ^ width :=
      (Nat.div_lt_iff_lt_mul positive).mpr (by simpa only [pow_succ] using second_bound)
    have tails : first / base = second / base := by
      apply ih _ _ first_tail second_tail
      intro index within
      simpa only [Nat.div_div_eq_div_mul, ← pow_succ'] using same (index + 1) (by omega)
    have heads : first % base = second % base := by
      simpa only [pow_zero, Nat.div_one] using same 0 (by omega)
    have first_parts := Nat.mod_add_div first base
    have second_parts := Nat.mod_add_div second base
    rw [tails, heads] at first_parts
    exact first_parts.symm.trans second_parts

/-- The row accessor computes a single signed digit on demand. -/
def tuple (bound width mask : ℕ) : Fin width → BoundedValue bound :=
  fun index =>
    ⟨(mask / (2 * bound + 1) ^ index.val % (2 * bound + 1) : ℕ) - (bound : ℤ),
      Finset.mem_Icc.mpr (by
        have digit_bound := Nat.mod_lt (mask / (2 * bound + 1) ^ index.val)
          (show 0 < 2 * bound + 1 by omega)
        constructor <;> omega)⟩

theorem tuple_injective (bound width : ℕ) :
    Function.Injective (fun mask : Fin ((2 * bound + 1) ^ width) => tuple bound width mask.val) := by
  intro first second same
  apply Fin.ext
  apply radix_unique (2 * bound + 1) width (by omega) _ _ first.isLt second.isLt
  intro index within
  have digit_same := congrArg Subtype.val (congrFun same ⟨index, within⟩)
  dsimp only [tuple] at digit_same
  omega

theorem tuple_bijective (bound width : ℕ) :
    Function.Bijective (fun mask : Fin ((2 * bound + 1) ^ width) => tuple bound width mask.val) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨tuple_injective bound width, ?_⟩
  simp only [Fintype.card_fun, Fintype.card_fin]
  congr 1
  simp only [BoundedValue, Fintype.card_coe, Int.card_Icc]
  omega

/-- Only the inverse of this proof-level equivalence uses choice. The forward
map is the explicit scalar radix accessor. -/
noncomputable def tupleEquiv (bound width : ℕ) :
    Fin ((2 * bound + 1) ^ width) ≃ (Fin width → BoundedValue bound) :=
  Equiv.ofBijective _ (tuple_bijective bound width)

/-- Descending counter enumeration with one scalar accumulator and on-demand
access to each candidate tuple. -/
def sumMeasurements {R : Type*} [AddMonoid R] (bound width : ℕ)
    (contribution : (Fin width → BoundedValue bound) → R) (accumulator : R) : R :=
  sumLoop (fun mask => contribution (tuple bound width mask)) ((2 * bound + 1) ^ width) accumulator

/-- Every bounded integer tuple contributes exactly once. This also covers
width zero (one empty tuple) and bound zero (one all-zero tuple). -/
theorem sumMeasurements_correct {R : Type*} [AddCommMonoid R] (bound width : ℕ)
    (contribution : (Fin width → BoundedValue bound) → R) (accumulator : R) :
    sumMeasurements bound width contribution accumulator =
      (∑ measured : Fin width → BoundedValue bound, contribution measured) + accumulator := by
  rw [sumMeasurements, sumLoop_correct]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  exact (tupleEquiv bound width).sum_comp contribution

@[simp] theorem tuple_zero_bound (width mask : ℕ) (index : Fin width) :
    (tuple 0 width mask index).val = 0 := by simp [tuple]

theorem sumMeasurements_zero_width {R : Type*} [AddMonoid R] (bound : ℕ)
    (contribution : (Fin 0 → BoundedValue bound) → R) (accumulator : R) :
    sumMeasurements bound 0 contribution accumulator =
      contribution (tuple bound 0 0) + accumulator := rfl

theorem sumMeasurements_zero_bound {R : Type*} [AddMonoid R] (width : ℕ)
    (contribution : (Fin width → BoundedValue 0) → R) (accumulator : R) :
    sumMeasurements 0 width contribution accumulator =
      contribution (tuple 0 width 0) + accumulator := by
  simp only [sumMeasurements, Nat.mul_zero, Nat.zero_add, one_pow, sumLoop]

section Grouped

variable {Group : Type*} {Row : Group → Type*} {width : ℕ}

/-- Read the requested group/row through a supplied explicit ordinal index.
The forward accessor never computes the inverse of this index. -/
def groupedTuple (rowNumber : (Σ group, Row group) → Fin width) (bound mask : ℕ) :
    MeasurementTuple Row bound :=
  fun group row => tuple bound width mask (rowNumber ⟨group, row⟩)

/-- A bijective row numbering transfers the scalar enumeration to the exact
dependent measurement tuple type used by the grouped algebra. -/
theorem groupedTuple_bijective (rowNumber : (Σ group, Row group) → Fin width)
    (numbering : Function.Bijective rowNumber) (bound : ℕ) :
    Function.Bijective (fun mask : Fin ((2 * bound + 1) ^ width) =>
      groupedTuple rowNumber bound mask.val) := by
  constructor
  · intro first second same
    apply tuple_injective bound width
    funext index
    obtain ⟨⟨group, row⟩, rfl⟩ := numbering.surjective index
    exact congrFun (congrFun same group) row
  · intro measured
    let numberingEquiv := Equiv.ofBijective rowNumber numbering
    let flat : Fin width → BoundedValue bound := fun index =>
      measured (numberingEquiv.symm index).1 (numberingEquiv.symm index).2
    obtain ⟨mask, same⟩ := (tuple_bijective bound width).surjective flat
    refine ⟨mask, ?_⟩
    funext group row
    change tuple bound width mask.val (rowNumber ⟨group, row⟩) = measured group row
    refine (congrFun same (rowNumber ⟨group, row⟩)).trans ?_
    change (fun entry : Σ group, Row group => measured entry.1 entry.2)
      (numberingEquiv.symm (numberingEquiv ⟨group, row⟩)) = _
    rw [numberingEquiv.symm_apply_apply]

noncomputable def groupedTupleEquiv (rowNumber : (Σ group, Row group) → Fin width)
    (numbering : Function.Bijective rowNumber) (bound : ℕ) :
    Fin ((2 * bound + 1) ^ width) ≃ MeasurementTuple Row bound :=
  Equiv.ofBijective _ (groupedTuple_bijective rowNumber numbering bound)

def sumGrouped {R : Type*} [AddMonoid R]
    (rowNumber : (Σ group, Row group) → Fin width) (bound : ℕ)
    (contribution : MeasurementTuple Row bound → R) (accumulator : R) : R :=
  sumLoop (fun mask => contribution (groupedTuple rowNumber bound mask))
    ((2 * bound + 1) ^ width) accumulator

theorem sumGrouped_correct [Fintype Group] [DecidableEq Group]
    [∀ group, Fintype (Row group)] [∀ group, DecidableEq (Row group)]
    {R : Type*} [AddCommMonoid R]
    (rowNumber : (Σ group, Row group) → Fin width)
    (numbering : Function.Bijective rowNumber) (bound : ℕ)
    (contribution : MeasurementTuple Row bound → R) (accumulator : R) :
    sumGrouped rowNumber bound contribution accumulator =
      (∑ measured : MeasurementTuple Row bound, contribution measured) + accumulator := by
  rw [sumGrouped, sumLoop_correct]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  exact (groupedTupleEquiv rowNumber numbering bound).sum_comp contribution

end Grouped

/-- A concrete row-major numbering for the common rectangular group/row
layout: `row + rows * group`. Empty groups and zero rows require no exception. -/
def rectangularIndex (groups rows : ℕ) :
    (Σ _group : Fin groups, Fin rows) → Fin (groups * rows) :=
  fun entry => finProdFinEquiv (entry.1, entry.2)

theorem rectangularIndex_bijective (groups rows : ℕ) :
    Function.Bijective (rectangularIndex groups rows) :=
  ((Equiv.sigmaEquivProd (Fin groups) (Fin rows)).trans finProdFinEquiv).bijective

theorem rectangularIndex_val (groups rows : ℕ) (group : Fin groups) (row : Fin rows) :
    (rectangularIndex groups rows ⟨group, row⟩).val = row.val + rows * group.val := rfl

/-- An explicit scalar loop for rectangular grouped measurement arrays. -/
def sumRectangular {R : Type*} [AddMonoid R] (bound groups rows : ℕ)
    (contribution : MeasurementTuple (fun _ : Fin groups => Fin rows) bound → R)
    (accumulator : R) : R :=
  sumGrouped (rectangularIndex groups rows) bound contribution accumulator

theorem sumRectangular_correct {R : Type*} [AddCommMonoid R] (bound groups rows : ℕ)
    (contribution : MeasurementTuple (fun _ : Fin groups => Fin rows) bound → R)
    (accumulator : R) :
    sumRectangular bound groups rows contribution accumulator =
      (∑ measured : MeasurementTuple (fun _ : Fin groups => Fin rows) bound,
        contribution measured) + accumulator :=
  sumGrouped_correct (rectangularIndex groups rows) (rectangularIndex_bijective groups rows)
    bound contribution accumulator

end NtimeDspace.MeasurementEnumeration
