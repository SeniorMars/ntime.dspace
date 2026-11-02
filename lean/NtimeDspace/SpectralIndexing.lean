import NtimeDspace.MeasurementEnumeration
import NtimeDspace.LocalAssignmentLoop
import NtimeDspace.ConcreteGroupedDeformation
import Mathlib.Data.Nat.Find

/-!
# Scalar access to the concrete spectral labels and bad rows

Labels are read as base-`r*r` digits. Counting antisymmetric coordinates and
ranking bad labels use repeated scalar scans, with finite sets appearing only
in specifications and proofs. The bad predicate is the complement of the exact
half-open integer window used by the finite-field deformation.

The arithmetic routines below do not establish machine time or work-tape
bounds. They avoid storing the full label space or a filtered list of bad rows.
-/

namespace NtimeDspace.SpectralIndexing

open scoped BigOperators
open HermiteRecovery FiniteFieldDeformation GroupedDeformation

variable (r Q : ℕ) (positive : 0 < r)

/-- Read one ordered-pair coordinate from a base-`r*r` counter. -/
def label (mask : ℕ) : Label (Fin Q) r :=
  fun node => finProdFinEquiv.symm
    ⟨mask / (r * r) ^ node.val % (r * r), Nat.mod_lt _ (Nat.mul_pos positive positive)⟩

theorem label_injective :
    Function.Injective (fun mask : Fin ((r * r) ^ Q) => label r Q positive mask.val) := by
  intro first second same
  apply Fin.ext
  apply MeasurementEnumeration.radix_unique (r * r) Q (Nat.mul_pos positive positive)
    _ _ first.isLt second.isLt
  intro node within
  have digit_same := congrArg (fun pair => (finProdFinEquiv pair).val)
    (congrFun same ⟨node, within⟩)
  simpa only [label, Equiv.apply_symm_apply] using digit_same

theorem label_bijective :
    Function.Bijective (fun mask : Fin ((r * r) ^ Q) => label r Q positive mask.val) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨label_injective r Q positive, by simp only [Label, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_prod]⟩

/-- The inverse is proof-only; label access uses the displayed radix formula. -/
noncomputable def labelEquiv : Fin ((r * r) ^ Q) ≃ Label (Fin Q) r :=
  Equiv.ofBijective _ (label_bijective r Q positive)

/-- Count precisely the coordinates whose second component is smaller than
the first, matching the tensor basis's antisymmetric orientation. -/
def antisymmetricCount (mask : ℕ) : ℕ :=
  sumLoop (fun node =>
    if within : node < Q then
      if (label r Q positive mask ⟨node, within⟩).2 <
          (label r Q positive mask ⟨node, within⟩).1 then 1 else 0
    else 0) Q 0

theorem antisymmetricCount_correct (mask : ℕ) :
    antisymmetricCount r Q positive mask =
      TensorBasisField.antisymmetricCount (label r Q positive mask) := by
  rw [antisymmetricCount, sumLoop_correct, Nat.add_zero, ← Fin.sum_univ_eq_sum_range]
  simp only [TensorBasisField.antisymmetricCount, TensorBasisField.antisymmetricCoordinates,
    Finset.card_filter]
  apply Finset.sum_congr rfl
  intro node _
  simp only [dite_eq_left node.isLt]

theorem antisymmetricCount_le (mask : ℕ) : antisymmetricCount r Q positive mask ≤ Q := by
  rw [antisymmetricCount_correct, TensorBasisField.antisymmetricCount,
    TensorBasisField.antisymmetricCoordinates]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

/-- Complement of `[start,start+width)`, with signed endpoints. -/
def isBad (start : ℤ) (width mask : ℕ) : Bool :=
  decide (¬(start ≤ (antisymmetricCount r Q positive mask : ℤ) ∧
    (antisymmetricCount r Q positive mask : ℤ) < start + width))

theorem isBad_correct (start : ℤ) (width mask : ℕ) :
    isBad r Q positive start width mask = true ↔
      label r Q positive mask ∈ bad (Node := Fin Q) start width := by
  simp only [isBad, decide_eq_true_eq, antisymmetricCount_correct, bad,
    ParityInterpolation.badIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    ParityInterpolation.mem_integerWindow]

/-- The bad predicate restricted to the finite label-counter range. -/
def classification (start : ℤ) (width : ℕ) : Fin ((r * r) ^ Q) → Bool :=
  fun mask => isBad r Q positive start width mask.val

/-- A full scan of label counters, retaining only a scalar number of earlier
bad labels. `limit` does not alter the scan's finite domain. -/
def countBefore (start : ℤ) (width limit : ℕ) : ℕ :=
  LocalAssignmentLoop.countBefore (classification r Q positive start width) true limit

def badCount (start : ℤ) (width : ℕ) : ℕ :=
  countBefore r Q positive start width ((r * r) ^ Q)

abbrev BadMask (start : ℤ) (width : ℕ) :=
  {mask : Fin ((r * r) ^ Q) // classification r Q positive start width mask = true}

abbrev BadLabel (start : ℤ) (width : ℕ) :=
  {index : Label (Fin Q) r // index ∈ bad (Node := Fin Q) start width}

/-- A scanned bad counter denotes an actual bad tensor-basis label. -/
def badLabel (start : ℤ) (width : ℕ) (mask : BadMask r Q positive start width) :
    BadLabel r Q start width :=
  ⟨label r Q positive mask.val.val,
    (isBad_correct r Q positive start width mask.val.val).mp mask.property⟩

theorem badLabel_bijective (start : ℤ) (width : ℕ) :
    Function.Bijective (badLabel r Q positive start width) := by
  constructor
  · intro first second same
    apply Subtype.ext
    apply label_injective r Q positive
    exact congrArg Subtype.val same
  · intro index
    obtain ⟨mask, same⟩ := (label_bijective r Q positive).surjective index.val
    change label r Q positive mask.val = index.val at same
    have accepted : classification r Q positive start width mask = true :=
      (isBad_correct r Q positive start width mask.val).mpr (by rw [same]; exact index.property)
    refine ⟨⟨mask, accepted⟩, ?_⟩
    exact Subtype.ext same

/-- The scalar scan counts exactly the bad rows used by the algebra. -/
theorem badCount_correct (start : ℤ) (width : ℕ) :
    badCount r Q positive start width = (bad (Node := Fin Q) (r := r) start width).card := by
  have count := LocalAssignmentLoop.localVariable_card
    (classification r Q positive start width) true
  have cardinal := Fintype.card_congr
    (Equiv.ofBijective _ (badLabel_bijective r Q positive start width))
  change Fintype.card (BadMask r Q positive start width) = badCount r Q positive start width at count
  rw [← count, cardinal]
  exact Fintype.card_coe _

/-- Rank by rescanning the scalar labels, not by storing the filtered set. -/
def badRank (start : ℤ) (width : ℕ) (mask : BadMask r Q positive start width) :
    Fin (badCount r Q positive start width) :=
  LocalAssignmentLoop.rank (classification r Q positive start width) true mask

theorem badRank_bijective (start : ℤ) (width : ℕ) :
    Function.Bijective (badRank r Q positive start width) :=
  LocalAssignmentLoop.rank_bijective (classification r Q positive start width) true

theorem badRank_val (start : ℤ) (width : ℕ) (mask : BadMask r Q positive start width) :
    (badRank r Q positive start width mask).val =
      countBefore r Q positive start width mask.val.val := rfl

/-- A proof identity for reconstructing a counter from a fixed number of
digits. The displayed sum is not used to materialize a list of digits. -/
theorem radix_sum (base width mask : ℕ) :
    (∑ node ∈ Finset.range width, mask / base ^ node % base * base ^ node) =
      mask % base ^ width := by
  induction width with
  | zero => simp [Nat.mod_one]
  | succ width ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have decompose := Nat.mod_add_div (mask % (base ^ width * base)) (base ^ width)
    rw [Nat.mod_mod_of_dvd mask (Nat.dvd_mul_right _ _), Nat.mod_mul_right_div_self] at decompose
    simpa only [Nat.mul_comm] using decompose

/-- The reverse label index is also an explicit scalar scan, not a chosen
inverse of the label equivalence. -/
def code (index : Label (Fin Q) r) : ℕ :=
  sumLoop (fun node =>
    if within : node < Q then
      (finProdFinEquiv (index ⟨node, within⟩)).val * (r * r) ^ node
    else 0) Q 0

theorem code_label (mask : Fin ((r * r) ^ Q)) :
    code r Q (label r Q positive mask.val) = mask.val := by
  rw [code, sumLoop_correct, Nat.add_zero]
  have terms : (∑ node ∈ Finset.range Q,
      if within : node < Q then
        (finProdFinEquiv (label r Q positive mask.val ⟨node, within⟩)).val * (r * r) ^ node
      else 0) =
      ∑ node ∈ Finset.range Q, mask.val / (r * r) ^ node % (r * r) * (r * r) ^ node := by
    apply Finset.sum_congr rfl
    intro node member
    simp only [dite_eq_left (Finset.mem_range.mp member), label, Equiv.apply_symm_apply]
  rw [terms, radix_sum, Nat.mod_eq_of_lt mask.isLt]

include positive in
theorem code_lt (index : Label (Fin Q) r) : code r Q index < (r * r) ^ Q := by
  obtain ⟨mask, same⟩ := (label_bijective r Q positive).surjective index
  change label r Q positive mask.val = index at same
  rw [← same, code_label]
  exact mask.isLt

theorem label_code (index : Label (Fin Q) r) :
    label r Q positive (code r Q index) = index := by
  obtain ⟨mask, same⟩ := (label_bijective r Q positive).surjective index
  change label r Q positive mask.val = index at same
  rw [← same, code_label]

/-- Recover the bounded counter for a bad label by evaluating its digit code. -/
def maskOfBad (start : ℤ) (width : ℕ) (index : BadLabel r Q start width) :
    BadMask r Q positive start width :=
  ⟨⟨code r Q index.val, code_lt r Q positive index.val⟩,
    (isBad_correct r Q positive start width _).mpr (by
      rw [label_code]; exact index.property)⟩

theorem badLabel_maskOfBad (start : ℤ) (width : ℕ) (index : BadLabel r Q start width) :
    badLabel r Q positive start width (maskOfBad r Q positive start width index) = index :=
  Subtype.ext (label_code r Q positive index.val)

theorem maskOfBad_badLabel (start : ℤ) (width : ℕ) (mask : BadMask r Q positive start width) :
    maskOfBad r Q positive start width (badLabel r Q positive start width mask) = mask :=
  Subtype.ext (Fin.ext (code_label r Q positive mask.val))

/-- The rank of an actual bad tensor label, computed entirely by scalar scans. -/
def indexRank (start : ℤ) (width : ℕ) (index : BadLabel r Q start width) :
    Fin (badCount r Q positive start width) :=
  badRank r Q positive start width (maskOfBad r Q positive start width index)

theorem indexRank_bijective (start : ℤ) (width : ℕ) :
    Function.Bijective (indexRank r Q positive start width) := by
  apply (badRank_bijective r Q positive start width).comp
  constructor
  · intro first second same
    have mapped := congrArg (badLabel r Q positive start width) same
    simpa only [badLabel_maskOfBad] using mapped
  · intro mask
    exact ⟨badLabel r Q positive start width mask, maskOfBad_badLabel r Q positive start width mask⟩

/-- A bounded descending search for the counter with the requested bad rank.
Its predicate recomputes the rank by scalar scans. No inverse obtained by
choice is evaluated by this definition. -/
def selectedMask (start : ℤ) (width ordinal : ℕ) : ℕ :=
  Nat.findGreatest (fun mask => mask < (r * r) ^ Q ∧
    isBad r Q positive start width mask = true ∧
    countBefore r Q positive start width mask = ordinal) ((r * r) ^ Q - 1)

theorem selectedMask_spec (start : ℤ) (width : ℕ)
    (ordinal : Fin (badCount r Q positive start width)) :
    selectedMask r Q positive start width ordinal.val < (r * r) ^ Q ∧
      isBad r Q positive start width (selectedMask r Q positive start width ordinal.val) = true ∧
      countBefore r Q positive start width (selectedMask r Q positive start width ordinal.val) =
        ordinal.val := by
  obtain ⟨mask, same⟩ := (badRank_bijective r Q positive start width).surjective ordinal
  have rank_same := congrArg Fin.val same
  change countBefore r Q positive start width mask.val.val = ordinal.val at rank_same
  unfold selectedMask
  exact Nat.findGreatest_spec
    (P := fun candidate => candidate < (r * r) ^ Q ∧
      isBad r Q positive start width candidate = true ∧
      countBefore r Q positive start width candidate = ordinal.val)
    (m := mask.val.val) (n := (r * r) ^ Q - 1) (by have := mask.val.isLt; omega)
    ⟨mask.val.isLt, mask.property, rank_same⟩

def badMaskAt (start : ℤ) (width : ℕ)
    (ordinal : Fin (badCount r Q positive start width)) : BadMask r Q positive start width :=
  ⟨⟨selectedMask r Q positive start width ordinal.val,
    (selectedMask_spec r Q positive start width ordinal).1⟩,
    (selectedMask_spec r Q positive start width ordinal).2.1⟩

theorem badRank_badMaskAt (start : ℤ) (width : ℕ)
    (ordinal : Fin (badCount r Q positive start width)) :
    badRank r Q positive start width (badMaskAt r Q positive start width ordinal) = ordinal :=
  Fin.ext (selectedMask_spec r Q positive start width ordinal).2.2

/-- Access an actual bad spectral label by its finite ordinal. -/
def badAt (start : ℤ) (width : ℕ)
    (ordinal : Fin (badCount r Q positive start width)) : BadLabel r Q start width :=
  badLabel r Q positive start width (badMaskAt r Q positive start width ordinal)

theorem indexRank_badAt (start : ℤ) (width : ℕ)
    (ordinal : Fin (badCount r Q positive start width)) :
    indexRank r Q positive start width (badAt r Q positive start width ordinal) = ordinal := by
  rw [indexRank, badAt, maskOfBad_badLabel, badRank_badMaskAt]

theorem badAt_indexRank (start : ℤ) (width : ℕ) (index : BadLabel r Q start width) :
    badAt r Q positive start width (indexRank r Q positive start width index) = index := by
  apply (indexRank_bijective r Q positive start width).injective
  exact indexRank_badAt r Q positive start width _

/-- Both directions are now explicit arithmetic procedures. This equivalence
has no noncomputable inverse or materialized bad-label table. -/
def badAtEquiv (start : ℤ) (width : ℕ) :
    Fin (badCount r Q positive start width) ≃ BadLabel r Q start width where
  toFun := badAt r Q positive start width
  invFun := indexRank r Q positive start width
  left_inv := indexRank_badAt r Q positive start width
  right_inv := badAt_indexRank r Q positive start width

/-- The actual row type from `ConcreteGroupedDeformation`, with finite copies. -/
abbrev Row (copies : ℕ) (start : ℤ) (width : ℕ) :=
  ConcreteGroupedDeformation.Row (Fin Q) (Fin copies) r start width

/-- Copy-major scalar numbering of the actual bad-basis rows. -/
def rowNumber (copies : ℕ) (start : ℤ) (width : ℕ)
    (row : Row r Q copies start width) : Fin (copies * badCount r Q positive start width) :=
  finProdFinEquiv (row.1, indexRank r Q positive start width row.2)

def rowAt (copies : ℕ) (start : ℤ) (width : ℕ)
    (ordinal : Fin (copies * badCount r Q positive start width)) : Row r Q copies start width :=
  let pair : Fin copies × Fin (badCount r Q positive start width) := finProdFinEquiv.symm ordinal
  (pair.1, badAt r Q positive start width pair.2)

def rowEquiv (copies : ℕ) (start : ℤ) (width : ℕ) :
    Row r Q copies start width ≃ Fin (copies * badCount r Q positive start width) :=
  (Equiv.prodCongr (Equiv.refl (Fin copies)) (badAtEquiv r Q positive start width).symm).trans
    finProdFinEquiv

theorem rowEquiv_apply (copies : ℕ) (start : ℤ) (width : ℕ) (row : Row r Q copies start width) :
    rowEquiv r Q positive copies start width row = rowNumber r Q positive copies start width row := rfl

theorem rowEquiv_symm_apply (copies : ℕ) (start : ℤ) (width : ℕ)
    (ordinal : Fin (copies * badCount r Q positive start width)) :
    (rowEquiv r Q positive copies start width).symm ordinal =
      rowAt r Q positive copies start width ordinal := rfl

theorem rowNumber_bijective (copies : ℕ) (start : ℤ) (width : ℕ) :
    Function.Bijective (rowNumber r Q positive copies start width) :=
  (rowEquiv r Q positive copies start width).bijective

/-- Flatten the actual group/copy/bad-label coordinates for the measurement
counter. Only the requested label is accessed and ranked. -/
def measurementRowNumber (copies : ℕ) (start : ℤ) (width : ℕ)
    (entry : Σ _group : Fin r, Row r Q copies start width) :
    Fin (r * (copies * badCount r Q positive start width)) :=
  finProdFinEquiv (entry.1, rowNumber r Q positive copies start width entry.2)

theorem measurementRowNumber_bijective (copies : ℕ) (start : ℤ) (width : ℕ) :
    Function.Bijective (measurementRowNumber r Q positive copies start width) :=
  (((Equiv.sigmaEquivProd (Fin r) (Row r Q copies start width)).trans
    (Equiv.prodCongr (Equiv.refl (Fin r)) (rowEquiv r Q positive copies start width))).trans
      finProdFinEquiv).bijective

/-- The scalar count registers remain within the full label-space size. -/
theorem countBefore_le (start : ℤ) (width limit : ℕ) :
    countBefore r Q positive start width limit ≤ (r * r) ^ Q :=
  LocalAssignmentLoop.countBefore_le (classification r Q positive start width) true limit

theorem selectedMask_le (start : ℤ) (width ordinal : ℕ) :
    selectedMask r Q positive start width ordinal ≤ (r * r) ^ Q - 1 :=
  Nat.findGreatest_le _

/-- The radix label count equals the dimension used by the paper's tensor
construction. -/
theorem label_space_size : (r * r) ^ Q = r ^ (2 * Q) := by
  rw [← pow_two, ← pow_mul]

/-- Scalar enumeration for the concrete measurement rows, using the explicit
group/copy/bad-label numbering rather than a finite-type chosen enumeration. -/
def sumConcreteMeasurements {R : Type*} [AddMonoid R]
    (copies : ℕ) (start : ℤ) (width bound : ℕ)
    (contribution : MeasurementTuple (fun _ : Fin r => Row r Q copies start width) bound → R)
    (accumulator : R) : R :=
  MeasurementEnumeration.sumGrouped (measurementRowNumber r Q positive copies start width)
    bound contribution accumulator

theorem sumConcreteMeasurements_correct {R : Type*} [AddCommMonoid R]
    (copies : ℕ) (start : ℤ) (width bound : ℕ)
    (contribution : MeasurementTuple (fun _ : Fin r => Row r Q copies start width) bound → R)
    (accumulator : R) :
    sumConcreteMeasurements r Q positive copies start width bound contribution accumulator =
      (∑ measured : MeasurementTuple (fun _ : Fin r => Row r Q copies start width) bound,
        contribution measured) + accumulator :=
  MeasurementEnumeration.sumGrouped_correct (measurementRowNumber r Q positive copies start width)
    (measurementRowNumber_bijective r Q positive copies start width) bound contribution accumulator

end NtimeDspace.SpectralIndexing
