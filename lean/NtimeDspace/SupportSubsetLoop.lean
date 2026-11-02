import NtimeDspace.AssignmentLoop
import NtimeDspace.SparseCorrection

/-!
# Exact-width support-subset masks

The executing routines take a width and a bit accessor. They neither decode a
support nor construct a subset. A duplicate-free support list is used only to
prove that width-many mask bits represent its subsets exactly once. In
particular the parser capacity never supplies extra mask bits.

The scalar population count gives the sign in the Boolean finite-difference
sum. Streaming compressed-code lookup returns precisely the represented
subset's membership bit. These are arithmetic-loop correctness statements;
machine compilation and work-tape bounds remain separate.
-/

namespace NtimeDspace.SupportSubsetLoop

open scoped BigOperators
open SparseCorrection

variable {n : ℕ}

/-- Each actual support entry has its own mask bit. -/
theorem assignmentBit_get (support : List (Fin n)) (distinct : support.Nodup)
    (mask : Assignment support.length) (index : Fin support.length) :
    SupportAssignment.assignmentBit support (Nat.le_refl _) mask (support.get index) =
      mask index := by
  unfold SupportAssignment.assignmentBit
  rw [dite_eq_left (List.get_mem support index)]
  apply congrArg mask
  apply Fin.ext
  exact List.get_idxOf distinct index

/-- Proof-side mask of an arbitrary subset; the executing loop uses binary
counter bits and does not call this inverse. -/
def subsetMask (support : List (Fin n)) (subset : Finset (Fin n)) :
    Assignment support.length := fun index => decide (support.get index ∈ subset)

theorem subsetMask_membership (support : List (Fin n)) (subset : Finset (Fin n))
    (included : subset ⊆ support.toFinset) (v : Fin n) :
    SupportAssignment.assignmentBit support (Nat.le_refl _) (subsetMask support subset) v =
      decide (v ∈ subset) := by
  by_cases member : v ∈ support
  · simp only [SupportAssignment.assignmentBit, dite_eq_left member, subsetMask,
      List.idxOf_get]
  · have absent : v ∉ subset := fun present => member (List.mem_toFinset.mp (included present))
    simp only [SupportAssignment.assignmentBit, dite_eq_right member, absent, decide_false]

/-- Exact, duplicate-free correspondence with all subsets of the support. -/
def maskEquiv (support : List (Fin n)) (distinct : support.Nodup) :
    Assignment support.length ≃ {subset : Finset (Fin n) // subset ⊆ support.toFinset} where
  toFun mask := ⟨maskSubset support (Nat.le_refl _) mask,
    maskSubset_subset support (Nat.le_refl _) mask⟩
  invFun subset := subsetMask support subset.val
  left_inv mask := by
    funext index
    change decide (support.get index ∈ maskSubset support (Nat.le_refl _) mask) = mask index
    rw [← maskSubset_membership, assignmentBit_get support distinct]
  right_inv subset := by
    apply Subtype.ext
    ext v
    simp only [maskSubset, Finset.mem_filter, Finset.mem_univ, true_and,
      subsetMask_membership support subset.val subset.property, decide_eq_true_eq]

/-- Scalar scan of the actual mask width. Only an index and an accumulator are
needed; no selected-index collection is built. -/
def countOnes (width : ℕ) (mask : Assignment width) : ℕ :=
  GroupedAssignmentEvaluation.scanSum (fun index => if mask index then 1 else 0) 0

theorem countOnes_eq_sum (width : ℕ) (mask : Assignment width) :
    countOnes width mask = ∑ index, if mask index then 1 else 0 := by
  simp only [countOnes, GroupedAssignmentEvaluation.scanSum_correct, add_zero]

theorem countOnes_le (width : ℕ) (mask : Assignment width) : countOnes width mask ≤ width := by
  rw [countOnes_eq_sum]
  calc
    (∑ index : Fin width, if mask index then 1 else 0) ≤ ∑ _index : Fin width, 1 := by
      apply Finset.sum_le_sum
      intro index _
      split <;> omega
    _ = width := by simp

theorem selected_indices_image (support : List (Fin n)) (distinct : support.Nodup)
    (mask : Assignment support.length) :
    (Finset.univ.filter (fun index => mask index = true)).image support.get =
      maskSubset support (Nat.le_refl _) mask := by
  ext v
  constructor
  · intro member
    obtain ⟨index, selected, rfl⟩ := Finset.mem_image.mp member
    apply of_decide_eq_true
    rw [← maskSubset_membership support (Nat.le_refl _) mask (support.get index),
      assignmentBit_get support distinct mask index]
    exact (Finset.mem_filter.mp selected).2
  · intro member
    have present : v ∈ support := List.mem_toFinset.mp
      (maskSubset_subset support (Nat.le_refl _) mask member)
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp present
    apply Finset.mem_image.mpr
    refine ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [← assignmentBit_get support distinct mask index,
      maskSubset_membership support (Nat.le_refl _) mask (support.get index)]
    exact decide_eq_true member

theorem countOnes_eq_card (support : List (Fin n)) (distinct : support.Nodup)
    (mask : Assignment support.length) :
    countOnes support.length mask = (maskSubset support (Nat.le_refl _) mask).card := by
  rw [← selected_indices_image support distinct, Finset.card_image_of_injective]
  · rw [countOnes_eq_sum]
    simp
  · intro first second same
    exact distinct.get_inj_iff.mp same

/-- The arithmetic exponent is exactly the finite-difference exponent. -/
theorem sign_correct {R : Type*} [Ring R] (support : List (Fin n))
    (distinct : support.Nodup) (mask : Assignment support.length) :
    (-1 : R) ^ (support.length - countOnes support.length mask) =
      (-1 : R) ^ (support.toFinset.card - (maskSubset support (Nat.le_refl _) mask).card) := by
  rw [countOnes_eq_card support distinct, List.toFinset_card_of_nodup distinct]

/-- The existing scalar binary-mask loop enumerates each support subset once.
The callback takes only a bit accessor; the subset is a proof-side value. -/
theorem sumAssignments_subsets {R : Type*} [AddCommMonoid R]
    (support : List (Fin n)) (distinct : support.Nodup)
    (callback : Assignment support.length → R) (weight : Finset (Fin n) → R)
    (accumulator : R)
    (agrees : ∀ mask, callback mask = weight (maskSubset support (Nat.le_refl _) mask)) :
    AssignmentLoop.sumAssignments support.length callback accumulator =
      (∑ subset ∈ support.toFinset.powerset, weight subset) + accumulator := by
  rw [AssignmentLoop.sumAssignments_correct]
  apply congrArg (· + accumulator)
  apply Finset.sum_bij (fun mask _ => maskSubset support (Nat.le_refl _) mask)
  · intro mask _
    exact Finset.mem_powerset.mpr (maskSubset_subset support (Nat.le_refl _) mask)
  · intro first _ second _ same
    apply (maskEquiv support distinct).injective
    exact Subtype.ext same
  · intro subset member
    let target : {subset : Finset (Fin n) // subset ⊆ support.toFinset} :=
      ⟨subset, Finset.mem_powerset.mp member⟩
    exact ⟨(maskEquiv support distinct).symm target, Finset.mem_univ _,
      congrArg Subtype.val ((maskEquiv support distinct).apply_symm_apply target)⟩
  · intro mask _
    exact agrees mask

/-- Executing signed subset loop, using the scalar population count rather
than constructing the selected subset to determine its sign. -/
def sumSignedSubsets {R : Type*} [Ring R] (width : ℕ)
    (callback : Assignment width → R) (accumulator : R) : R :=
  AssignmentLoop.sumAssignments width
    (fun mask => (-1 : R) ^ (width - countOnes width mask) * callback mask) accumulator

theorem sumSignedSubsets_correct {R : Type*} [Ring R]
    (support : List (Fin n)) (distinct : support.Nodup)
    (callback : Assignment support.length → R) (weight : Finset (Fin n) → R)
    (accumulator : R)
    (agrees : ∀ mask, callback mask = weight (maskSubset support (Nat.le_refl _) mask)) :
    sumSignedSubsets support.length callback accumulator =
      (∑ subset ∈ support.toFinset.powerset,
        (-1 : R) ^ (support.toFinset.card - subset.card) * weight subset) + accumulator := by
  apply sumAssignments_subsets support distinct
    (fun mask => (-1 : R) ^ (support.length - countOnes support.length mask) * callback mask)
    (fun subset => (-1 : R) ^ (support.toFinset.card - subset.card) * weight subset) accumulator
  intro mask
  rw [sign_correct support distinct mask, agrees mask]

/-- Streaming support lookup is the membership oracle for exactly the subset
enumerated above, even when parser capacity exceeds actual mask width. -/
theorem compressed_lookup_membership {capacity : ℕ} (support : List (Fin n))
    (valid : SupportAssignment.Valid capacity support) (mask : Assignment support.length)
    (v : Fin n) :
    SupportAssignment.lookupBit (SupportAssignment.extendMask valid.2 mask) v
      (SupportAssignment.encode support) =
      some (decide (v ∈ maskSubset support (Nat.le_refl _) mask)) := by
  rw [SupportAssignment.lookupBit_exactMask support valid mask v,
    maskSubset_membership support (Nat.le_refl _) mask v]

theorem compressed_lookup_getD {capacity : ℕ} (support : List (Fin n))
    (valid : SupportAssignment.Valid capacity support) (mask : Assignment support.length)
    (v : Fin n) :
    (SupportAssignment.lookupBit (SupportAssignment.extendMask valid.2 mask) v
      (SupportAssignment.encode support)).getD false =
      decide (v ∈ maskSubset support (Nat.le_refl _) mask) := by
  rw [compressed_lookup_membership support valid mask v, Option.getD_some]

end NtimeDspace.SupportSubsetLoop
