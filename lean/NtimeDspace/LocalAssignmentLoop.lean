import NtimeDspace.AssignmentLoop
import NtimeDspace.SchedulePlacement

/-!
Local assignment enumeration with explicit variable ranks. Both group size and
a variable's rank are obtained by rescanning declared variable indices with a
scalar counter. The loop retains one binary assignment mask; a requested bit is
looked up by its computed rank. No list of group localVars or assignments is
constructed by these procedures. This is an arithmetic implementation interface,
not yet a tape-machine bound for scans or callbacks.
-/

namespace NtimeDspace.LocalAssignmentLoop

open scoped BigOperators
open GroupedDeformation

variable {n : ℕ} {Group : Type*} [DecidableEq Group]

/-- Scan declared variables, counting matches strictly before `limit`. A full
scan is deliberate: its scalar state does not retain a list of group members. -/
def countBefore (groupOf : Fin n → Group) (group : Group) (limit : ℕ) : ℕ :=
  sumLoop (fun i =>
    if within : i < n then
      if i < limit ∧ groupOf ⟨i, within⟩ = group then 1 else 0
    else 0) n 0

theorem countBefore_eq_card (groupOf : Fin n → Group) (group : Group) (limit : ℕ) :
    countBefore groupOf group limit =
      (Finset.univ.filter (fun v : Fin n => v.val < limit ∧ groupOf v = group)).card := by
  rw [countBefore, sumLoop_correct, Nat.add_zero, ← Fin.sum_univ_eq_sum_range,
    Finset.card_filter]
  apply Finset.sum_congr rfl
  intro v _
  simp only [dite_eq_left v.isLt]

theorem countBefore_le (groupOf : Fin n → Group) (group : Group) (limit : ℕ) :
    countBefore groupOf group limit ≤ n := by
  rw [countBefore_eq_card]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

def groupSize (groupOf : Fin n → Group) (group : Group) : ℕ :=
  countBefore groupOf group n

theorem groupSize_eq_card (groupOf : Fin n → Group) (group : Group) :
    groupSize groupOf group = (CanonicalPlacement.bucket groupOf group).card := by
  rw [groupSize, countBefore_eq_card]
  congr 1
  ext v
  simp [CanonicalPlacement.bucket]

theorem localVariable_card (groupOf : Fin n → Group) (group : Group) :
    Fintype.card (LocalVariable groupOf group) = groupSize groupOf group := by
  rw [groupSize_eq_card]
  simp [LocalVariable, Fintype.card_subtype, CanonicalPlacement.bucket]

theorem countBefore_eq_copyNumber (groupOf : Fin n → Group) (group : Group)
    (localVar : LocalVariable groupOf group) :
    countBefore groupOf group localVar.val.val = CanonicalPlacement.copyNumber groupOf localVar.val := by
  rw [countBefore_eq_card]
  simp only [CanonicalPlacement.copyNumber, CanonicalPlacement.predecessors, localVar.property]
  rfl

/-- The local bit position is the number of preceding variables in this group. -/
def rank (groupOf : Fin n → Group) (group : Group) (localVar : LocalVariable groupOf group) :
    Fin (groupSize groupOf group) :=
  ⟨countBefore groupOf group localVar.val.val, by
    rw [countBefore_eq_copyNumber, groupSize_eq_card]
    simpa only [localVar.property] using
      CanonicalPlacement.copyNumber_lt_bucket groupOf localVar.val⟩

theorem rank_injective (groupOf : Fin n → Group) (group : Group) :
    Function.Injective (rank groupOf group) := by
  intro first second same
  apply Subtype.ext
  apply CanonicalPlacement.placement_injective groupOf
  apply Prod.ext
  · have ranks := congrArg Fin.val same
    change countBefore groupOf group first.val.val = countBefore groupOf group second.val.val at ranks
    simpa only [countBefore_eq_copyNumber] using ranks
  · exact first.property.trans second.property.symm

theorem rank_bijective (groupOf : Fin n → Group) (group : Group) :
    Function.Bijective (rank groupOf group) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨rank_injective groupOf group, by simp [localVariable_card]⟩

noncomputable def rankEquiv (groupOf : Fin n → Group) (group : Group) :
    LocalVariable groupOf group ≃ Fin (groupSize groupOf group) :=
  Equiv.ofBijective _ (rank_bijective groupOf group)

/-- One assignment is read directly from its mask, with ranks recomputed on
demand rather than stored in an index table. -/
def assignment (groupOf : Fin n → Group) (group : Group) (mask : ℕ) :
    LocalAssignment groupOf group :=
  fun localVar => mask.testBit (rank groupOf group localVar).val

noncomputable def assignmentEquiv (groupOf : Fin n → Group) (group : Group) :
    Fin (2 ^ groupSize groupOf group) ≃ LocalAssignment groupOf group :=
  (AssignmentLoop.assignmentEquiv (groupSize groupOf group)).trans
    (Equiv.arrowCongr (rankEquiv groupOf group).symm (Equiv.refl Bool))

theorem assignmentEquiv_apply (groupOf : Fin n → Group) (group : Group)
    (mask : Fin (2 ^ groupSize groupOf group)) :
    assignmentEquiv groupOf group mask = assignment groupOf group mask.val := rfl

def sumAssignments {R : Type*} [AddMonoid R] (groupOf : Fin n → Group) (group : Group)
    (contribution : LocalAssignment groupOf group → R) (accumulator : R) : R :=
  sumLoop (fun mask => contribution (assignment groupOf group mask))
    (2 ^ groupSize groupOf group) accumulator

theorem sumAssignments_correct {R : Type*} [AddCommMonoid R]
    (groupOf : Fin n → Group) (group : Group)
    (contribution : LocalAssignment groupOf group → R) (accumulator : R) :
    sumAssignments groupOf group contribution accumulator =
      (∑ a : LocalAssignment groupOf group, contribution a) + accumulator := by
  rw [sumAssignments, sumLoop_correct]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  exact (assignmentEquiv groupOf group).sum_comp contribution

/-- The balanced schedule bounds the mask width of the actual local loop.
This is a bound on its representation, not on an uncompiled callback. -/
theorem balanced_groupSize {Node : Type*} [Fintype Node] [DecidableEq Node]
    (formula : Formula n) (bits : ℕ) (seed : SchedulePlacement.Seed formula Node bits)
    (balanced : SchedulePlacement.Balanced formula bits seed) (node : Node) (group : Fin (2 ^ bits)) :
    groupSize (SchedulePlacement.variableGroup formula bits seed node) group * 2 ^ bits ≤ 2 * n := by
  have bound := balanced.2 node group
  have size : (groupSize (SchedulePlacement.variableGroup formula bits seed node) group : ℚ) =
      HashVariance.bucketCount (SchedulePlacement.variableGroup formula bits seed node) group := by
    rw [groupSize_eq_card]
    simp only [CanonicalPlacement.bucket, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, HashVariance.bucketCount]
  rw [← size] at bound
  have positive : (0 : ℚ) < 2 ^ bits := by positivity
  have multiplied := (le_div_iff₀ positive).mp bound
  exact_mod_cast multiplied

end NtimeDspace.LocalAssignmentLoop
