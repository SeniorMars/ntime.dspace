import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
An explicit copy number for a labeled incidence is its rank among earlier
incidences with the same label. This implements the manuscript's bucket
placement as a finite formula and proves that no two incidences occupy the
same copy and label. Computing this rank by a machine is a separate obligation.
-/

namespace NtimeDspace.CanonicalPlacement

variable {M : ℕ} {Label : Type*} [DecidableEq Label]

def bucket (label : Fin M → Label) (value : Label) : Finset (Fin M) :=
  Finset.univ.filter (fun e => label e = value)

def predecessors (label : Fin M → Label) (e : Fin M) : Finset (Fin M) :=
  Finset.univ.filter (fun earlier => earlier < e ∧ label earlier = label e)

def copyNumber (label : Fin M → Label) (e : Fin M) : ℕ :=
  (predecessors label e).card

theorem predecessors_subset (label : Fin M → Label) (e : Fin M) :
    predecessors label e ⊆ bucket label (label e) := by
  intro earlier h
  simp only [predecessors, bucket, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  exact h.2

theorem copyNumber_lt_bucket (label : Fin M → Label) (e : Fin M) :
    copyNumber label e < (bucket label (label e)).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨predecessors_subset label e, ?_⟩
  intro same
  have member : e ∈ bucket label (label e) := by simp [bucket]
  rw [← same] at member
  simp [predecessors] at member

theorem copyNumber_strict (label : Fin M → Label) (e f : Fin M)
    (earlier : e < f) (same_label : label e = label f) :
    copyNumber label e < copyNumber label f := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro i hi
    simp only [predecessors, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1.trans earlier, hi.2.trans same_label⟩
  · intro same
    have member : e ∈ predecessors label f := by simp [predecessors, earlier, same_label]
    rw [← same] at member
    simp [predecessors] at member

/-- Equal copy numbers and equal labels determine the original incidence. -/
theorem placement_injective (label : Fin M → Label) :
    Function.Injective (fun e => (copyNumber label e, label e)) := by
  intro e f equal
  have ranks : copyNumber label e = copyNumber label f := congrArg Prod.fst equal
  have labels : label e = label f := congrArg Prod.snd equal
  rcases lt_trichotomy e f with before | same | after
  · have := copyNumber_strict label e f before labels
    omega
  · exact same
  · have := copyNumber_strict label f e after labels.symm
    omega

/-- A bucket-capacity bound bounds every explicit copy index. -/
def copyIndex (label : Fin M → Label) (capacity : ℕ)
    (bounded : ∀ value, (bucket label value).card ≤ capacity) (e : Fin M) : Fin capacity :=
  ⟨copyNumber label e, (copyNumber_lt_bucket label e).trans_le (bounded (label e))⟩

theorem bounded_placement_injective (label : Fin M → Label) (capacity : ℕ)
    (bounded : ∀ value, (bucket label value).card ≤ capacity) :
    Function.Injective (fun e => (copyIndex label capacity bounded e, label e)) := by
  intro e f equal
  apply placement_injective label
  have ranks := congrArg (fun pair => (pair.1.val, pair.2)) equal
  exact ranks

end NtimeDspace.CanonicalPlacement
