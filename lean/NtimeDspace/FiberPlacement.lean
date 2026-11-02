import NtimeDspace.IncidenceDeformation
import NtimeDspace.HashVariance
import Mathlib.Data.Fin.Embedding

/-!
# Finite placement into copies of the label space

Each label fiber is enumerated by Mathlib's finite-type equivalence and its
index is placed in a common bounded copy type. This gives an explicit finite
mathematical construction and an injectivity proof. It does not implement the
paper's small-space rank accessor or assert a cost for computing the indices.
-/

namespace NtimeDspace.FiberPlacement

noncomputable section

open scoped BigOperators

variable {Inc Label : Type*} [Fintype Inc] [DecidableEq Label]

/-- Enumerate each label fiber and embed its index into the available copies. -/
def placementEmbedding (label : Inc → Label) (copies : ℕ)
    (fiber_bound : ∀ value, Fintype.card {inc // label inc = value} ≤ copies) :
    Inc ↪ Fin copies × Label :=
  (Equiv.sigmaFiberEquiv label).symm.toEmbedding |>.trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl Label)
      (fun value => (Fintype.equivFin {inc // label inc = value}).toEmbedding |>.trans
        (Fin.castLEEmb (fiber_bound value)))) |>.trans
    (Equiv.sigmaEquivProd Label (Fin copies)).toEmbedding |>.trans
    (Equiv.prodComm Label (Fin copies)).toEmbedding

theorem placementEmbedding_label (label : Inc → Label) (copies : ℕ)
    (fiber_bound : ∀ value, Fintype.card {inc // label inc = value} ≤ copies) (inc : Inc) :
    (placementEmbedding label copies fiber_bound inc).2 = label inc := rfl

def copyIndex (label : Inc → Label) (copies : ℕ)
    (fiber_bound : ∀ value, Fintype.card {inc // label inc = value} ≤ copies) (inc : Inc) :
    Fin copies :=
  (placementEmbedding label copies fiber_bound inc).1

theorem copyIndex_injective_placement (label : Inc → Label) (copies : ℕ)
    (fiber_bound : ∀ value, Fintype.card {inc // label inc = value} ≤ copies) :
    Function.Injective (fun inc => (copyIndex label copies fiber_bound inc, label inc)) := by
  intro first second same
  apply (placementEmbedding label copies fiber_bound).injective
  exact Prod.ext (congrArg Prod.fst same) (congrArg Prod.snd same)

theorem bucketCount_eq_fiber_card (label : Inc → Label) (value : Label) :
    HashVariance.bucketCount label value = (Fintype.card {inc // label inc = value} : ℚ) := by
  simp [HashVariance.bucketCount, Fintype.card_subtype]

/-- The rational occupancies from the affine variance calculation imply the
finite fiber bound needed for placement. -/
theorem fiber_bound_of_bucketCount (label : Inc → Label) (copies : ℕ)
    (occupancy : ∀ value, HashVariance.bucketCount label value ≤ (copies : ℚ)) :
    ∀ value, Fintype.card {inc // label inc = value} ≤ copies := by
  intro value
  have h := occupancy value
  rw [bucketCount_eq_fiber_card] at h
  exact_mod_cast h

theorem exists_copyIndex_of_occupancy (label : Inc → Label) (copies : ℕ)
    (occupancy : ∀ value, HashVariance.bucketCount label value ≤ (copies : ℚ)) :
    ∃ copy : Inc → Fin copies, Function.Injective (fun inc => (copy inc, label inc)) :=
  ⟨copyIndex label copies (fiber_bound_of_bucketCount label copies occupancy),
    copyIndex_injective_placement label copies (fiber_bound_of_bucketCount label copies occupancy)⟩

end

end NtimeDspace.FiberPlacement
