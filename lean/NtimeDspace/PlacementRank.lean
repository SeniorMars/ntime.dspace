import NtimeDspace.PlacementTerm

/-!
# Copies as ranks in label buckets

The copy of an incidence is the number of incidences before it (in the order
of constraint, then scope position) with the same label. With the label, it
determines the incidence (`rank_label_injective`), and it is below the size of
the label's bucket (`rankN_lt_bucket`).
-/

namespace NtimeDspace.Placement

open WeightedSystem

variable {n : ℕ} (formula : System n)

/-- Lexicographic order on incidences, as numbers. -/
def lexLt (a b : Incidence formula) : Prop :=
  (a.1 : ℕ) < b.1 ∨ ((a.1 : ℕ) = b.1 ∧ (a.2 : ℕ) < b.2)

instance (a b : Incidence formula) : Decidable (lexLt formula a b) := by
  unfold lexLt; infer_instance

theorem lexLt_irrefl (a : Incidence formula) : ¬ lexLt formula a a := by
  unfold lexLt; omega

theorem lexLt_trans {a b c : Incidence formula} (h1 : lexLt formula a b) (h2 : lexLt formula b c) :
    lexLt formula a c := by
  unfold lexLt at *; omega

theorem incidence_ext {a b : Incidence formula} (h1 : (a.1 : ℕ) = b.1) (h2 : (a.2 : ℕ) = b.2) :
    a = b := by
  obtain ⟨e, i⟩ := a
  obtain ⟨e', i'⟩ := b
  simp only at h1 h2
  have he : e = e' := Fin.ext h1
  subst he
  have hi : i = i' := Fin.ext h2
  subst hi
  rfl

theorem lexLt_total {a b : Incidence formula} (h : a ≠ b) : lexLt formula a b ∨ lexLt formula b a := by
  unfold lexLt
  by_contra hc
  push_neg at hc
  apply h
  exact incidence_ext formula (by omega) (by omega)

variable (L : Incidence formula → ℕ)

/-- The rank of an incidence among earlier incidences with the same label. -/
def rankN (a : Incidence formula) : ℕ :=
  ∑ b : Incidence formula, if lexLt formula b a ∧ L b = L a then 1 else 0

theorem rankN_lt_of_lexLt {a b : Incidence formula} (hlt : lexLt formula a b) (hL : L a = L b) :
    rankN formula L a < rankN formula L b := by
  unfold rankN
  apply Finset.sum_lt_sum
  · intro c _
    by_cases h : lexLt formula c a ∧ L c = L a
    · rw [if_pos h, if_pos ⟨lexLt_trans formula h.1 hlt, h.2.trans hL⟩]
    · rw [if_neg h]; exact Nat.zero_le _
  · refine ⟨a, Finset.mem_univ _, ?_⟩
    rw [if_neg (fun h => lexLt_irrefl formula a h.1), if_pos ⟨hlt, hL⟩]
    exact Nat.zero_lt_one

/-- **Rank and label determine the incidence.** -/
theorem rank_label_injective :
    Function.Injective (fun a : Incidence formula => (rankN formula L a, L a)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  by_contra hne
  rcases lexLt_total formula hne with hl | hl
  · exact absurd h.1 (rankN_lt_of_lexLt formula L hl h.2).ne
  · exact absurd h.1.symm (rankN_lt_of_lexLt formula L hl h.2.symm).ne

/-- The rank is below the size of the label's bucket. -/
theorem rankN_lt_bucket (a : Incidence formula) :
    rankN formula L a < ∑ b : Incidence formula, if L b = L a then 1 else 0 := by
  unfold rankN
  apply Finset.sum_lt_sum
  · intro c _
    by_cases h : lexLt formula c a ∧ L c = L a
    · rw [if_pos h, if_pos h.2]
    · rw [if_neg h]; exact Nat.zero_le _
  · refine ⟨a, Finset.mem_univ _, ?_⟩
    rw [if_neg (fun h => lexLt_irrefl formula a h.1), if_pos rfl]
    exact Nat.zero_lt_one

end NtimeDspace.Placement
