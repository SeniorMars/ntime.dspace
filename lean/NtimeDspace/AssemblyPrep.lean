import NtimeDspace.PlacementSearch
import NtimeDspace.CounterTerm
import NtimeDspace.WConcreteCountingLoop

/-!
# Preparation for assembling the counter

Contracts for the group and label terms, and the copy map of a balanced seed
number with its injectivity.
-/

namespace NtimeDspace.ProgTerm

open Term Placement WeightedSystem

variable {w : List Bool} {n : ℕ}

theorem implN_grpT {QT bitsT IBT sT h nd : Term} {env : List ℕ} (hQ : StableAt w QT env)
    (hb : StableAt w bitsT env) (hIB : StableAt w IBT env) (hs : StableAt w sT env)
    (hh : StableAt w h env) (hnd : StableAt w nd env) :
    ImplN w env (grpT QT bitsT IBT sT h nd)
      (grpN (QT.denote w env) (bitsT.denote w env) (IBT.denote w env) (sT.denote w env)
        (h.denote w env) (nd.denote w env)) := by
  intro pre a ha
  have key : ∀ (pre : List ℕ) (a : Term), StableAt w a (pre ++ env) →
      (grpT QT bitsT IBT sT h nd a).denote w (pre ++ env) =
        grpN (QT.denote w env) (bitsT.denote w env) (IBT.denote w env) (sT.denote w env)
          (h.denote w env) (nd.denote w env) (a.denote w (pre ++ env)) := by
    intro pre a ha
    rw [denote_grpT (hIB.extend pre) (hQ.extend pre) (hb.extend pre) (hs.extend pre)
      (hh.extend pre) (hnd.extend pre) ha, hQ pre, hb pre, hIB pre, hs pre, hh pre, hnd pre]
  refine ⟨key pre a ha, fun extra => ?_⟩
  rw [← List.append_assoc, key _ a (by rw [List.append_assoc]; exact ha.extend extra),
    List.append_assoc, ha extra, key pre a ha]

theorem implN2_labelT {QT bitsT IBT sT : Term} {varT : Term → Term → Term} {V : ℕ → ℕ → ℕ}
    {env : List ℕ} (hQ : StableAt w QT env) (hb : StableAt w bitsT env)
    (hIB : StableAt w IBT env) (hs : StableAt w sT env) (iV : ImplN2 w env varT V) :
    ImplN2 w env (fun e i => labelT QT bitsT IBT sT (varT e i) e)
      (fun e i => labelN (QT.denote w env) (bitsT.denote w env) (sT.denote w env)
        (IBT.denote w env) (V e i) e) := by
  have key : ∀ (pre : List ℕ) (a b : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
      (labelT QT bitsT IBT sT (varT a b) a).denote w (pre ++ env) =
        labelN (QT.denote w env) (bitsT.denote w env) (sT.denote w env) (IBT.denote w env)
          (V (a.denote w (pre ++ env)) (b.denote w (pre ++ env))) (a.denote w (pre ++ env)) := by
    intro pre a b ha hb'
    obtain ⟨v1, vs⟩ := iV pre a b ha hb'
    rw [denote_labelT (hIB.extend pre) (hQ.extend pre) (hb.extend pre) (hs.extend pre) vs ha, v1,
      hQ pre, hb pre, hs pre, hIB pre]
  intro pre a b ha hb'
  refine ⟨key pre a b ha hb', fun extra => ?_⟩
  rw [← List.append_assoc, key _ a b (by rw [List.append_assoc]; exact ha.extend extra)
    (by rw [List.append_assoc]; exact hb'.extend extra), List.append_assoc, ha extra, hb' extra,
    key pre a b ha hb']

/-- The number of copies for a balanced seed. -/
def copiesOf (S : System n) (Q bits : ℕ) : ℕ := 2 * incidenceCount S / (2 ^ bits * 2 ^ bits) ^ Q

theorem rankN_lt_copies (S : System n) (Q bits s : ℕ) (hbal : balN S Q bits s) (inc : Incidence S) :
    rankN S (incLabelN S Q bits s) inc < copiesOf S Q bits := by
  have hb := hbal.1 _ (incLabelN_lt S Q bits s inc)
  have hlt := rankN_lt_bucket S (incLabelN S Q bits s) inc
  have hpos : 0 < (2 ^ bits * 2 ^ bits) ^ Q := by positivity
  unfold copiesOf
  exact lt_of_lt_of_le hlt ((Nat.le_div_iff_mul_le hpos).mpr hb)

/-- The copy map of a balanced seed number. -/
def copyOfS (S : System n) (Q bits s : ℕ) (hbal : balN S Q bits s) :
    Incidence S → Fin (copiesOf S Q bits) :=
  fun inc => ⟨rankN S (incLabelN S Q bits s) inc, rankN_lt_copies S Q bits s hbal inc⟩

theorem placement_injective_S (S : System n) (Q bits s : ℕ) (hbal : balN S Q bits s) :
    Function.Injective (fun inc => (copyOfS S Q bits s hbal inc,
      (WSchedulePlacement.incidenceLabel S bits (seedOf S Q bits s) inc :
        TensorEvaluation.Label (2 ^ bits) Q))) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  apply rank_label_injective S (incLabelN S Q bits s)
  simp only [Prod.mk.injEq]
  have hl : incLabelN S Q bits s a = incLabelN S Q bits s b := by
    apply label_injective_lt Q bits (incLabelN_lt S Q bits s a) (incLabelN_lt S Q bits s b)
    have ha := incidenceLabel_seedOf S Q bits s a
    have hb := incidenceLabel_seedOf S Q bits s b
    unfold incLabelN
    rw [← ha, ← hb]
    exact h.2
  exact ⟨congrArg Fin.val h.1, hl⟩

end NtimeDspace.ProgTerm
