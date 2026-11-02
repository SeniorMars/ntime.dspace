import NtimeDspace.GroupedTerm

/-!
# Integer tensor signs

`integerTensorSign index position` is a product over nodes of pair signs in
`{-1, 0, 1}`, so it is `0` unless every pair sign is nonzero, and otherwise
`(-1)` to the number of negative pair signs. Terms compute the indicator of a
positive and of a negative sign for label numbers.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool} {r Q : ℕ}

/-- A nonzero pair sign. -/
def pairNZ (i q : Fin r × Fin r) : Prop := q = i ∨ (i.1 ≠ i.2 ∧ q = i.swap)
/-- A negative pair sign. -/
def pairNeg (i q : Fin r × Fin r) : Prop := i.2 < i.1 ∧ q = i.swap

instance (i q : Fin r × Fin r) : Decidable (pairNZ i q) := by unfold pairNZ; infer_instance
instance (i q : Fin r × Fin r) : Decidable (pairNeg i q) := by unfold pairNeg; infer_instance

theorem integerPairSign_eq (i q : Fin r × Fin r) :
    WGroupedAccessorEvaluation.integerPairSign i q =
      if pairNZ i q then (if pairNeg i q then -1 else 1) else 0 := by
  obtain ⟨i1, i2⟩ := i
  obtain ⟨q1, q2⟩ := q
  unfold WGroupedAccessorEvaluation.integerPairSign pairNZ pairNeg
  simp only [Prod.mk.injEq, Prod.swap_prod_mk, ne_eq]
  by_cases d : i1 = i2
  · subst d
    by_cases x : q1 = i1 <;> by_cases y : q2 = i1 <;> simp [x, y]
  · by_cases o : i1 < i2
    · have no : ¬ i2 < i1 := fun h => lt_asymm o h
      by_cases x : q1 = i1 <;> by_cases y : q2 = i2 <;> by_cases x' : q1 = i2 <;>
        by_cases y' : q2 = i1 <;> simp_all
    · have o' : i2 < i1 := lt_of_le_of_ne (not_lt.mp o) (Ne.symm d)
      by_cases x : q1 = i1 <;> by_cases y : q2 = i2 <;> by_cases x' : q1 = i2 <;>
        by_cases y' : q2 = i1 <;> simp_all

theorem integerTensorSign_eq (index position : TensorEvaluation.Label r Q) :
    WGroupedAccessorEvaluation.integerTensorSign index position =
      if ∀ node, pairNZ (index node) (position node) then
        (-1) ^ (Finset.univ.filter fun node => pairNeg (index node) (position node)).card
      else 0 := by
  unfold WGroupedAccessorEvaluation.integerTensorSign
  rw [WGroupedAssignmentEvaluation.scanProduct_correct, mul_one]
  simp only [integerPairSign_eq]
  split_ifs with hall
  · rw [Finset.card_filter, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun node _ => ?_
    rw [if_pos (hall node)]
    split_ifs <;> simp
  · push_neg at hall
    obtain ⟨node, hn⟩ := hall
    exact Finset.prod_eq_zero (Finset.mem_univ node) (by rw [if_neg hn])

theorem integerTensorSign_split (index position : TensorEvaluation.Label r Q) :
    WGroupedAccessorEvaluation.integerTensorSign index position =
      ((if (∀ node, pairNZ (index node) (position node)) ∧
          (Finset.univ.filter fun node => pairNeg (index node) (position node)).card % 2 = 0
        then 1 else 0 : ℕ) : ℤ) -
      ((if (∀ node, pairNZ (index node) (position node)) ∧
          (Finset.univ.filter fun node => pairNeg (index node) (position node)).card % 2 = 1
        then 1 else 0 : ℕ) : ℤ) := by
  rw [integerTensorSign_eq]
  by_cases hall : ∀ node, pairNZ (index node) (position node)
  · rcases Nat.mod_two_eq_zero_or_one
      (Finset.univ.filter fun node => pairNeg (index node) (position node)).card with h | h
    · rw [if_pos hall, Even.neg_one_pow (Nat.even_iff.mpr h), if_pos ⟨hall, h⟩,
        if_neg (fun h' => by omega)]
      simp
    · rw [if_pos hall, Odd.neg_one_pow (Nat.odd_iff.mpr h), if_neg (fun h' => by omega),
        if_pos ⟨hall, h⟩]
      simp
  · rw [if_neg hall, if_neg (fun h' => hall h'.1), if_neg (fun h' => hall h'.1)]
    simp

/-! ### Terms -/

section Terms

variable (rT QT : Term)

def pairNZT (u w' node : Term) : Term :=
  lt (const 0) (add (mul (eqT (labFstT rT w' node) (labFstT rT u node))
      (eqT (labSndT rT w' node) (labSndT rT u node)))
    (mul (sub (const 1) (eqT (labFstT rT u node) (labSndT rT u node)))
      (mul (eqT (labFstT rT w' node) (labSndT rT u node))
        (eqT (labSndT rT w' node) (labFstT rT u node)))))

def pairNegT (u w' node : Term) : Term :=
  mul (lt (labSndT rT u node) (labFstT rT u node))
    (mul (eqT (labFstT rT w' node) (labSndT rT u node))
      (eqT (labSndT rT w' node) (labFstT rT u node)))

def signPosT (u w' : Term) : Term :=
  mul (allT QT fun node => pairNZT rT u w' node)
    (eqT (mod (sumT QT fun node => pairNegT rT u w' node) (const 2)) (const 0))

def signNegT (u w' : Term) : Term :=
  mul (allT QT fun node => pairNZT rT u w' node)
    (mod (sumT QT fun node => pairNegT rT u w' node) (const 2))

end Terms

section Denote

variable {rT QT u w' : Term} {env : List ℕ} (positive : 0 < r)

/-- Node-level facts at a binder environment. -/
theorem node_facts (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hu : StableAt w u env) (hw : StableAt w w' env) (acc node : ℕ) (hnode : node < Q) :
    (pairNZT rT u w' (lvl env.length)).denote w (acc :: node :: env) =
        (if pairNZ (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, hnode⟩)
          (SpectralIndexing.label r Q positive (w'.denote w env) ⟨node, hnode⟩) then 1 else 0) ∧
      (pairNegT rT u w' (lvl env.length)).denote w (acc :: node :: env) =
        (if pairNeg (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, hnode⟩)
          (SpectralIndexing.label r Q positive (w'.denote w env) ⟨node, hnode⟩) then 1 else 0) := by
  have hr' : StableAt w rT (acc :: node :: env) := hr.extend [acc, node]
  have hrv' : rT.denote w (acc :: node :: env) = r := by rw [hr.cons₂, hrv]
  have hnv : (lvl env.length).denote w (acc :: node :: env) = node := denote_lvl_index env acc node
  have hnode' : (lvl env.length).denote w (acc :: node :: env) < Q := by rw [hnv]; exact hnode
  have e1 : u.denote w (acc :: node :: env) = u.denote w env := hu.cons₂ acc node
  have e2 : w'.denote w (acc :: node :: env) = w'.denote w env := hw.cons₂ acc node
  set i := SpectralIndexing.label r Q positive (u.denote w env) ⟨node, hnode⟩
  set q := SpectralIndexing.label r Q positive (w'.denote w env) ⟨node, hnode⟩
  have f1 : (labFstT rT u (lvl env.length)).denote w (acc :: node :: env) = i.1 := by
    rw [denote_labFstT hr' hrv' positive u _ hnode']; simp only [e1, hnv, i]
  have f2 : (labSndT rT u (lvl env.length)).denote w (acc :: node :: env) = i.2 := by
    rw [denote_labSndT hr' hrv' positive u _ hnode']; simp only [e1, hnv, i]
  have f3 : (labFstT rT w' (lvl env.length)).denote w (acc :: node :: env) = q.1 := by
    rw [denote_labFstT hr' hrv' positive w' _ hnode']; simp only [e2, hnv, q]
  have f4 : (labSndT rT w' (lvl env.length)).denote w (acc :: node :: env) = q.2 := by
    rw [denote_labSndT hr' hrv' positive w' _ hnode']; simp only [e2, hnv, q]
  obtain ⟨i1, i2⟩ := i
  obtain ⟨q1, q2⟩ := q
  constructor
  · unfold pairNZT pairNZ
    simp only [denote_lt, denote_add, denote_mul, denote_eqT, denote_sub, denote_const, f1, f2, f3,
      f4, Prod.mk.injEq, Prod.swap_prod_mk, ne_eq, Fin.val_inj]
    by_cases a : q1 = i1 <;> by_cases b : q2 = i2 <;> by_cases c : i1 = i2 <;>
      by_cases d : q1 = i2 <;> by_cases e : q2 = i1 <;> simp [a, b, c, d, e]
  · unfold pairNegT pairNeg
    simp only [denote_lt, denote_mul, denote_eqT, f1, f2, f3, f4, Prod.swap_prod_mk,
      Prod.mk.injEq, Fin.val_inj, Fin.lt_def]
    by_cases a : (i2 : ℕ) < i1 <;> by_cases d : q1 = i2 <;> by_cases e : q2 = i1 <;> simp [a, d, e]

theorem allT_denote_lt (n : Term) (test : Term → Term) (env : List ℕ) (Pr : ℕ → Prop)
    [DecidablePred Pr]
    (ht : ∀ acc i, i < n.denote w env →
      (test (lvl env.length)).denote w (acc :: i :: env) = if Pr i then 1 else 0) :
    (allT n test).denote w env = if ∀ i < n.denote w env, Pr i then 1 else 0 := by
  rw [allT, denote_eqT, denote_sumT_lt _ _ env (fun i => if Pr i then 0 else 1) (fun acc i hi => by
    simp only [denote_sub, denote_const, ht acc i hi]; split_ifs <;> rfl), denote_const]
  by_cases hall : ∀ i < n.denote w env, Pr i
  · rw [if_pos hall, if_pos (Finset.sum_eq_zero fun i hi => if_pos (hall i (Finset.mem_range.mp hi)))]
  · rw [if_neg hall, if_neg]
    push_neg at hall
    obtain ⟨i, hi, hni⟩ := hall
    intro hzero
    have := (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_range.mpr hi)
    rw [if_neg hni] at this
    exact one_ne_zero this

open Classical in
theorem denote_signT_parts (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQv : QT.denote w env = Q) (hu : StableAt w u env) (hw : StableAt w w' env) :
    (signPosT rT QT u w').denote w env =
        (if (∀ node, pairNZ (SpectralIndexing.label r Q positive (u.denote w env) node)
            (SpectralIndexing.label r Q positive (w'.denote w env) node)) ∧
          (Finset.univ.filter fun node => pairNeg (SpectralIndexing.label r Q positive
            (u.denote w env) node) (SpectralIndexing.label r Q positive (w'.denote w env) node)).card
            % 2 = 0 then 1 else 0) ∧
    (signNegT rT QT u w').denote w env =
        (if (∀ node, pairNZ (SpectralIndexing.label r Q positive (u.denote w env) node)
            (SpectralIndexing.label r Q positive (w'.denote w env) node)) ∧
          (Finset.univ.filter fun node => pairNeg (SpectralIndexing.label r Q positive
            (u.denote w env) node) (SpectralIndexing.label r Q positive (w'.denote w env) node)).card
            % 2 = 1 then 1 else 0) := by
  set U := SpectralIndexing.label r Q positive (u.denote w env)
  set W := SpectralIndexing.label r Q positive (w'.denote w env)
  have hall : (allT QT fun node => pairNZT rT u w' node).denote w env =
      if ∀ node : Fin Q, pairNZ (U node) (W node) then 1 else 0 := by
    rw [allT_denote_lt _ _ env (fun i => if h : i < Q then pairNZ (U ⟨i, h⟩) (W ⟨i, h⟩) else True)
      (fun acc i hi => by
        rw [hQv] at hi
        rw [(node_facts positive hr hrv hu hw acc i hi).1]; simp only [dif_pos hi]
        exact ite_iff' Iff.rfl), hQv]
    apply ite_iff'
    constructor
    · intro h node; have := h node node.isLt; rwa [dif_pos node.isLt] at this
    · intro h i hi; rw [dif_pos hi]; exact h ⟨i, hi⟩
  have hcnt : (sumT QT fun node => pairNegT rT u w' node).denote w env =
      (Finset.univ.filter fun node : Fin Q => pairNeg (U node) (W node)).card := by
    rw [denote_sumT_lt _ _ env (fun i => if h : i < Q then
        (if pairNeg (U ⟨i, h⟩) (W ⟨i, h⟩) then 1 else 0) else 0) (fun acc i hi => by
        rw [hQv] at hi
        rw [(node_facts positive hr hrv hu hw acc i hi).2, dif_pos hi]), hQv,
      Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun node _ => by rw [dif_pos node.isLt]
  constructor
  · unfold signPosT
    rw [denote_mul, hall, denote_eqT, denote_mod, hcnt, denote_const, denote_const]
    by_cases h1 : ∀ node : Fin Q, pairNZ (U node) (W node) <;>
      by_cases h2 : (Finset.univ.filter fun node : Fin Q => pairNeg (U node) (W node)).card % 2 = 0 <;>
      simp [h1, h2]
  · unfold signNegT
    rw [denote_mul, hall, denote_mod, hcnt, denote_const]
    by_cases h1 : ∀ node : Fin Q, pairNZ (U node) (W node) <;>
      rcases Nat.mod_two_eq_zero_or_one
        (Finset.univ.filter fun node : Fin Q => pairNeg (U node) (W node)).card with h2 | h2 <;>
      simp [h1, h2]

end Denote

end NtimeDspace.ProgTerm
