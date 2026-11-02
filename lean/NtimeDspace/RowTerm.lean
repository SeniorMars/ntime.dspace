import NtimeDspace.FiniteFieldTerm

/-!
# Bad-label counting and row selection as terms

`badBeforeT lim` counts bad label numbers below `lim`
(`SpectralIndexing.countBefore`), `badCountT` counts all of them, and
`selMaskT ord` is the bad label number of rank `ord`
(`SpectralIndexing.selectedMask`), found as a sum over all label numbers since
exactly one bad label has a given rank.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

section Def

variable (rT QT sP sN widthT : Term)

def badBeforeT (lim : Term) : Term :=
  sumT (powT (mul rT rT) QT) fun m => mul (lt m lim) (isBadT rT QT sP sN widthT m)

def badCountT : Term := badBeforeT rT QT sP sN widthT (powT (mul rT rT) QT)

def selMaskT (ord : Term) : Term :=
  sumT (powT (mul rT rT) QT) fun m =>
    mul (mul (isBadT rT QT sP sN widthT m) (eqT (badBeforeT rT QT sP sN widthT m) ord)) m

end Def

variable {r Q : ℕ} (positive : 0 < r)

theorem countBefore_eq_sum (start : ℤ) (width lim : ℕ) :
    SpectralIndexing.countBefore r Q positive start width lim =
      ∑ m ∈ Finset.range ((r * r) ^ Q),
        if m < lim ∧ SpectralIndexing.isBad r Q positive start width m = true then 1 else 0 := by
  unfold SpectralIndexing.countBefore
  rw [LocalAssignmentLoop.countBefore, sumLoop_correct, Nat.add_zero]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [dif_pos (Finset.mem_range.mp hm)]
  rfl

theorem countBefore_lt_of_bad (start : ℤ) (width : ℕ) {m1 m2 : ℕ} (hlt : m1 < m2)
    (hm2 : m2 ≤ (r * r) ^ Q)
    (hb : SpectralIndexing.isBad r Q positive start width m1 = true) :
    SpectralIndexing.countBefore r Q positive start width m1 <
      SpectralIndexing.countBefore r Q positive start width m2 := by
  rw [countBefore_eq_sum, countBefore_eq_sum]
  apply Finset.sum_lt_sum
  · intro m _
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨by omega, h1.2⟩ h2
    · exact Nat.zero_le _
    · exact le_rfl
  · refine ⟨m1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [if_neg (by omega), if_pos ⟨hlt, hb⟩]
    exact Nat.zero_lt_one

/-- At most one bad label number has a given rank. -/
theorem bad_rank_unique (start : ℤ) (width : ℕ) {m1 m2 : ℕ} (h1 : m1 < (r * r) ^ Q)
    (h2 : m2 < (r * r) ^ Q) (b1 : SpectralIndexing.isBad r Q positive start width m1 = true)
    (b2 : SpectralIndexing.isBad r Q positive start width m2 = true)
    (c : SpectralIndexing.countBefore r Q positive start width m1 =
      SpectralIndexing.countBefore r Q positive start width m2) : m1 = m2 := by
  rcases lt_trichotomy m1 m2 with h | h | h
  · exact absurd c (countBefore_lt_of_bad positive start width h h2.le b1).ne
  · exact h
  · exact absurd c.symm (countBefore_lt_of_bad positive start width h h1.le b2).ne

/-- The selected mask is the sum over label numbers of the unique bad one of rank `ord`. -/
theorem selectedMask_eq_sum (start : ℤ) (width : ℕ)
    (ord : Fin (SpectralIndexing.badCount r Q positive start width)) :
    SpectralIndexing.selectedMask r Q positive start width ord.val =
      ∑ m ∈ Finset.range ((r * r) ^ Q),
        if SpectralIndexing.isBad r Q positive start width m = true ∧
          SpectralIndexing.countBefore r Q positive start width m = ord.val then m else 0 := by
  obtain ⟨hs1, hs2, hs3⟩ := SpectralIndexing.selectedMask_spec r Q positive start width ord
  rw [Finset.sum_eq_single (SpectralIndexing.selectedMask r Q positive start width ord.val)]
  · rw [if_pos ⟨hs2, hs3⟩]
  · intro m hm hne
    rw [if_neg]
    rintro ⟨hb, hc⟩
    exact hne (bad_rank_unique positive start width (Finset.mem_range.mp hm) hs1 hb hs2
      (hc.trans hs3.symm))
  · intro h; exact absurd (Finset.mem_range.mpr hs1) h

section Denote

variable {rT QT sP sN widthT : Term} {env : List ℕ}

theorem denote_badBeforeT (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hsP : StableAt w sP env)
    (hsN : StableAt w sN env) (hwd : StableAt w widthT env) {lim : Term} (hl : StableAt w lim env) :
    (badBeforeT rT QT sP sN widthT lim).denote w env =
      SpectralIndexing.countBefore r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
        (widthT.denote w env) (lim.denote w env) := by
  rw [countBefore_eq_sum]
  unfold badBeforeT
  rw [denote_sumT _ _ env (fun m => if m < lim.denote w env ∧ SpectralIndexing.isBad r Q positive
      ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env) m = true then 1 else 0),
    powT_denote _ _ _ (hr.mul hr), denote_mul, hrv, hQv]
  intro acc m
  have hr' : StableAt w rT (acc :: m :: env) := hr.extend [acc, m]
  have hrv' : rT.denote w (acc :: m :: env) = r := by rw [hr.cons₂, hrv]
  have hQv' : QT.denote w (acc :: m :: env) = Q := by rw [hQ.cons₂, hQv]
  have hm : StableAt w (lvl env.length) (acc :: m :: env) := stableAt_lvl (by simp)
  have hmv : (lvl env.length).denote w (acc :: m :: env) = m := denote_lvl_index env acc m
  rw [denote_mul, denote_lt, denote_isBadT positive hr' hrv' hQv' hm, hmv, hl.cons₂,
    hsP.cons₂, hsN.cons₂, hwd.cons₂]
  by_cases h1 : m < lim.denote w env <;>
    cases SpectralIndexing.isBad r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
      (widthT.denote w env) m <;> simp [h1]

theorem StableAt.badBeforeT (positive : 0 < r) (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hsP : StableAt w sP env)
    (hsN : StableAt w sN env) (hwd : StableAt w widthT env) {lim : Term} (hl : StableAt w lim env) :
    StableAt w (badBeforeT rT QT sP sN widthT lim) env := fun extra => by
  rw [denote_badBeforeT positive (hr.extend extra) (by rw [hr extra, hrv]) (hQ.extend extra)
    (by rw [hQ extra, hQv]) (hsP.extend extra) (hsN.extend extra) (hwd.extend extra)
    (hl.extend extra), denote_badBeforeT positive hr hrv hQ hQv hsP hsN hwd hl, hsP extra,
    hsN extra, hwd extra, hl extra]

theorem denote_badCountT (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hsP : StableAt w sP env)
    (hsN : StableAt w sN env) (hwd : StableAt w widthT env) :
    (badCountT rT QT sP sN widthT).denote w env =
      SpectralIndexing.badCount r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
        (widthT.denote w env) := by
  unfold badCountT SpectralIndexing.badCount
  rw [denote_badBeforeT positive hr hrv hQ hQv hsP hsN hwd (StableAt.powT (hr.mul hr) hQ),
    powT_denote _ _ _ (hr.mul hr), denote_mul, hrv, hQv]

theorem denote_selMaskT_sum (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hsP : StableAt w sP env)
    (hsN : StableAt w sN env) (hwd : StableAt w widthT env) {ord : Term} (ho : StableAt w ord env) :
    (selMaskT rT QT sP sN widthT ord).denote w env =
      ∑ m ∈ Finset.range ((r * r) ^ Q),
        if SpectralIndexing.isBad r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
            (widthT.denote w env) m = true ∧
          SpectralIndexing.countBefore r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
            (widthT.denote w env) m = ord.denote w env then m else 0 := by
  unfold selMaskT
  rw [denote_sumT _ _ env (fun m => if SpectralIndexing.isBad r Q positive
      ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env) m = true ∧
      SpectralIndexing.countBefore r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
        (widthT.denote w env) m = ord.denote w env then m else 0),
    powT_denote _ _ _ (hr.mul hr), denote_mul, hrv, hQv]
  intro acc m
  set env' := acc :: m :: env
  have hr' : StableAt w rT env' := hr.extend [acc, m]
  have hrv' : rT.denote w env' = r := by rw [hr.cons₂, hrv]
  have hQ' : StableAt w QT env' := hQ.extend [acc, m]
  have hQv' : QT.denote w env' = Q := by rw [hQ.cons₂, hQv]
  have hm : StableAt w (lvl env.length) env' := stableAt_lvl (by simp [env'])
  have hmv : (lvl env.length).denote w env' = m := denote_lvl_index env acc m
  have e1 : sP.denote w env' = sP.denote w env := hsP.cons₂ acc m
  have e2 : sN.denote w env' = sN.denote w env := hsN.cons₂ acc m
  have e3 : widthT.denote w env' = widthT.denote w env := hwd.cons₂ acc m
  have e4 : ord.denote w env' = ord.denote w env := ho.cons₂ acc m
  rw [denote_mul, denote_mul, denote_isBadT positive hr' hrv' hQv' hm, denote_eqT,
    denote_badBeforeT positive hr' hrv' hQ' hQv' (hsP.extend [acc, m]) (hsN.extend [acc, m])
      (hwd.extend [acc, m]) hm, hmv, e1, e2, e3, e4]
  cases SpectralIndexing.isBad r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
      (widthT.denote w env) m <;>
    by_cases h : SpectralIndexing.countBefore r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
      (widthT.denote w env) m = ord.denote w env <;> simp [h]

theorem denote_selMaskT (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hsP : StableAt w sP env)
    (hsN : StableAt w sN env) (hwd : StableAt w widthT env) {ord : Term} (ho : StableAt w ord env)
    (hlt : ord.denote w env < SpectralIndexing.badCount r Q positive
      ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)) :
    (selMaskT rT QT sP sN widthT ord).denote w env =
      SpectralIndexing.selectedMask r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
        (widthT.denote w env) (ord.denote w env) := by
  rw [show ord.denote w env = (⟨ord.denote w env, hlt⟩ : Fin _).val from rfl,
    selectedMask_eq_sum positive, denote_selMaskT_sum positive hr hrv hQ hQv hsP hsN hwd ho]

theorem StableAt.selMaskT (positive : 0 < r) (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hsP : StableAt w sP env)
    (hsN : StableAt w sN env) (hwd : StableAt w widthT env) {ord : Term} (ho : StableAt w ord env) :
    StableAt w (selMaskT rT QT sP sN widthT ord) env := fun extra => by
  rw [denote_selMaskT_sum positive (hr.extend extra) (by rw [hr extra, hrv]) (hQ.extend extra)
    (by rw [hQ extra, hQv]) (hsP.extend extra) (hsN.extend extra) (hwd.extend extra)
    (ho.extend extra), denote_selMaskT_sum positive hr hrv hQ hQv hsP hsN hwd ho, hsP extra,
    hsN extra, hwd extra, ho extra]

theorem StableAt.badCountT (positive : 0 < r) (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hsP : StableAt w sP env)
    (hsN : StableAt w sN env) (hwd : StableAt w widthT env) :
    StableAt w (badCountT rT QT sP sN widthT) env :=
  StableAt.badBeforeT positive hr hrv hQ hQv hsP hsN hwd (StableAt.powT (hr.mul hr) hQ)

end Denote

end NtimeDspace.ProgTerm
