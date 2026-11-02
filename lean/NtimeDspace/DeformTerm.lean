import NtimeDspace.LabelTerm
import NtimeDspace.DeformationEvaluation

/-!
# Parity interpolation and the deformation entries as terms

The signed window start is held as two naturals, `start = sP - sN`. Terms for
the parity interpolant (`ParityEvaluation.evaluate`), the bad-label test, the
spectral coefficient `beta`, the residual over bad labels, and the matrix
`entry` and `coefficient` of `DeformationEvaluation`, all modulo `p`.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- `a - b` modulo `p`. -/
def subModT (pT a b : Term) : Term := mod (add a (sub pT (mod b pT))) pT

theorem cast_subModT {P : ℕ} (hP : 0 < P) (pT a b : Term) (env : List ℕ)
    (hpv : pT.denote w env = P) :
    ((subModT pT a b).denote w env : ZMod P) = (a.denote w env : ZMod P) - b.denote w env := by
  simp only [subModT, denote_mod, denote_add, denote_sub, hpv]
  exact cast_mod_add_sub_mod P _ _ hP

theorem StableAt.subModT {pT a b : Term} {env : List ℕ} (hp : StableAt w pT env)
    (ha : StableAt w a env) (hb : StableAt w b env) : StableAt w (subModT pT a b) env :=
  (ha.add (hp.sub (hb.mod hp))).mod hp

/-- The residue of `start + j`, for `start = sP - sN`. -/
def nodeT (pT sP sN j : Term) : Term := subModT pT (add sP j) sN

theorem cast_nodeT {P : ℕ} [Fact P.Prime] (hP : 0 < P) (pT sP sN j : Term) (env : List ℕ)
    (hpv : pT.denote w env = P) :
    ((nodeT pT sP sN j).denote w env : ZMod P) =
      ParityEvaluation.node P ((sP.denote w env : ℤ) - sN.denote w env) (j.denote w env) := by
  rw [nodeT, cast_subModT hP _ _ _ env hpv, denote_add]
  unfold ParityEvaluation.node
  push_cast
  ring

/-- A Lagrange basis value on the window. -/
def basisT (pT sP sN width slot x : Term) : Term :=
  Term.prodMod pT width fun other => ite (eqT other slot) (const 1)
    (mod (mul (subModT pT x (nodeT pT sP sN other))
      (invModT pT (subModT pT (nodeT pT sP sN slot) (nodeT pT sP sN other)))) pT)

/-- The parity interpolant at `x`. -/
def parityT (pT sP sN width x : Term) : Term :=
  Term.sumMod pT width fun slot =>
    mod (mul (signT pT (add (add sP slot) sN)) (basisT pT sP sN width slot x)) pT

theorem StableAt.nodeT {pT sP sN j : Term} {env : List ℕ} (hp : StableAt w pT env)
    (h1 : StableAt w sP env) (h2 : StableAt w sN env) (hj : StableAt w j env) :
    StableAt w (nodeT pT sP sN j) env := StableAt.subModT hp (h1.add hj) h2

section Parity

variable {P : ℕ} [Fact P.Prime] {pT sP sN widthT : Term} {env : List ℕ}

theorem cast_basisT (hP3 : 2 < P) (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hsP : StableAt w sP env) (hsN : StableAt w sN env) {slot x : Term}
    (hslot : StableAt w slot env) (hx : StableAt w x env) :
    ((basisT pT sP sN widthT slot x).denote w env : ZMod P) =
      ParityEvaluation.basisValue P ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)
        (slot.denote w env) (x.denote w env : ZMod P) := by
  have hP0 : 0 < P := by omega
  unfold basisT ParityEvaluation.basisValue
  rw [ParityEvaluation.productLoop_correct, mul_one,
    denote_prodModZ pT widthT _ env P (fun other => if other = slot.denote w env then 1 else
      ((x.denote w env : ZMod P) - ParityEvaluation.node P ((sP.denote w env : ℤ) - sN.denote w env)
        other) / (ParityEvaluation.node P ((sP.denote w env : ℤ) - sN.denote w env) (slot.denote w env) -
        ParityEvaluation.node P ((sP.denote w env : ℤ) - sN.denote w env) other)) hp hpv]
  intro acc other _
  set env' := acc :: other :: env
  have e' : env' = [acc, other] ++ env := rfl
  have hp' : StableAt w pT env' := hp.extend [acc, other]
  have hpv' : pT.denote w env' = P := by rw [hp.cons₂, hpv]
  have hov : (lvl env.length).denote w env' = other := denote_lvl_index env acc other
  have hos : StableAt w (lvl env.length) env' := stableAt_lvl (by simp [env'])
  rw [denote_ite, denote_eqT, hov, hslot.cons₂]
  by_cases h : other = slot.denote w env
  · simp [h]
  · rw [if_neg h, if_neg (lt_irrefl 0), denote_mod, hpv', ZMod.natCast_mod, denote_mul,
      Nat.cast_mul, cast_subModT hP0 _ _ _ env' hpv',
      invModT_denote pT _ env' P hP3 hp' hpv'
        (StableAt.subModT hp' (StableAt.nodeT hp' (hsP.extend [acc, other])
          (hsN.extend [acc, other]) (hslot.extend [acc, other]))
          (StableAt.nodeT hp' (hsP.extend [acc, other]) (hsN.extend [acc, other]) hos)),
      cast_subModT hP0 _ _ _ env' hpv']
    have e1 : x.denote w env' = x.denote w env := hx.cons₂ acc other
    have e2 : sP.denote w env' = sP.denote w env := hsP.cons₂ acc other
    have e3 : sN.denote w env' = sN.denote w env := hsN.cons₂ acc other
    have e4 : slot.denote w env' = slot.denote w env := hslot.cons₂ acc other
    simp only [cast_nodeT hP0 _ _ _ _ env' hpv', e1, e2, e3, e4, hov, div_eq_mul_inv, if_neg h]

theorem paritySign_sub (a b c : ℕ) :
    ParityEvaluation.paritySign P ((a : ℤ) - b + c) = (-1 : ZMod P) ^ (a + c + b) := by
  unfold ParityEvaluation.paritySign
  rcases Nat.even_or_odd (a + c + b) with h | h
  · rw [h.neg_one_pow, if_pos]
    obtain ⟨m, hm⟩ := h
    omega
  · rw [h.neg_one_pow, if_neg]
    obtain ⟨m, hm⟩ := h
    omega

theorem cast_parityT (hP3 : 2 < P) (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hsP : StableAt w sP env) (hsN : StableAt w sN env) (hwd : StableAt w widthT env)
    {x : Term} (hx : StableAt w x env) :
    ((parityT pT sP sN widthT x).denote w env : ZMod P) =
      ParityEvaluation.evaluate P ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)
        (x.denote w env : ZMod P) := by
  unfold parityT ParityEvaluation.evaluate
  rw [sumLoop_correct, add_zero,
    denote_sumModZ pT widthT _ env P (fun slot =>
      ParityEvaluation.paritySign P ((sP.denote w env : ℤ) - sN.denote w env + slot) *
        ParityEvaluation.basisValue P ((sP.denote w env : ℤ) - sN.denote w env)
          (widthT.denote w env) slot (x.denote w env : ZMod P)) hp hpv]
  intro acc slot _
  set env' := acc :: slot :: env
  have hp' : StableAt w pT env' := hp.extend [acc, slot]
  have hpv' : pT.denote w env' = P := by rw [hp.cons₂, hpv]
  have hsv : (lvl env.length).denote w env' = slot := denote_lvl_index env acc slot
  have hss : StableAt w (lvl env.length) env' := stableAt_lvl (by simp [env'])
  rw [denote_mod, hpv', ZMod.natCast_mod, denote_mul, Nat.cast_mul,
    signT_denote pT _ env' P (by omega) hpv',
    cast_basisT hP3 hp' hpv' (hsP.extend [acc, slot]) (hsN.extend [acc, slot]) hss
      (hx.extend [acc, slot]), paritySign_sub]
  have e1 : x.denote w env' = x.denote w env := hx.cons₂ acc slot
  have e2 : sP.denote w env' = sP.denote w env := hsP.cons₂ acc slot
  have e3 : sN.denote w env' = sN.denote w env := hsN.cons₂ acc slot
  have e4 : widthT.denote w env' = widthT.denote w env := hwd.cons₂ acc slot
  simp only [denote_add, e1, e2, e3, e4, hsv]

end Parity

/-! ### Counts of a label -/

section Counts

variable {rT QT u : Term} {env : List ℕ} {r Q : ℕ} (positive : 0 < r)

theorem StableAt.antisymT (positive : 0 < r) (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hu : StableAt w u env) :
    StableAt w (antisymT rT QT u) env := fun extra => by
  rw [denote_antisymT positive (hr.extend extra) (by rw [hr extra, hrv]) (by rw [hQ extra, hQv])
    (hu.extend extra), denote_antisymT positive hr hrv hQv hu, hu extra]

theorem denote_normExpT (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQv : QT.denote w env = Q) (hu : StableAt w u env) :
    (normExpT rT QT u).denote w env =
      TensorEvaluation.normExponent (SpectralIndexing.label r Q positive (u.denote w env)) := by
  unfold normExpT TensorEvaluation.normExponent
  rw [GroupedAssignmentEvaluation.scanSum_correct, add_zero,
    denote_sumT_lt _ _ env (fun node => if h : node < Q then
      (if (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, h⟩).1 ≠
        (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, h⟩).2 then 1 else 0) else 0),
    hQv, ← Fin.sum_univ_eq_sum_range]
  · exact Finset.sum_congr rfl fun node _ => by rw [dif_pos node.isLt]
  intro acc node hnode
  rw [hQv] at hnode
  have hr' : StableAt w rT (acc :: node :: env) := hr.extend [acc, node]
  have hrv' : rT.denote w (acc :: node :: env) = r := by rw [hr.cons₂, hrv]
  have hnv : (lvl env.length).denote w (acc :: node :: env) = node := denote_lvl_index env acc node
  have hnode' : (lvl env.length).denote w (acc :: node :: env) < Q := by rw [hnv]; exact hnode
  rw [denote_sub, denote_const, denote_eqT, denote_labFstT hr' hrv' positive u _ hnode',
    denote_labSndT hr' hrv' positive u _ hnode', dif_pos hnode]
  have e1 : u.denote w (acc :: node :: env) = u.denote w env := hu.cons₂ acc node
  simp only [e1, hnv]
  by_cases h : ((SpectralIndexing.label r Q positive (u.denote w env) ⟨node, hnode⟩).1 : ℕ) =
      (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, hnode⟩).2
  · rw [if_pos h, if_neg (not_not.mpr (Fin.ext h))]
  · rw [if_neg h, if_pos (fun h' => h (congrArg Fin.val h'))]

theorem antisym_spectral (m : ℕ) :
    SpectralIndexing.antisymmetricCount r Q positive m =
      TensorEvaluation.antisymmetricCount (SpectralIndexing.label r Q positive m) := by
  rw [SpectralIndexing.antisymmetricCount_correct, TensorEvaluation.antisymmetricCount_correct]

end Counts

/-! ### The bad test and `beta` -/

/-- Whether label `u` is bad: its antisymmetric count lies outside `[start, start + width)`. -/
def isBadT (rT QT sP sN widthT u : Term) : Term :=
  sub (const 1) (mul (sub (const 1) (lt (add (antisymT rT QT u) sN) sP))
    (lt (add (antisymT rT QT u) sN) (add sP widthT)))

theorem denote_isBadT {rT QT sP sN widthT u : Term} {env : List ℕ} {r Q : ℕ} (positive : 0 < r)
    (hr : StableAt w rT env) (hrv : rT.denote w env = r) (hQv : QT.denote w env = Q)
    (hu : StableAt w u env) :
    (isBadT rT QT sP sN widthT u).denote w env =
      (SpectralIndexing.isBad r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
        (widthT.denote w env) (u.denote w env)).toNat := by
  unfold isBadT SpectralIndexing.isBad
  rw [antisym_spectral positive]
  simp only [denote_sub, denote_const, denote_mul, denote_lt, denote_add,
    denote_antisymT positive hr hrv hQv hu]
  generalize TensorEvaluation.antisymmetricCount (SpectralIndexing.label r Q positive (u.denote w env)) = c
  generalize sP.denote w env = a
  generalize sN.denote w env = b
  generalize widthT.denote w env = d
  by_cases h1 : c + b < a
  · have : ¬((a : ℤ) - b ≤ c ∧ (c : ℤ) < a - b + d) := by omega
    rw [decide_eq_true this, if_pos h1]; simp
  · by_cases h2 : c + b < a + d
    · have : ((a : ℤ) - b ≤ c ∧ (c : ℤ) < a - b + d) := by omega
      rw [decide_eq_false (not_not_intro this), if_neg h1, if_pos h2]; rfl
    · have : ¬((a : ℤ) - b ≤ c ∧ (c : ℤ) < a - b + d) := by omega
      rw [decide_eq_true this, if_neg h1, if_neg h2]; rfl

/-- The spectral coefficient `beta(u, idx)`, modulo `p`. -/
def betaT (pT rT QT sP sN widthT u idx : Term) : Term :=
  mod (mul (mod (mul (subModT pT (const 1) (mod (mul (signT pT (antisymT rT QT idx))
      (parityT pT sP sN widthT (antisymT rT QT idx))) pT)) (tensorEntryT pT rT QT idx u)) pT)
    (powModT pT (invModT pT (const 2)) (normExpT rT QT idx))) pT

theorem cast_betaT {P r Q : ℕ} [Fact P.Prime] (hP3 : 2 < P) (positive : 0 < r)
    {pT rT QT sP sN widthT u idx : Term} {env : List ℕ}
    (hp : StableAt w pT env) (hpv : pT.denote w env = P) (hr : StableAt w rT env)
    (hrv : rT.denote w env = r) (hQ : StableAt w QT env) (hQv : QT.denote w env = Q)
    (hsP : StableAt w sP env) (hsN : StableAt w sN env) (hwd : StableAt w widthT env)
    (hu : StableAt w u env) (hidx : StableAt w idx env) :
    ((betaT pT rT QT sP sN widthT u idx).denote w env : ZMod P) =
      DeformationEvaluation.beta P ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)
        (SpectralIndexing.label r Q positive (u.denote w env))
        (SpectralIndexing.label r Q positive (idx.denote w env)) := by
  have hP0 : 0 < P := by omega
  have hanti := StableAt.antisymT positive hr hrv hQ hQv hidx
  have h2 : ∀ acc k, ((invModT pT (const 2)).denote w (acc :: k :: env) : ZMod P) = (2 : ZMod P)⁻¹ :=
    fun acc k => by
      rw [invModT_denote pT (const 2) (acc :: k :: env) P hP3 (hp.extend [acc, k])
        (by rw [hp.cons₂, hpv]) (stableAt_const _ _)]
      simp
  unfold betaT DeformationEvaluation.beta TensorEvaluation.tensorNorm
  simp only [denote_mod, hpv, ZMod.natCast_mod, denote_mul, Nat.cast_mul]
  rw [cast_subModT hP0 _ _ _ env hpv, denote_mod, hpv, ZMod.natCast_mod, denote_mul, Nat.cast_mul,
    signT_denote pT _ env P (by omega) hpv, cast_parityT hP3 hp hpv hsP hsN hwd hanti,
    cast_tensorEntryT positive hp hpv hr hrv hQv hidx hu,
    powModT_denote' pT _ _ env P _ hp hpv h2, denote_normExpT positive hr hrv hQv hidx,
    denote_antisymT positive hr hrv hQv hidx, inv_pow, div_eq_mul_inv]
  simp

/-! ### The residual over bad labels -/

/-- **The residual as a sum over label numbers.** The spec streams bad labels in ordinal order;
the same sum runs over all label numbers with the bad test. -/
theorem residual_eq_sum_masks {P r Q : ℕ} [Fact P.Prime] (positive : 0 < r) (start : ℤ)
    (width : ℕ) (u w' : TensorEvaluation.Label r Q) :
    DeformationEvaluation.residual P positive start width u w' =
      ∑ m ∈ Finset.range ((r * r) ^ Q),
        if SpectralIndexing.isBad r Q positive start width m then
          DeformationEvaluation.beta P start width u (SpectralIndexing.label r Q positive m) *
            TensorEvaluation.tensorEntry (SpectralIndexing.label r Q positive m) w' else 0 := by
  classical
  set g : TensorEvaluation.Label r Q → ZMod P := fun L =>
    DeformationEvaluation.beta P start width u L * TensorEvaluation.tensorEntry L w'
  unfold DeformationEvaluation.residual
  rw [GroupedAssignmentEvaluation.scanSum_correct, add_zero]
  change ∑ ord, (fun b : SpectralIndexing.BadLabel r Q start width => g b.val)
    (SpectralIndexing.badAtEquiv r Q positive start width ord) = _
  rw [Equiv.sum_comp (SpectralIndexing.badAtEquiv r Q positive start width)
      (fun b : SpectralIndexing.BadLabel r Q start width => g b.val),
    Finset.sum_coe_sort (FiniteFieldDeformation.bad start width) g,
    ← Finset.sum_ite_mem_eq (FiniteFieldDeformation.bad start width) g,
    ← (SpectralIndexing.labelEquiv r Q positive).sum_comp
      (fun L => if L ∈ FiniteFieldDeformation.bad start width then g L else 0)]
  rw [← Fin.sum_univ_eq_sum_range (fun m => if SpectralIndexing.isBad r Q positive start width m then
    g (SpectralIndexing.label r Q positive m) else 0)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hl : SpectralIndexing.labelEquiv r Q positive m = SpectralIndexing.label r Q positive m := rfl
  rw [hl]
  by_cases hb : SpectralIndexing.isBad r Q positive start width m = true
  · rw [if_pos ((SpectralIndexing.isBad_correct r Q positive start width m).mp hb), if_pos hb]
  · rw [if_neg (fun h => hb ((SpectralIndexing.isBad_correct r Q positive start width m).mpr h)),
      if_neg hb]

/-- The residual of `u` and `w'`: the sum over bad label numbers `m` of
`beta(u, m) · tensorEntry(m, w')`, modulo `p`. -/
def residualT (pT rT QT sP sN widthT u w' : Term) : Term :=
  Term.sumMod pT (powT (mul rT rT) QT) fun m => ite (isBadT rT QT sP sN widthT m)
    (mod (mul (betaT pT rT QT sP sN widthT u m) (tensorEntryT pT rT QT m w')) pT) (const 0)

section Residual

variable {P r Q : ℕ} [Fact P.Prime] {pT rT QT sP sN widthT u w' : Term} {env : List ℕ}

theorem cast_residualT (hP3 : 2 < P) (positive : 0 < r)
    (hp : StableAt w pT env) (hpv : pT.denote w env = P) (hr : StableAt w rT env)
    (hrv : rT.denote w env = r) (hQ : StableAt w QT env) (hQv : QT.denote w env = Q)
    (hsP : StableAt w sP env) (hsN : StableAt w sN env) (hwd : StableAt w widthT env)
    (hu : StableAt w u env) (hw : StableAt w w' env) :
    ((residualT pT rT QT sP sN widthT u w').denote w env : ZMod P) =
      DeformationEvaluation.residual P positive ((sP.denote w env : ℤ) - sN.denote w env)
        (widthT.denote w env) (SpectralIndexing.label r Q positive (u.denote w env))
        (SpectralIndexing.label r Q positive (w'.denote w env)) := by
  rw [residual_eq_sum_masks]
  unfold residualT
  rw [denote_sumModZ pT _ _ env P _ hp hpv, powT_denote _ _ _ (hr.mul hr), denote_mul, hrv, hQv]
  intro acc m _
  set env' := acc :: m :: env
  have hp' : StableAt w pT env' := hp.extend [acc, m]
  have hpv' : pT.denote w env' = P := by rw [hp.cons₂, hpv]
  have hr' : StableAt w rT env' := hr.extend [acc, m]
  have hrv' : rT.denote w env' = r := by rw [hr.cons₂, hrv]
  have hQ' : StableAt w QT env' := hQ.extend [acc, m]
  have hQv' : QT.denote w env' = Q := by rw [hQ.cons₂, hQv]
  have hm : StableAt w (lvl env.length) env' := stableAt_lvl (by simp [env'])
  have hmv : (lvl env.length).denote w env' = m := denote_lvl_index env acc m
  have e1 : sP.denote w env' = sP.denote w env := hsP.cons₂ acc m
  have e2 : sN.denote w env' = sN.denote w env := hsN.cons₂ acc m
  have e3 : widthT.denote w env' = widthT.denote w env := hwd.cons₂ acc m
  have e4 : u.denote w env' = u.denote w env := hu.cons₂ acc m
  have e5 : w'.denote w env' = w'.denote w env := hw.cons₂ acc m
  rw [denote_ite, denote_isBadT positive hr' hrv' hQv' hm, hmv, e1, e2, e3]
  cases SpectralIndexing.isBad r Q positive ((sP.denote w env : ℤ) - sN.denote w env)
    (widthT.denote w env) m
  · simp
  · rw [if_pos (by simp), if_pos rfl, denote_mod, hpv', ZMod.natCast_mod, denote_mul, Nat.cast_mul,
      cast_betaT hP3 positive hp' hpv' hr' hrv' hQ' hQv' (hsP.extend [acc, m])
        (hsN.extend [acc, m]) (hwd.extend [acc, m]) (hu.extend [acc, m]) hm,
      cast_tensorEntryT positive hp' hpv' hr' hrv' hQv' hm (hw.extend [acc, m]), hmv, e1, e2, e3,
      e4, e5]

end Residual

/-- The matrix entry `A[u, w']`: identity entry minus the residual, modulo `p`. -/
def entryT (pT rT QT sP sN widthT u w' : Term) : Term :=
  subModT pT (sameLabelT rT QT u w') (residualT pT rT QT sP sN widthT u w')

/-- The deformation coefficient at `point`, modulo `p`, with node values `node + 1`. -/
def coefficientT (pT rT QT sP sN widthT u w' point : Term) : Term :=
  mod (add (residualT pT rT QT sP sN widthT u w')
    (mul (entryT pT rT QT sP sN widthT u w') (mismatchT pT rT QT u w' point))) pT

section Entry

variable {P r Q : ℕ} [Fact P.Prime] {pT rT QT sP sN widthT u w' : Term} {env : List ℕ}

theorem cast_entryT (hP3 : 2 < P) (positive : 0 < r)
    (hp : StableAt w pT env) (hpv : pT.denote w env = P) (hr : StableAt w rT env)
    (hrv : rT.denote w env = r) (hQ : StableAt w QT env) (hQv : QT.denote w env = Q)
    (hsP : StableAt w sP env) (hsN : StableAt w sN env) (hwd : StableAt w widthT env)
    (hu : StableAt w u env) (hw : StableAt w w' env) :
    ((entryT pT rT QT sP sN widthT u w').denote w env : ZMod P) =
      DeformationEvaluation.entry P positive ((sP.denote w env : ℤ) - sN.denote w env)
        (widthT.denote w env) (SpectralIndexing.label r Q positive (u.denote w env))
        (SpectralIndexing.label r Q positive (w'.denote w env)) := by
  unfold entryT DeformationEvaluation.entry
  rw [cast_subModT (by omega) _ _ _ env hpv, denote_sameLabelT positive hr hrv hQv hu hw,
    cast_residualT hP3 positive hp hpv hr hrv hQ hQv hsP hsN hwd hu hw]
  split_ifs <;> simp

theorem cast_coefficientT (hP3 : 2 < P) (positive : 0 < r) {point : Term}
    (hp : StableAt w pT env) (hpv : pT.denote w env = P) (hr : StableAt w rT env)
    (hrv : rT.denote w env = r) (hQ : StableAt w QT env) (hQv : QT.denote w env = Q)
    (hsP : StableAt w sP env) (hsN : StableAt w sN env) (hwd : StableAt w widthT env)
    (hu : StableAt w u env) (hw : StableAt w w' env) (hpt : StableAt w point env) :
    ((coefficientT pT rT QT sP sN widthT u w' point).denote w env : ZMod P) =
      DeformationEvaluation.coefficient P positive (nodeValues (P := P) Q)
        ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)
        (SpectralIndexing.label r Q positive (u.denote w env))
        (SpectralIndexing.label r Q positive (w'.denote w env)) (point.denote w env : ZMod P) := by
  have hent := cast_entryT hP3 positive hp hpv hr hrv hQ hQv hsP hsN hwd hu hw
  unfold DeformationEvaluation.entry at hent
  unfold coefficientT DeformationEvaluation.coefficient
  rw [denote_mod, hpv, ZMod.natCast_mod, denote_add, Nat.cast_add, denote_mul, Nat.cast_mul,
    cast_residualT hP3 positive hp hpv hr hrv hQ hQv hsP hsN hwd hu hw, hent,
    cast_mismatchT positive hP3 hp hpv hr hrv hQv hu hw hpt]

end Entry

end NtimeDspace.ProgTerm
