import NtimeDspace.RowTerm
import NtimeDspace.WGroupedAccessorEvaluation

/-!
# The grouped accessors as terms

Measurement rows are `(copy, bad label)` pairs numbered `ρ = rank + badCount · copy`
(`SpectralIndexing.rowAt`). This file gives terms for the measurement row
number, the measurement coefficient, the local coefficient, and the integer
measurement (as positive and negative parts) of `WGroupedAccessorEvaluation`.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-! ### Rows -/

variable {r Q : ℕ} (positive : 0 < r)

theorem rowAt_fst (copies : ℕ) (start : ℤ) (width : ℕ)
    (ρ : Fin (copies * SpectralIndexing.badCount r Q positive start width)) :
    ((SpectralIndexing.rowAt r Q positive copies start width ρ).1 : ℕ) =
      ρ / SpectralIndexing.badCount r Q positive start width := by
  simp [SpectralIndexing.rowAt, finProdFinEquiv]

theorem rowAt_snd (copies : ℕ) (start : ℤ) (width : ℕ)
    (ρ : Fin (copies * SpectralIndexing.badCount r Q positive start width)) :
    ((SpectralIndexing.rowAt r Q positive copies start width ρ).2 : TensorEvaluation.Label r Q) =
      SpectralIndexing.label r Q positive (SpectralIndexing.selectedMask r Q positive start width
        (ρ % SpectralIndexing.badCount r Q positive start width)) := by
  simp [SpectralIndexing.rowAt, finProdFinEquiv, SpectralIndexing.badAt,
    SpectralIndexing.badLabel, SpectralIndexing.badMaskAt]

theorem measurementRowNumber_rowAt (copies : ℕ) (start : ℤ) (width : ℕ) (g : Fin r)
    (ρ : Fin (copies * SpectralIndexing.badCount r Q positive start width)) :
    (SpectralIndexing.measurementRowNumber r Q positive copies start width
      ⟨g, SpectralIndexing.rowAt r Q positive copies start width ρ⟩ : ℕ) =
      ρ + copies * SpectralIndexing.badCount r Q positive start width * g := by
  have h : SpectralIndexing.rowNumber r Q positive copies start width
      (SpectralIndexing.rowAt r Q positive copies start width ρ) = ρ :=
    (SpectralIndexing.rowEquiv r Q positive copies start width).apply_symm_apply ρ
  simp only [SpectralIndexing.measurementRowNumber, finProdFinEquiv, Equiv.coe_fn_mk, h]

/-! ### The measurement coefficient -/

/-- The bad label number of rank `j`, as a sum (defined for every `j`). -/
def selMaskN (r Q : ℕ) (positive : 0 < r) (start : ℤ) (width j : ℕ) : ℕ :=
  ∑ m ∈ Finset.range ((r * r) ^ Q),
    if SpectralIndexing.isBad r Q positive start width m = true ∧
      SpectralIndexing.countBefore r Q positive start width m = j then m else 0

section MC

variable (pT rT QT sP sN widthT : Term) (cpT lbT : Term → Term → Term)

/-- The measurement coefficient of incidence `(e, i)` at row `ρ`. -/
def mcT (e i _g ρ : Term) : Term :=
  ite (eqT (div ρ (badCountT rT QT sP sN widthT)) (cpT e i))
    (betaT pT rT QT sP sN widthT (lbT e i)
      (selMaskT rT QT sP sN widthT (mod ρ (badCountT rT QT sP sN widthT))))
    (const 0)

end MC

variable {P : ℕ} [Fact P.Prime]

/-- The measurement coefficient on numbers. -/
noncomputable def mcN (r Q : ℕ) (positive : 0 < r) (start : ℤ) (width : ℕ) (CP LB : ℕ → ℕ → ℕ)
    (e i _g ρ : ℕ) : ZMod P :=
  if ρ / SpectralIndexing.badCount r Q positive start width = CP e i then
    DeformationEvaluation.beta P start width (SpectralIndexing.label r Q positive (LB e i))
      (SpectralIndexing.label r Q positive (selMaskN r Q positive start width
        (ρ % SpectralIndexing.badCount r Q positive start width)))
  else 0

theorem implZ4_mcT (hP3 : 2 < P) {pT rT QT sP sN widthT : Term} {cpT lbT : Term → Term → Term}
    {env : List ℕ} (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hr : StableAt w rT env) (hrv : rT.denote w env = r) (hQ : StableAt w QT env)
    (hQv : QT.denote w env = Q) (hsP : StableAt w sP env) (hsN : StableAt w sN env)
    (hwd : StableAt w widthT env) {CP LB : ℕ → ℕ → ℕ} (iCP : ImplN2 w env cpT CP)
    (iLB : ImplN2 w env lbT LB) :
    ImplZ4 w env P (mcT pT rT QT sP sN widthT cpT lbT)
      (mcN r Q positive ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env) CP LB) := by
  intro pre a b c d ha hb hc hd
  have hp' : StableAt w pT (pre ++ env) := hp.extend pre
  have hpv' : pT.denote w (pre ++ env) = P := by rw [hp pre, hpv]
  have hr' : StableAt w rT (pre ++ env) := hr.extend pre
  have hrv' : rT.denote w (pre ++ env) = r := by rw [hr pre, hrv]
  have hQ' : StableAt w QT (pre ++ env) := hQ.extend pre
  have hQv' : QT.denote w (pre ++ env) = Q := by rw [hQ pre, hQv]
  have hsP' : StableAt w sP (pre ++ env) := hsP.extend pre
  have hsN' : StableAt w sN (pre ++ env) := hsN.extend pre
  have hwd' : StableAt w widthT (pre ++ env) := hwd.extend pre
  have hbc := denote_badCountT positive hr' hrv' hQ' hQv' hsP' hsN' hwd'
  have hbcs := StableAt.badCountT positive hr' hrv' hQ' hQv' hsP' hsN' hwd'
  obtain ⟨cp, -⟩ := iCP pre a b ha hb
  obtain ⟨lb, lbs⟩ := iLB pre a b ha hb
  have hord : StableAt w (mod d (badCountT rT QT sP sN widthT)) (pre ++ env) := hd.mod hbcs
  have hsel := StableAt.selMaskT positive hr' hrv' hQ' hQv' hsP' hsN' hwd' hord
  unfold mcT mcN
  rw [denote_ite, denote_eqT, denote_div, hbc, cp, hsP pre, hsN pre, hwd pre]
  by_cases h : d.denote w (pre ++ env) / SpectralIndexing.badCount r Q positive
      ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env) = CP (a.denote w (pre ++ env)) (b.denote w (pre ++ env))
  · rw [if_pos (by simp [h]), if_pos h,
      cast_betaT hP3 positive hp' hpv' hr' hrv' hQ' hQv' hsP' hsN' hwd' lbs hsel, lb,
      denote_selMaskT_sum positive hr' hrv' hQ' hQv' hsP' hsN' hwd' hord, denote_mod, hbc,
      hsP pre, hsN pre, hwd pre]
    rfl
  · rw [if_neg (by simp [h]), if_neg h]
    simp

/-- **The measurement coefficient accessor** agrees with the spec at every row. -/
theorem mcN_spec {n copies : ℕ} (formula : WeightedSystem.System n) (start : ℤ) (width : ℕ)
    (copyOf : WeightedSystem.Incidence formula → Fin copies)
    (labelOf : WeightedSystem.Incidence formula → TensorEvaluation.Label r Q) (CP LB : ℕ → ℕ → ℕ)
    (hCP : ∀ inc : WeightedSystem.Incidence formula, CP inc.1 inc.2 = (copyOf inc).val)
    (hLB : ∀ inc : WeightedSystem.Incidence formula,
      labelOf inc = SpectralIndexing.label r Q positive (LB inc.1 inc.2))
    (inc : WeightedSystem.Incidence formula) (g : Fin r)
    (ρ : Fin (copies * SpectralIndexing.badCount r Q positive start width)) :
    mcN (P := P) r Q positive start width CP LB inc.1 inc.2 g ρ =
      WGroupedAccessorEvaluation.measurementCoefficient P formula copyOf labelOf start width inc g
        (SpectralIndexing.rowAt r Q positive copies start width ρ) := by
  have hbc : 0 < SpectralIndexing.badCount r Q positive start width := by
    rcases Nat.eq_zero_or_pos (SpectralIndexing.badCount r Q positive start width) with h | h
    · have h1 := ρ.isLt
      have h2 : copies * SpectralIndexing.badCount r Q positive start width = 0 := by
        rw [h, Nat.mul_zero]
      omega
    · exact h
  have hord : (ρ : ℕ) % SpectralIndexing.badCount r Q positive start width <
      SpectralIndexing.badCount r Q positive start width := Nat.mod_lt _ hbc
  unfold mcN WGroupedAccessorEvaluation.measurementCoefficient
  have hsel : selMaskN r Q positive start width
      ((ρ : ℕ) % SpectralIndexing.badCount r Q positive start width) =
      SpectralIndexing.selectedMask r Q positive start width
        ((ρ : ℕ) % SpectralIndexing.badCount r Q positive start width) := by
    rw [show (ρ : ℕ) % SpectralIndexing.badCount r Q positive start width =
      (⟨_, hord⟩ : Fin _).val from rfl, selectedMask_eq_sum positive]
    rfl
  rw [hsel, ← rowAt_snd positive, hLB inc]
  have e1 : ((ρ : ℕ) / SpectralIndexing.badCount r Q positive start width = CP inc.1 inc.2) ↔
      (SpectralIndexing.rowAt r Q positive copies start width ρ).1 = copyOf inc := by
    rw [hCP, ← rowAt_fst positive, Fin.val_inj]
  by_cases h : (SpectralIndexing.rowAt r Q positive copies start width ρ).1 = copyOf inc
  · rw [if_pos (e1.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (e1.mp h')), if_neg h]

/-! ### The row number -/

/-- The measurement row number of `(g, ρ)`: `ρ + copies · badCount · g`. -/
def rowNumT (cbT : Term) (_nd g ρ : Term) : Term := add ρ (mul cbT g)

theorem implN2_rowNumT {cbT nd : Term} {env : List ℕ} (hcb : StableAt w cbT env) :
    ImplN2 w env (rowNumT cbT nd) (fun g ρ => ρ + cbT.denote w env * g) := by
  intro pre a b ha hb
  refine ⟨?_, hb.add ((hcb.extend pre).mul ha)⟩
  simp [rowNumT, hcb pre]

/-! ### The local coefficient -/

section LC

variable (pT rT QT sP sN widthT mT : Term) (arity : Term → Term)
  (cpT lbT varT : Term → Term → Term)

/-- The local coefficient of incidence `(e, i)` and variable `v` at node `nd`. -/
def lcT (nd e i v : Term) : Term :=
  incSumModT pT mT arity fun e' i' =>
    ite (mul (eqT (cpT e' i') (cpT e i)) (eqT (varT e' i') v))
      (mod (mul (entryT pT rT QT sP sN widthT (lbT e i) (lbT e' i'))
        (mismatchT pT rT QT (lbT e i) (lbT e' i') (add nd (const 1)))) pT) (const 0)

end LC

/-- The local coefficient on numbers, at node `ν`. -/
noncomputable def lcN {n : ℕ} (formula : WeightedSystem.System n) (start : ℤ) (width : ℕ)
    (CP LB V : ℕ → ℕ → ℕ) (ν e i v : ℕ) : ZMod P :=
  ∑ inc : WeightedSystem.Incidence formula,
    if CP inc.1 inc.2 = CP e i ∧ V inc.1 inc.2 = v then
      DeformationEvaluation.entry P positive start width
          (SpectralIndexing.label r Q positive (LB e i))
          (SpectralIndexing.label r Q positive (LB inc.1 inc.2)) *
        TensorEvaluation.mismatchProduct (nodeValues (P := P) Q)
          (SpectralIndexing.label r Q positive (LB e i))
          (SpectralIndexing.label r Q positive (LB inc.1 inc.2)) ((ν + 1 : ℕ) : ZMod P)
    else 0

theorem implZ3_lcT (hP3 : 2 < P) {n : ℕ} (formula : WeightedSystem.System n)
    {pT rT QT sP sN widthT mT : Term} {arity : Term → Term} {cpT lbT varT : Term → Term → Term}
    {env : List ℕ} (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hr : StableAt w rT env) (hrv : rT.denote w env = r) (hQ : StableAt w QT env)
    (hQv : QT.denote w env = Q) (hsP : StableAt w sP env) (hsN : StableAt w sN env)
    (hwd : StableAt w widthT env) (hm : StableAt w mT env)
    (hmv : mT.denote w env = formula.constraints.length)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    {CP LB V : ℕ → ℕ → ℕ} (iCP : ImplN2 w env cpT CP) (iLB : ImplN2 w env lbT LB)
    (iV : ImplN2 w env varT V) {nd : Term} (hnd : StableAt w nd env) :
    ImplZ3 w env P (lcT pT rT QT sP sN widthT mT arity cpT lbT varT nd)
      (lcN (P := P) (Q := Q) positive formula ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)
        CP LB V (nd.denote w env)) := by
  intro pre a b c ha hb hc
  unfold lcT lcN
  refine cast_incSumModT formula (hp.extend pre) (by rw [hp pre, hpv]) (by rw [hm pre, hmv])
    (iAR.extend pre) hAR (fun e' i' =>
      if CP e' i' = CP (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) ∧
          V e' i' = c.denote w (pre ++ env) then
        DeformationEvaluation.entry P positive ((sP.denote w env : ℤ) - sN.denote w env)
            (widthT.denote w env)
            (SpectralIndexing.label r Q positive (LB (a.denote w (pre ++ env)) (b.denote w (pre ++ env))))
            (SpectralIndexing.label r Q positive (LB e' i')) *
          TensorEvaluation.mismatchProduct (nodeValues (P := P) Q)
            (SpectralIndexing.label r Q positive (LB (a.denote w (pre ++ env)) (b.denote w (pre ++ env))))
            (SpectralIndexing.label r Q positive (LB e' i')) ((nd.denote w env + 1 : ℕ) : ZMod P)
      else 0) ?_
  intro pre2 e' i' he hi _ _
  have hp2 : StableAt w pT (pre2 ++ (pre ++ env)) := (hp.extend pre).extend pre2
  have hpv2 : pT.denote w (pre2 ++ (pre ++ env)) = P := by rw [(hp.extend pre) pre2, hp pre, hpv]
  have hr2 : StableAt w rT (pre2 ++ (pre ++ env)) := (hr.extend pre).extend pre2
  have hrv2 : rT.denote w (pre2 ++ (pre ++ env)) = r := by rw [(hr.extend pre) pre2, hr pre, hrv]
  have hQ2 : StableAt w QT (pre2 ++ (pre ++ env)) := (hQ.extend pre).extend pre2
  have hQv2 : QT.denote w (pre2 ++ (pre ++ env)) = Q := by rw [(hQ.extend pre) pre2, hQ pre, hQv]
  have hsP2 : StableAt w sP (pre2 ++ (pre ++ env)) := (hsP.extend pre).extend pre2
  have hsN2 : StableAt w sN (pre2 ++ (pre ++ env)) := (hsN.extend pre).extend pre2
  have hwd2 : StableAt w widthT (pre2 ++ (pre ++ env)) := (hwd.extend pre).extend pre2
  have ha2 : StableAt w a (pre2 ++ (pre ++ env)) := ha.extend pre2
  have hb2 : StableAt w b (pre2 ++ (pre ++ env)) := hb.extend pre2
  have hnd2 : StableAt w (add nd (const 1)) (pre2 ++ (pre ++ env)) :=
    ((hnd.extend pre).extend pre2).add (stableAt_const _ _)
  obtain ⟨cp1, -⟩ := (iCP.extend pre) pre2 e' i' he hi
  obtain ⟨cp2, -⟩ := (iCP.extend pre) pre2 a b ha2 hb2
  obtain ⟨v1, -⟩ := (iV.extend pre) pre2 e' i' he hi
  obtain ⟨lb1, lbs1⟩ := (iLB.extend pre) pre2 e' i' he hi
  obtain ⟨lb2, lbs2⟩ := (iLB.extend pre) pre2 a b ha2 hb2
  rw [denote_ite, denote_mul, denote_eqT, denote_eqT, cp1, cp2, v1, ha pre2, hb pre2, hc pre2]
  by_cases h : CP (e'.denote w (pre2 ++ (pre ++ env))) (i'.denote w (pre2 ++ (pre ++ env))) =
      CP (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) ∧
      V (e'.denote w (pre2 ++ (pre ++ env))) (i'.denote w (pre2 ++ (pre ++ env))) =
        c.denote w (pre ++ env)
  · rw [if_pos ((pos_mul_ind_iff _ _).mpr h), if_pos h, denote_mod, hpv2, ZMod.natCast_mod,
      denote_mul, Nat.cast_mul,
      cast_entryT hP3 positive hp2 hpv2 hr2 hrv2 hQ2 hQv2 hsP2 hsN2 hwd2 lbs2 lbs1,
      cast_mismatchT positive hP3 hp2 hpv2 hr2 hrv2 hQv2 lbs2 lbs1 hnd2,
      lb1, lb2, ha pre2, hb pre2, (hsP.extend pre) pre2, (hsN.extend pre) pre2,
      (hwd.extend pre) pre2, hsP pre, hsN pre, hwd pre, denote_add, denote_const,
      (hnd.extend pre) pre2, hnd pre]
  · rw [if_neg (fun h' => h ((pos_mul_ind_iff _ _).mp h')), if_neg h]
    simp

/-- **The local coefficient accessor** agrees with the spec. -/
theorem lcN_spec {n copies : ℕ} (formula : WeightedSystem.System n) (start : ℤ) (width : ℕ)
    (copyOf : WeightedSystem.Incidence formula → Fin copies)
    (labelOf : WeightedSystem.Incidence formula → TensorEvaluation.Label r Q) (CP LB V : ℕ → ℕ → ℕ)
    (hCP : ∀ inc : WeightedSystem.Incidence formula, CP inc.1 inc.2 = (copyOf inc).val)
    (hLB : ∀ inc : WeightedSystem.Incidence formula,
      labelOf inc = SpectralIndexing.label r Q positive (LB inc.1 inc.2))
    (hV : ∀ inc : WeightedSystem.Incidence formula,
      V inc.1 inc.2 = (WIncidenceEvaluation.variableOf formula inc).val)
    (ν : Fin Q) (inc : WeightedSystem.Incidence formula) (v : Fin n) :
    lcN (P := P) (Q := Q) positive formula start width CP LB V ν inc.1 inc.2 v =
      WGroupedAccessorEvaluation.localCoefficient P positive formula copyOf labelOf
        (nodeValues (P := P) Q) start width ν inc v := by
  unfold lcN WGroupedAccessorEvaluation.localCoefficient WGroupedAccessorEvaluation.variableSum
  rw [WIncidenceEvaluation.scanIncidences_correct, add_zero]
  refine Finset.sum_congr rfl fun other _ => ?_
  have e1 : (CP other.1 other.2 = CP inc.1 inc.2) ↔ copyOf other = copyOf inc := by
    rw [hCP, hCP, Fin.val_inj]
  have e2 : (V other.1 other.2 = v.val) ↔ WIncidenceEvaluation.variableOf formula other = v := by
    rw [hV, Fin.val_inj]
  rw [hLB inc, hLB other]
  by_cases h : copyOf other = copyOf inc ∧ WIncidenceEvaluation.variableOf formula other = v
  · rw [if_pos ⟨e1.mpr h.1, e2.mpr h.2⟩, if_pos h]
    rfl
  · rw [if_neg (fun h' => h ⟨e1.mp h'.1, e2.mp h'.2⟩), if_neg h]

end NtimeDspace.ProgTerm
