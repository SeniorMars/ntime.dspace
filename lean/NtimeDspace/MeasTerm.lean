import NtimeDspace.SignTerm

/-!
# The integer measurement accessor

The measurement of row `ρ` at variable `v` is a sum over incidences in the
row's copy carrying `v` of the integer tensor sign of the row's bad label and
the incidence's label. `measPosT` and `measNegT` compute its positive and
negative parts exactly (`measurement_eq_parts`).
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

theorem denote_incSumT {n : ℕ} (formula : WeightedSystem.System n) {mT : Term}
    {arity : Term → Term} {body : Term → Term → Term} {env : List ℕ}
    (hmv : mT.denote w env = formula.constraints.length)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    (F : ℕ → ℕ → ℕ)
    (hbody : ∀ (pre : List ℕ) (e i : Term), StableAt w e (pre ++ env) → StableAt w i (pre ++ env) →
      e.denote w (pre ++ env) < formula.constraints.length →
      i.denote w (pre ++ env) < AR (e.denote w (pre ++ env)) →
      (body e i).denote w (pre ++ env) = F (e.denote w (pre ++ env)) (i.denote w (pre ++ env))) :
    (incSumT mT arity body).denote w env = ∑ inc : WeightedSystem.Incidence formula, F inc.1 inc.2 := by
  rw [← sum_incidence_eq formula AR hAR F]
  unfold incSumT
  rw [denote_sumT_lt mT _ env (fun e => ∑ i ∈ Finset.range (AR e), F e i), hmv]
  intro acc e he
  rw [hmv] at he
  have hes : StableAt w (lvl env.length) ([acc, e] ++ env) := stableAt_lvl (by simp)
  have hev : (lvl env.length).denote w (acc :: e :: env) = e := denote_lvl_index env acc e
  obtain ⟨har, -⟩ := iAR [acc, e] _ hes
  simp only [List.cons_append, List.nil_append] at har
  rw [denote_sumT_lt _ _ (acc :: e :: env) (fun i => F e i), har, hev]
  intro acc' i hi
  rw [har, hev] at hi
  have hes' : StableAt w (lvl env.length) ([acc', i, acc, e] ++ env) := hes.extend [acc', i]
  have his : StableAt w (lvl (env.length + 2)) ([acc', i, acc, e] ++ env) := stableAt_lvl (by simp)
  have hev' : (lvl env.length).denote w (acc' :: i :: acc :: e :: env) = e := by
    rw [denote_lvl]; simp only [List.length_cons]
    rw [show env.length + 1 + 1 + 1 + 1 - env.length - 1 = 3 by omega]; rfl
  have hiv : (lvl (env.length + 2)).denote w (acc' :: i :: acc :: e :: env) = i := by
    rw [denote_lvl]; simp only [List.length_cons]
    rw [show env.length + 1 + 1 + 1 + 1 - (env.length + 2) - 1 = 1 by omega]; rfl
  have hb := hbody [acc', i, acc, e] (lvl env.length) (lvl (env.length + 2)) hes' his
    (by simpa [hev'] using he) (by simpa [hev', hiv] using hi)
  simp only [List.cons_append, List.nil_append, hev', hiv] at hb
  have hlen : (acc :: e :: env).length = env.length + 2 := by simp
  rw [hlen]
  exact hb

variable {r Q : ℕ} (positive : 0 < r)

open Classical in
/-- The positive (`par = 0`) or negative (`par = 1`) sign indicator of two labels. -/
noncomputable def signPart (par : ℕ) (U W : TensorEvaluation.Label r Q) : ℕ :=
  if (∀ node, pairNZ (U node) (W node)) ∧
      (Finset.univ.filter fun node => pairNeg (U node) (W node)).card % 2 = par then 1 else 0

section Def

variable (rT QT sP sN widthT mT : Term) (arity : Term → Term) (cpT lbT varT : Term → Term → Term)

/-- A part of the measurement of row `ρ` at variable `v`, with sign term `sgn`. -/
def measSignT (sgn : Term → Term → Term) (_nd _g ρ v : Term) : Term :=
  incSumT mT arity fun e' i' =>
    mul (mul (eqT (cpT e' i') (div ρ (badCountT rT QT sP sN widthT))) (eqT (varT e' i') v))
      (sgn (selMaskT rT QT sP sN widthT (mod ρ (badCountT rT QT sP sN widthT))) (lbT e' i'))

end Def

/-- A part of the measurement on numbers. -/
noncomputable def measSignN {n : ℕ} (formula : WeightedSystem.System n) (start : ℤ) (width : ℕ)
    (CP LB V : ℕ → ℕ → ℕ) (par ρ v : ℕ) : ℕ :=
  ∑ inc : WeightedSystem.Incidence formula,
    if CP inc.1 inc.2 = ρ / SpectralIndexing.badCount r Q positive start width ∧ V inc.1 inc.2 = v
    then signPart par (SpectralIndexing.label r Q positive (selMaskN r Q positive start width
        (ρ % SpectralIndexing.badCount r Q positive start width)))
      (SpectralIndexing.label r Q positive (LB inc.1 inc.2))
    else 0

theorem pos_signPos {rT QT u w' : Term} {env : List ℕ} (hr : StableAt w rT env)
    (hrv : rT.denote w env = r) (hQv : QT.denote w env = Q) (hu : StableAt w u env)
    (hw : StableAt w w' env) :
    (signPosT rT QT u w').denote w env = signPart 0 (SpectralIndexing.label r Q positive (u.denote w env))
      (SpectralIndexing.label r Q positive (w'.denote w env)) := by
  rw [(denote_signT_parts positive hr hrv hQv hu hw).1, signPart]

theorem neg_signNeg {rT QT u w' : Term} {env : List ℕ} (hr : StableAt w rT env)
    (hrv : rT.denote w env = r) (hQv : QT.denote w env = Q) (hu : StableAt w u env)
    (hw : StableAt w w' env) :
    (signNegT rT QT u w').denote w env = signPart 1 (SpectralIndexing.label r Q positive (u.denote w env))
      (SpectralIndexing.label r Q positive (w'.denote w env)) := by
  rw [(denote_signT_parts positive hr hrv hQv hu hw).2, signPart]

theorem implN3_measSignT {n : ℕ} (formula : WeightedSystem.System n) (par : ℕ)
    {rT QT sP sN widthT mT : Term} {arity : Term → Term} {cpT lbT varT : Term → Term → Term}
    {sgn : Term → Term → Term} {env : List ℕ}
    (hsgn : ∀ (E : List ℕ) (u w' : Term), StableAt w rT E → rT.denote w E = r →
      QT.denote w E = Q → StableAt w u E → StableAt w w' E →
      (sgn u w').denote w E = signPart par (SpectralIndexing.label r Q positive (u.denote w E))
        (SpectralIndexing.label r Q positive (w'.denote w E)))
    (hr : StableAt w rT env) (hrv : rT.denote w env = r) (hQ : StableAt w QT env)
    (hQv : QT.denote w env = Q) (hsP : StableAt w sP env) (hsN : StableAt w sN env)
    (hwd : StableAt w widthT env) (hm : StableAt w mT env)
    (hmv : mT.denote w env = formula.constraints.length)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    {CP LB V : ℕ → ℕ → ℕ} (iCP : ImplN2 w env cpT CP) (iLB : ImplN2 w env lbT LB)
    (iV : ImplN2 w env varT V) (nd : Term) :
    ImplN3 w env (measSignT rT QT sP sN widthT mT arity cpT lbT varT sgn nd)
      (fun _g ρ v => measSignN (Q := Q) positive formula ((sP.denote w env : ℤ) - sN.denote w env)
        (widthT.denote w env) CP LB V par ρ v) := by
  have key : ∀ (pre : List ℕ) (a b c : Term), StableAt w a (pre ++ env) →
      StableAt w b (pre ++ env) → StableAt w c (pre ++ env) →
      (measSignT rT QT sP sN widthT mT arity cpT lbT varT sgn nd a b c).denote w (pre ++ env) =
        measSignN (Q := Q) positive formula ((sP.denote w env : ℤ) - sN.denote w env)
          (widthT.denote w env) CP LB V par (b.denote w (pre ++ env)) (c.denote w (pre ++ env)) := by
    intro pre a b c ha hb hc
    unfold measSignT measSignN
    refine denote_incSumT formula (by rw [hm pre, hmv]) (iAR.extend pre) hAR (fun e' i' =>
      if CP e' i' = b.denote w (pre ++ env) / SpectralIndexing.badCount r Q positive
            ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env) ∧
          V e' i' = c.denote w (pre ++ env) then
        signPart par (SpectralIndexing.label r Q positive (selMaskN r Q positive
            ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)
            (b.denote w (pre ++ env) % SpectralIndexing.badCount r Q positive
              ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env))))
          (SpectralIndexing.label r Q positive (LB e' i'))
      else 0) ?_
    intro pre2 e' i' he hi _ _
    have hr2 : StableAt w rT (pre2 ++ (pre ++ env)) := (hr.extend pre).extend pre2
    have hrv2 : rT.denote w (pre2 ++ (pre ++ env)) = r := by rw [(hr.extend pre) pre2, hr pre, hrv]
    have hQ2 : StableAt w QT (pre2 ++ (pre ++ env)) := (hQ.extend pre).extend pre2
    have hQv2 : QT.denote w (pre2 ++ (pre ++ env)) = Q := by rw [(hQ.extend pre) pre2, hQ pre, hQv]
    have hsP2 : StableAt w sP (pre2 ++ (pre ++ env)) := (hsP.extend pre).extend pre2
    have hsN2 : StableAt w sN (pre2 ++ (pre ++ env)) := (hsN.extend pre).extend pre2
    have hwd2 : StableAt w widthT (pre2 ++ (pre ++ env)) := (hwd.extend pre).extend pre2
    have hbc := denote_badCountT positive hr2 hrv2 hQ2 hQv2 hsP2 hsN2 hwd2
    have hbcs := StableAt.badCountT positive hr2 hrv2 hQ2 hQv2 hsP2 hsN2 hwd2
    have hb2 : StableAt w b (pre2 ++ (pre ++ env)) := hb.extend pre2
    have hc2 : StableAt w c (pre2 ++ (pre ++ env)) := hc.extend pre2
    have hord : StableAt w (mod b (badCountT rT QT sP sN widthT)) (pre2 ++ (pre ++ env)) := hb2.mod hbcs
    have hsel := StableAt.selMaskT positive hr2 hrv2 hQ2 hQv2 hsP2 hsN2 hwd2 hord
    obtain ⟨cp1, -⟩ := (iCP.extend pre) pre2 e' i' he hi
    obtain ⟨v1, -⟩ := (iV.extend pre) pre2 e' i' he hi
    obtain ⟨lb1, lbs1⟩ := (iLB.extend pre) pre2 e' i' he hi
    rw [denote_mul, denote_mul, denote_eqT, denote_eqT, denote_div, hbc, cp1, v1,
      hsgn (pre2 ++ (pre ++ env)) _ _ hr2 hrv2 hQv2 hsel lbs1, lb1,
      denote_selMaskT_sum positive hr2 hrv2 hQ2 hQv2 hsP2 hsN2 hwd2 hord, denote_mod, hbc,
      hb pre2, hc pre2, (hsP.extend pre) pre2, (hsN.extend pre) pre2, (hwd.extend pre) pre2,
      hsP pre, hsN pre, hwd pre]
    simp only [selMaskN]
    split_ifs <;> simp_all
  intro pre a b c ha hb hc
  refine ⟨key pre a b c ha hb hc, fun extra => ?_⟩
  rw [← List.append_assoc, key _ a b c (by rw [List.append_assoc]; exact ha.extend extra)
    (by rw [List.append_assoc]; exact hb.extend extra) (by rw [List.append_assoc]; exact hc.extend extra),
    List.append_assoc, hb extra, hc extra, key pre a b c ha hb hc]

theorem integerTensorSign_parts (U W : TensorEvaluation.Label r Q) :
    WGroupedAccessorEvaluation.integerTensorSign U W = (signPart 1 U W : ℤ) * 0 + signPart 0 U W -
      signPart 1 U W := by
  rw [integerTensorSign_split, mul_zero, zero_add, signPart, signPart]

/-- **The measurement is the positive part minus the negative part.** -/
theorem measurement_eq_parts {n copies : ℕ} (formula : WeightedSystem.System n) (start : ℤ)
    (width : ℕ) (copyOf : WeightedSystem.Incidence formula → Fin copies)
    (labelOf : WeightedSystem.Incidence formula → TensorEvaluation.Label r Q) (CP LB V : ℕ → ℕ → ℕ)
    (hCP : ∀ inc : WeightedSystem.Incidence formula, CP inc.1 inc.2 = (copyOf inc).val)
    (hLB : ∀ inc : WeightedSystem.Incidence formula,
      labelOf inc = SpectralIndexing.label r Q positive (LB inc.1 inc.2))
    (hV : ∀ inc : WeightedSystem.Incidence formula,
      V inc.1 inc.2 = (WIncidenceEvaluation.variableOf formula inc).val)
    (groupOf : Fin n → Fin r) (g : Fin r)
    (ρ : Fin (copies * SpectralIndexing.badCount r Q positive start width))
    (v : GroupedDeformation.LocalVariable groupOf g) :
    WGroupedAccessorEvaluation.measurement formula copyOf labelOf groupOf start width g
        (SpectralIndexing.rowAt r Q positive copies start width ρ) v =
      (measSignN (Q := Q) positive formula start width CP LB V 0 ρ v.val.val : ℤ) -
        measSignN (Q := Q) positive formula start width CP LB V 1 ρ v.val.val := by
  have hbc : 0 < SpectralIndexing.badCount r Q positive start width := by
    rcases Nat.eq_zero_or_pos (SpectralIndexing.badCount r Q positive start width) with h | h
    · have h1 := ρ.isLt
      have h2 : copies * SpectralIndexing.badCount r Q positive start width = 0 := by
        rw [h, Nat.mul_zero]
      omega
    · exact h
  have hord : (ρ : ℕ) % SpectralIndexing.badCount r Q positive start width <
      SpectralIndexing.badCount r Q positive start width := Nat.mod_lt _ hbc
  have hsel : selMaskN r Q positive start width
      ((ρ : ℕ) % SpectralIndexing.badCount r Q positive start width) =
      SpectralIndexing.selectedMask r Q positive start width
        ((ρ : ℕ) % SpectralIndexing.badCount r Q positive start width) := by
    rw [show (ρ : ℕ) % SpectralIndexing.badCount r Q positive start width =
      (⟨_, hord⟩ : Fin _).val from rfl, selectedMask_eq_sum positive]
    rfl
  unfold WGroupedAccessorEvaluation.measurement WGroupedAccessorEvaluation.variableSum measSignN
  rw [WIncidenceEvaluation.scanIncidences_correct, add_zero, Nat.cast_sum, Nat.cast_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun inc _ => ?_
  have e1 : (CP inc.1 inc.2 = (ρ : ℕ) / SpectralIndexing.badCount r Q positive start width) ↔
      copyOf inc = (SpectralIndexing.rowAt r Q positive copies start width ρ).1 := by
    rw [hCP, ← rowAt_fst positive, Fin.val_inj]
  have e2 : (V inc.1 inc.2 = v.val.val) ↔ WIncidenceEvaluation.variableOf formula inc = v.val := by
    rw [hV, Fin.val_inj]
  by_cases h : copyOf inc = (SpectralIndexing.rowAt r Q positive copies start width ρ).1 ∧
      WIncidenceEvaluation.variableOf formula inc = v.val
  · rw [if_pos h, if_pos ⟨e1.mpr h.1, e2.mpr h.2⟩, if_pos ⟨e1.mpr h.1, e2.mpr h.2⟩,
      integerTensorSign_parts, rowAt_snd positive, hLB inc, hsel]
    ring
  · rw [if_neg h, if_neg (fun h' => h ⟨e1.mp h'.1, e2.mp h'.2⟩),
      if_neg (fun h' => h ⟨e1.mp h'.1, e2.mp h'.2⟩)]
    simp

end NtimeDspace.ProgTerm
