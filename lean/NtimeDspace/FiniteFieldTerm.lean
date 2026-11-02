import NtimeDspace.IncScanTerm

/-!
# The coefficient-evaluation accessor as a term

`evalCT e i v x` computes `WIncidenceEvaluation.finiteField` at incidence
`(e, i)`, variable `v` and point `x`: the sum, over incidences in the same copy
carrying `v`, of the deformation coefficient of the two labels. It is the
`evalC` accessor of the counter term (`implZ4_evalCT`, `evalCT_spec`).
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

section Def

variable (pT rT QT sP sN widthT mT : Term) (arity : Term → Term)
  (cpT lbT varT : Term → Term → Term)

/-- The coefficient-evaluation accessor. -/
def evalCT (e i v x : Term) : Term :=
  incSumModT pT mT arity fun e' i' =>
    ite (mul (eqT (cpT e' i') (cpT e i)) (eqT (varT e' i') v))
      (coefficientT pT rT QT sP sN widthT (lbT e i) (lbT e' i') x) (const 0)

end Def

theorem pos_mul_ind_iff (p q : Prop) [Decidable p] [Decidable q] :
    (0 < (if p then 1 else 0) * (if q then 1 else 0)) ↔ p ∧ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

variable {n P r Q copies : ℕ} [Fact P.Prime]

/-- The value of the accessor on numbers. -/
noncomputable def evalCN (formula : WeightedSystem.System n) (positive : 0 < r) (start : ℤ)
    (width : ℕ) (CP LB V : ℕ → ℕ → ℕ) (e i v x : ℕ) : ZMod P :=
  ∑ inc : WeightedSystem.Incidence formula,
    if CP inc.1 inc.2 = CP e i ∧ V inc.1 inc.2 = v then
      DeformationEvaluation.coefficient P positive (nodeValues (P := P) Q) start width
        (SpectralIndexing.label r Q positive (LB e i))
        (SpectralIndexing.label r Q positive (LB inc.1 inc.2)) (x : ZMod P)
    else 0

theorem implZ4_evalCT (hP3 : 2 < P) (positive : 0 < r) (formula : WeightedSystem.System n)
    {pT rT QT sP sN widthT mT : Term} {arity : Term → Term} {cpT lbT varT : Term → Term → Term}
    {env : List ℕ} (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hr : StableAt w rT env) (hrv : rT.denote w env = r) (hQ : StableAt w QT env)
    (hQv : QT.denote w env = Q) (hsP : StableAt w sP env) (hsN : StableAt w sN env)
    (hwd : StableAt w widthT env) (hm : StableAt w mT env)
    (hmv : mT.denote w env = formula.constraints.length)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    {CP LB V : ℕ → ℕ → ℕ} (iCP : ImplN2 w env cpT CP) (iLB : ImplN2 w env lbT LB)
    (iV : ImplN2 w env varT V) :
    ImplZ4 w env P (evalCT pT rT QT sP sN widthT mT arity cpT lbT varT)
      (evalCN (Q := Q) formula positive ((sP.denote w env : ℤ) - sN.denote w env)
        (widthT.denote w env) CP LB V) := by
  intro pre a b c d ha hb hc hd
  unfold evalCT evalCN
  refine cast_incSumModT formula (hp.extend pre) (by rw [hp pre, hpv]) (by rw [hm pre, hmv])
    (iAR.extend pre) hAR (fun e' i' =>
      if CP e' i' = CP (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) ∧
          V e' i' = c.denote w (pre ++ env) then
        DeformationEvaluation.coefficient P positive (nodeValues (P := P) Q)
          ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)
          (SpectralIndexing.label r Q positive (LB (a.denote w (pre ++ env)) (b.denote w (pre ++ env))))
          (SpectralIndexing.label r Q positive (LB e' i')) (d.denote w (pre ++ env) : ZMod P)
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
  have hc2 : StableAt w c (pre2 ++ (pre ++ env)) := hc.extend pre2
  have hd2 : StableAt w d (pre2 ++ (pre ++ env)) := hd.extend pre2
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
  · rw [if_pos ((pos_mul_ind_iff _ _).mpr h), if_pos h,
      cast_coefficientT hP3 positive hp2 hpv2 hr2 hrv2 hQ2 hQv2 hsP2 hsN2 hwd2 lbs2 lbs1 hd2,
      lb1, lb2, ha pre2, hb pre2, hd pre2, (hsP.extend pre) pre2, (hsN.extend pre) pre2,
      (hwd.extend pre) pre2, hsP pre, hsN pre, hwd pre]
  · rw [if_neg (fun h' => h ((pos_mul_ind_iff _ _).mp h')), if_neg h]
    simp

/-- **The accessor computes `finiteField`** at every incidence and variable. -/
theorem evalCN_spec (formula : WeightedSystem.System n) (positive : 0 < r) (start : ℤ)
    (width : ℕ) (copyOf : WeightedSystem.Incidence formula → Fin copies)
    (labelOf : WeightedSystem.Incidence formula → TensorEvaluation.Label r Q) (CP LB V : ℕ → ℕ → ℕ)
    (hCP : ∀ inc : WeightedSystem.Incidence formula, CP inc.1 inc.2 = (copyOf inc).val)
    (hLB : ∀ inc : WeightedSystem.Incidence formula,
      labelOf inc = SpectralIndexing.label r Q positive (LB inc.1 inc.2))
    (hV : ∀ inc : WeightedSystem.Incidence formula,
      V inc.1 inc.2 = (WIncidenceEvaluation.variableOf formula inc).val)
    (inc : WeightedSystem.Incidence formula) (v : Fin n) (x : ℕ) :
    evalCN (P := P) (Q := Q) formula positive start width CP LB V inc.1 inc.2 v x =
      WIncidenceEvaluation.finiteField P positive formula copyOf labelOf (nodeValues (P := P) Q)
        start width inc v (x : ZMod P) := by
  unfold evalCN WIncidenceEvaluation.finiteField WIncidenceEvaluation.evaluate
  rw [WIncidenceEvaluation.coefficientValue_eq_sum]
  refine Finset.sum_congr rfl fun other _ => ?_
  have e1 : (CP other.1 other.2 = CP inc.1 inc.2) ↔ copyOf other = copyOf inc := by
    rw [hCP, hCP, Fin.val_inj]
  have e2 : (V other.1 other.2 = v.val) ↔ WIncidenceEvaluation.variableOf formula other = v := by
    rw [hV, Fin.val_inj]
  rw [hLB inc, hLB other]
  by_cases h : copyOf other = copyOf inc ∧ WIncidenceEvaluation.variableOf formula other = v
  · rw [if_pos ⟨e1.mpr h.1, e2.mpr h.2⟩, if_pos h]
  · rw [if_neg (fun h' => h ⟨e1.mp h'.1, e2.mp h'.2⟩), if_neg h]

end NtimeDspace.ProgTerm
