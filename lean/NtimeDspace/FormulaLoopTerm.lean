import NtimeDspace.InnerLoopSpec
import NtimeDspace.WGroupedFormulaLoop

/-!
# The grouped formula loop as a term

`formulaLoopT` mirrors `WGroupedFormulaLoop.evaluate`: a modular sum over the
measurement tuples `T < (2D+1)^width`, of the modular product over the groups of
`sumGroupT`. The target of group `g` and row `ρ` is the digit of `T` at the row
number of `(g, ρ)`, minus `D`.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- `(x - D) mod p` for a digit `x ≤ 2D` and `D < p`, as a residue. -/
def shiftT (p D x : Term) : Term := mod (sub (add x p) (mod D p)) p

theorem shiftT_cast (p D x : Term) (env : List ℕ) (P : ℕ) (hP0 : 0 < P)
    (hpv : p.denote w env = P) :
    ((shiftT p D x).denote w env : ZMod P) =
      (x.denote w env : ZMod P) - (D.denote w env : ZMod P) := by
  have hle : D.denote w env % P ≤ x.denote w env + P :=
    (Nat.mod_lt _ hP0).le.trans (Nat.le_add_left _ _)
  simp only [shiftT, denote_mod, denote_sub, denote_add, hpv, ZMod.natCast_mod]
  rw [Nat.cast_sub hle, ZMod.natCast_mod]
  push_cast
  simp

/-- The measurement part of incidence `(e, i)` under tuple `T`. -/
def measPartT (p groups rows : Term) (measCoef : Term → Term → Term → Term → Term)
    (rowNum : Term → Term → Term) (radix D T e i : Term) : Term :=
  Term.sumMod p groups fun g => Term.sumMod p rows fun ρ =>
    mod (mul (measCoef e i g ρ) (shiftT p D (digitT radix T (rowNum g ρ)))) p

/-- The grouped formula loop. -/
def formulaLoopT (p nT groups rows width D m : Term) (gOf sBit cGroup arity : Term → Term)
    (rowNum : Term → Term → Term) (posAll negAll : Term → Term → Term → Term)
    (weight : Term → Term → Term) (localC : Term → Term → Term → Term)
    (measCoef : Term → Term → Term → Term → Term) (corr : Term → Term → Term) : Term :=
  Term.sumMod p (powT (add (mul (const 2) D) (const 1)) width) fun T =>
    Term.prodMod p groups fun g =>
      sumGroupT p nT gOf g sBit rows (posAll g) (negAll g)
        (fun ρ => digitT (add (mul (const 2) D) (const 1)) T (rowNum g ρ)) D m cGroup arity weight
        localC (measPartT p groups rows measCoef rowNum (add (mul (const 2) D) (const 1)) D T) corr

/-- A three-argument term function implements `F` exactly, with stable results. -/
def ImplN3 (w : List Bool) (env : List ℕ) (f : Term → Term → Term → Term) (F : ℕ → ℕ → ℕ → ℕ) :
    Prop :=
  ∀ (pre : List ℕ) (a b c : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
    StableAt w c (pre ++ env) →
    (f a b c).denote w (pre ++ env) =
        F (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) (c.denote w (pre ++ env)) ∧
      StableAt w (f a b c) (pre ++ env)

/-- A four-argument term function implements `F` at the residue level. -/
def ImplZ4 (w : List Bool) (env : List ℕ) (P : ℕ) (f : Term → Term → Term → Term → Term)
    (F : ℕ → ℕ → ℕ → ℕ → ZMod P) : Prop :=
  ∀ (pre : List ℕ) (a b c d : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
    StableAt w c (pre ++ env) → StableAt w d (pre ++ env) →
    ((f a b c d).denote w (pre ++ env) : ZMod P) =
      F (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) (c.denote w (pre ++ env))
        (d.denote w (pre ++ env))

theorem ImplN3.extend {env : List ℕ} {f : Term → Term → Term → Term} {F : ℕ → ℕ → ℕ → ℕ}
    (h : ImplN3 w env f F) (pre : List ℕ) : ImplN3 w (pre ++ env) f F :=
  fun pre' a b c ha hb hc => by
    rw [← List.append_assoc] at ha hb hc ⊢; exact h (pre' ++ pre) a b c ha hb hc

theorem ImplN3.fix {env : List ℕ} {f : Term → Term → Term → Term} {F : ℕ → ℕ → ℕ → ℕ}
    (h : ImplN3 w env f F) (a : Term) (ha : StableAt w a env) :
    ImplN2 w env (f a) (F (a.denote w env)) :=
  fun pre b c hb hc => by
    have := h pre a b c (ha.extend pre) hb hc
    rw [ha pre] at this
    exact this

theorem ImplZ4.extend {env : List ℕ} {P : ℕ} {f : Term → Term → Term → Term → Term}
    {F : ℕ → ℕ → ℕ → ℕ → ZMod P} (h : ImplZ4 w env P f F) (pre : List ℕ) :
    ImplZ4 w (pre ++ env) P f F :=
  fun pre' a b c d ha hb hc hd => by
    rw [← List.append_assoc] at ha hb hc hd ⊢; exact h (pre' ++ pre) a b c d ha hb hc hd

theorem ImplN2.extend' {env : List ℕ} {f : Term → Term → Term} {F : ℕ → ℕ → ℕ}
    (h : ImplN2 w env f F) (pre : List ℕ) : ImplN2 w (pre ++ env) f F := h.extend pre

theorem measPartT_denote (p groups rows : Term) (measCoef : Term → Term → Term → Term → Term)
    (rowNum : Term → Term → Term) (radix D T e i : Term) (base : List ℕ) (P : ℕ) (hP0 : 0 < P)
    (MC : ℕ → ℕ → ℕ → ℕ → ZMod P) (RN : ℕ → ℕ → ℕ)
    (hMC : ImplZ4 w base P measCoef MC) (hRN : ImplN2 w base rowNum RN) (pre : List ℕ)
    (hp : StableAt w p (pre ++ base)) (hpv : p.denote w (pre ++ base) = P)
    (hgroups : StableAt w groups (pre ++ base)) (hrows : StableAt w rows (pre ++ base))
    (hradix : StableAt w radix (pre ++ base)) (hD : StableAt w D (pre ++ base))
    (hT : StableAt w T (pre ++ base)) (he : StableAt w e (pre ++ base))
    (hi : StableAt w i (pre ++ base)) :
    ((measPartT p groups rows measCoef rowNum radix D T e i).denote w (pre ++ base) : ZMod P) =
      ∑ g ∈ Finset.range (groups.denote w (pre ++ base)),
        ∑ ρ ∈ Finset.range (rows.denote w (pre ++ base)),
          MC (e.denote w (pre ++ base)) (i.denote w (pre ++ base)) g ρ *
            (((T.denote w (pre ++ base) / radix.denote w (pre ++ base) ^ RN g ρ %
              radix.denote w (pre ++ base) : ℕ) : ZMod P) - (D.denote w (pre ++ base) : ZMod P)) := by
  rw [measPartT, denote_sumModZ p groups _ (pre ++ base) P _ hp hpv (fun acc g _ => ?_)]
  have hpv1 : p.denote w (acc :: g :: (pre ++ base)) = P := by
    show p.denote w ([acc, g] ++ (pre ++ base)) = P; rw [hp, hpv]
  rw [denote_sumModZ p rows _ (acc :: g :: (pre ++ base)) P _ (hp.extend [acc, g]) hpv1
    (fun acc' ρ _ => ?_), hrows.cons₂]
  have hg2 : StableAt w (lvl (pre ++ base).length) ([acc', ρ, acc, g] ++ (pre ++ base)) :=
    (stableAt_index (pre ++ base) acc g).extend [acc', ρ]
  have hgv2 : (lvl (pre ++ base).length).denote w (acc' :: ρ :: acc :: g :: (pre ++ base)) = g := by
    rw [show acc' :: ρ :: acc :: g :: (pre ++ base) = [acc', ρ] ++ (acc :: g :: (pre ++ base))
      from rfl, (stableAt_index (w := w) (pre ++ base) acc g) [acc', ρ]]
    exact denote_lvl_index _ _ _
  have hρ2 : StableAt w (lvl (acc :: g :: (pre ++ base)).length)
      ([acc', ρ, acc, g] ++ (pre ++ base)) :=
    stableAt_index (acc :: g :: (pre ++ base)) acc' ρ
  have hρv2 : (lvl (acc :: g :: (pre ++ base)).length).denote w
      (acc' :: ρ :: acc :: g :: (pre ++ base)) = ρ := denote_lvl_index _ _ _
  have hpv2 : p.denote w (acc' :: ρ :: acc :: g :: (pre ++ base)) = P := by
    show p.denote w ([acc', ρ, acc, g] ++ (pre ++ base)) = P; rw [hp, hpv]
  have hmc := hMC ([acc', ρ, acc, g] ++ pre) e i _ _
    (by rw [List.append_assoc]; exact he.extend [acc', ρ, acc, g])
    (by rw [List.append_assoc]; exact hi.extend [acc', ρ, acc, g])
    (by rw [List.append_assoc]; exact hg2) (by rw [List.append_assoc]; exact hρ2)
  obtain ⟨hrn, -⟩ := hRN ([acc', ρ, acc, g] ++ pre) _ _ (by rw [List.append_assoc]; exact hg2)
    (by rw [List.append_assoc]; exact hρ2)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hmc hrn
  rw [hgv2, hρv2] at hmc hrn
  have hdig := digitT_denote radix T (rowNum (lvl (pre ++ base).length)
    (lvl (acc :: g :: (pre ++ base)).length)) (acc' :: ρ :: acc :: g :: (pre ++ base))
    (hradix.extend [acc', ρ, acc, g])
  simp only [denote_mod, denote_mul, ZMod.natCast_mod, Nat.cast_mul, hpv2]
  rw [hmc, shiftT_cast p D _ _ P hP0 hpv2, hdig, hrn]
  rw [show acc' :: ρ :: acc :: g :: (pre ++ base) = [acc', ρ, acc, g] ++ (pre ++ base) from rfl,
    he, hi, hT, hradix, hD]

/-- The digit accessor of a group under a tuple implements its digits. -/
theorem tdig_implN (radix T g : Term) (rowNum : Term → Term → Term) (env : List ℕ)
    (RN : ℕ → ℕ → ℕ) (iRN : ImplN2 w env rowNum RN) (hradix : StableAt w radix env)
    (hT : StableAt w T env) (hg : StableAt w g env) :
    ImplN w env (fun ρ => digitT radix T (rowNum g ρ)) (fun ρ =>
      T.denote w env / radix.denote w env ^ RN (g.denote w env) ρ % radix.denote w env) := by
  intro pre ρ hρ
  obtain ⟨hrn, hrns⟩ := iRN pre g ρ (hg.extend pre) hρ
  refine ⟨?_, (hradix.extend pre).digitT (hT.extend pre) hrns⟩
  rw [digitT_denote radix T _ _ (hradix.extend pre), hrn, hradix pre, hT pre, hg pre]

/-- The measurement part under a tuple implements its double sum. -/
theorem measPart_implZ2 (p groups rows : Term) (measCoef : Term → Term → Term → Term → Term)
    (rowNum : Term → Term → Term) (radix D T : Term) (base : List ℕ) (P : ℕ) (hP0 : 0 < P)
    (MC : ℕ → ℕ → ℕ → ℕ → ZMod P) (RN : ℕ → ℕ → ℕ)
    (iMC : ImplZ4 w base P measCoef MC) (iRN : ImplN2 w base rowNum RN) (env : List ℕ)
    (henv : ∃ pre, env = pre ++ base)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hgroups : StableAt w groups env) (hrows : StableAt w rows env)
    (hradix : StableAt w radix env) (hD : StableAt w D env) (hT : StableAt w T env) :
    ImplZ2 w env P (measPartT p groups rows measCoef rowNum radix D T) (fun e i =>
      ∑ g ∈ Finset.range (groups.denote w env), ∑ ρ ∈ Finset.range (rows.denote w env),
        MC e i g ρ * (((T.denote w env / radix.denote w env ^ RN g ρ % radix.denote w env : ℕ) :
          ZMod P) - (D.denote w env : ZMod P))) := by
  obtain ⟨pre0, rfl⟩ := henv
  intro pre e i he hi
  have := measPartT_denote p groups rows measCoef rowNum radix D T e i base P hP0 MC RN iMC iRN
    (pre ++ pre0) (by rw [List.append_assoc]; exact hp.extend pre)
    (by rw [List.append_assoc, hp pre]; exact hpv)
    (by rw [List.append_assoc]; exact hgroups.extend pre)
    (by rw [List.append_assoc]; exact hrows.extend pre)
    (by rw [List.append_assoc]; exact hradix.extend pre)
    (by rw [List.append_assoc]; exact hD.extend pre) (by rw [List.append_assoc]; exact hT.extend pre)
    (by rw [List.append_assoc]; exact he) (by rw [List.append_assoc]; exact hi)
  simp only [List.append_assoc] at this
  rw [this, hgroups pre, hrows pre, hT pre, hradix pre, hD pre]

open WGroupedAssignmentEvaluation in
/-- Inside the tuple loop, a group's term is the specification's group sum. -/
theorem groupTerm_eq {n r R W b P : ℕ} [Fact P.Prime] {Row : Type*}
    (formula : WeightedSystem.System n) (groupOf : Fin n → Fin r)
    (clauseGroup : Fin formula.constraints.length → Fin r) (rowAt : Fin R → Row)
    (rowNumber : (Σ _ : Fin r, Row) → Fin W)
    (measurement : ∀ g, Row → GroupedDeformation.LocalVariable groupOf g → ℤ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → ZMod P)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin r → Row → ZMod P)
    (supportBit : Fin n → Bool) (correctionValue : WeightedSystem.Incidence formula → ZMod P)
    (p nT groups rows width D m : Term) (gOf sBit cGroup arity : Term → Term)
    (rowNum : Term → Term → Term) (posAll negAll : Term → Term → Term → Term)
    (weight : Term → Term → Term) (localC : Term → Term → Term → Term)
    (measCoef : Term → Term → Term → Term → Term) (corr : Term → Term → Term) (base : List ℕ)
    (hp : StableAt w p base) (hpv : p.denote w base = P)
    (hn : StableAt w nT base) (hnv : nT.denote w base = n)
    (hgroups : StableAt w groups base) (hgroupsv : groups.denote w base = r)
    (hrows : StableAt w rows base) (hrowsv : rows.denote w base = R)
    (hwidth : StableAt w width base) (hwidthv : width.denote w base = W)
    (hD : StableAt w D base) (hDv : D.denote w base = b)
    (hm : StableAt w m base) (hmv : m.denote w base = formula.constraints.length)
    (G SB CG AR : ℕ → ℕ) (RN : ℕ → ℕ → ℕ) (Cp Cn : ℕ → ℕ → ℕ → ℕ) (Wt : ℕ → ℕ → ZMod P)
    (LC : ℕ → ℕ → ℕ → ZMod P) (MC : ℕ → ℕ → ℕ → ℕ → ZMod P) (CR : ℕ → ℕ → ZMod P)
    (iG : ImplN w base gOf G) (iSB : ImplN w base sBit SB) (iCG : ImplN w base cGroup CG)
    (iAR : ImplN w base arity AR) (iRN : ImplN2 w base rowNum RN)
    (iCp : ImplN3 w base posAll Cp) (iCn : ImplN3 w base negAll Cn)
    (iWt : ImplZ2 w base P weight Wt) (iLC : ImplZ3 w base P localC LC)
    (iMC : ImplZ4 w base P measCoef MC) (iCR : ImplZ2 w base P corr CR)
    (hG : ∀ v (h : v < n), G v = (groupOf ⟨v, h⟩).val)
    (hSB : ∀ v (h : v < n), SB v = (supportBit ⟨v, h⟩).toNat) (hSB01 : ∀ v, SB v ≤ 1)
    (hCG : ∀ e (h : e < formula.constraints.length), CG e = (clauseGroup ⟨e, h⟩).val)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    (hRN : ∀ g ρ (hg : g < r) (hρ : ρ < R), RN g ρ = (rowNumber ⟨⟨g, hg⟩, rowAt ⟨ρ, hρ⟩⟩).val)
    (hcoef : ∀ g ρ (hg : g < r) (hρ : ρ < R) v, measurement ⟨g, hg⟩ (rowAt ⟨ρ, hρ⟩) v =
      (Cp g ρ v.val.val : ℤ) - Cn g ρ v.val.val)
    (hWt : ∀ e (h : e < formula.constraints.length) A,
      Wt e A = ((formula.constraints[e]).weight (AssignmentLoop.assignment _ A) : ZMod P))
    (hLC : ∀ e i v (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hv : v < n),
      LC e i v = localCoefficient ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨v, hv⟩)
    (hMC : ∀ e i g ρ (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hg : g < r) (hρ : ρ < R),
      MC e i g ρ = measurementCoefficient ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨g, hg⟩ (rowAt ⟨ρ, hρ⟩))
    (hCR : ∀ e i (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length),
      CR e i = correctionValue ⟨⟨e, he⟩, ⟨i, hi⟩⟩)
    (hP2 : 2 < P) (Tt gt : Term) (Tv gv : ℕ) (hgr : gv < r) (env : List ℕ)
    (henv : ∃ pre, env = pre ++ base) (hT : StableAt w Tt env) (hTv : Tt.denote w env = Tv)
    (hgt : StableAt w gt env) (hgtv : gt.denote w env = gv) :
    ((sumGroupT p nT gOf gt sBit rows (posAll gt) (negAll gt)
        (fun ρ => digitT (add (mul (const 2) D) (const 1)) Tt (rowNum gt ρ)) D m cGroup arity weight
        localC (measPartT p groups rows measCoef rowNum (add (mul (const 2) D) (const 1)) D Tt)
        corr).denote w env : ZMod P) =
      WGroupedInnerLoop.sumGroup formula groupOf clauseGroup ⟨gv, hgr⟩ rowAt measurement
        localCoefficient measurementCoefficient
        (fun g row => (MeasurementEnumeration.groupedTuple rowNumber b Tv g row).val)
        supportBit correctionValue := by
  obtain ⟨pre0, rfl⟩ := henv
  have hrad : StableAt w (add (mul (const 2) D) (const 1)) (pre0 ++ base) :=
    ((stableAt_const 2 _).mul (hD.extend pre0)).add (stableAt_const 1 _)
  have hradv : (add (mul (const 2) D) (const 1)).denote w (pre0 ++ base) = 2 * b + 1 := by
    simp [hD pre0, hDv]
  have itd := tdig_implN (add (mul (const 2) D) (const 1)) Tt gt rowNum (pre0 ++ base) RN
    (iRN.extend pre0) hrad hT hgt
  have imt := measPart_implZ2 p groups rows measCoef rowNum (add (mul (const 2) D) (const 1)) D Tt
    base P (by omega) MC RN iMC iRN (pre0 ++ base) ⟨pre0, rfl⟩ (hp.extend pre0)
    (by rw [hp pre0]; exact hpv) (hgroups.extend pre0) (hrows.extend pre0) hrad (hD.extend pre0) hT
  rw [hradv, hTv, hgtv] at itd
  rw [hradv, hTv, hgroups pre0, hgroupsv, hrows pre0, hrowsv, hD pre0, hDv] at imt
  have key := sumGroupT_denote (base := pre0 ++ base) groupOf Fin.val Fin.val_injective gOf G
    (iG.extend pre0) hG p nT gt rows D m sBit _ cGroup arity (posAll gt) (negAll gt) weight localC
    (measPartT p groups rows measCoef rowNum (add (mul (const 2) D) (const 1)) D Tt) corr P
    (by omega) SB _ CG AR (Cp gv) (Cn gv) Wt LC _ CR (iSB.extend pre0) hSB01 itd (iCG.extend pre0)
    (iAR.extend pre0) (by have := (iCp.extend pre0).fix gt hgt; rwa [hgtv] at this)
    (by have := (iCn.extend pre0).fix gt hgt; rwa [hgtv] at this) (iWt.extend pre0)
    (iLC.extend pre0) imt (iCR.extend pre0) [] (hp.extend pre0) (by rw [List.nil_append, hp pre0]; exact hpv)
    (hn.extend pre0) (by rw [List.nil_append, hn pre0]; exact hnv) hgt ⟨gv, hgr⟩
    (by rw [List.nil_append]; exact hgtv) (hrows.extend pre0) (hD.extend pre0) (hm.extend pre0)
  simp only [List.nil_append] at key
  rw [key, hrows pre0, hrowsv, hD pre0, hDv, hm pre0, hmv]
  symm
  refine InnerLoopSpec.sumGroup_eq formula groupOf clauseGroup ⟨gv, hgr⟩ rowAt measurement
    localCoefficient measurementCoefficient _ supportBit correctionValue G SB CG AR _ (Cp gv) (Cn gv)
    b Wt LC _ CR hG hSB (fun ρ v => hcoef gv ρ hgr ρ.isLt v) (fun ρ => ?_) hCG hAR hWt hLC
    (fun e i he hi => ?_) hCR
  · simp only [MeasurementEnumeration.groupedTuple, MeasurementEnumeration.tuple,
      hRN gv ρ hgr ρ.isLt]
  · rw [WGroupedAssignmentEvaluation.scanSum_correct, add_zero,
      ← Fin.sum_univ_eq_sum_range (fun g => ∑ ρ ∈ Finset.range R, MC e i g ρ *
        (((Tv / (2 * b + 1) ^ RN g ρ % (2 * b + 1) : ℕ) : ZMod P) - (b : ZMod P))) r]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [WGroupedAssignmentEvaluation.scanSum_correct, add_zero,
      ← Fin.sum_univ_eq_sum_range (fun ρ => MC e i g ρ *
        (((Tv / (2 * b + 1) ^ RN g ρ % (2 * b + 1) : ℕ) : ZMod P) - (b : ZMod P))) R]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hMC e i g ρ he hi g.isLt ρ.isLt]
    simp only [MeasurementEnumeration.groupedTuple, MeasurementEnumeration.tuple,
      hRN g ρ g.isLt ρ.isLt]
    simp only [Int.cast_sub, Int.cast_natCast]

open WGroupedAssignmentEvaluation in
/-- **The formula-loop term computes `WGroupedFormulaLoop.evaluate`.** -/
theorem formulaLoopT_eq {n r R W b P : ℕ} [Fact P.Prime] {Row : Type*}
    (formula : WeightedSystem.System n) (groupOf : Fin n → Fin r)
    (clauseGroup : Fin formula.constraints.length → Fin r) (rowAt : Fin R → Row)
    (rowNumber : (Σ _ : Fin r, Row) → Fin W)
    (measurement : ∀ g, Row → GroupedDeformation.LocalVariable groupOf g → ℤ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → ZMod P)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin r → Row → ZMod P)
    (supportBit : Fin n → Bool) (correctionValue : WeightedSystem.Incidence formula → ZMod P)
    (p nT groups rows width D m : Term) (gOf sBit cGroup arity : Term → Term)
    (rowNum : Term → Term → Term) (posAll negAll : Term → Term → Term → Term)
    (weight : Term → Term → Term) (localC : Term → Term → Term → Term)
    (measCoef : Term → Term → Term → Term → Term) (corr : Term → Term → Term) (base : List ℕ)
    (hp : StableAt w p base) (hpv : p.denote w base = P)
    (hn : StableAt w nT base) (hnv : nT.denote w base = n)
    (hgroups : StableAt w groups base) (hgroupsv : groups.denote w base = r)
    (hrows : StableAt w rows base) (hrowsv : rows.denote w base = R)
    (hwidth : StableAt w width base) (hwidthv : width.denote w base = W)
    (hD : StableAt w D base) (hDv : D.denote w base = b)
    (hm : StableAt w m base) (hmv : m.denote w base = formula.constraints.length)
    (G SB CG AR : ℕ → ℕ) (RN : ℕ → ℕ → ℕ) (Cp Cn : ℕ → ℕ → ℕ → ℕ) (Wt : ℕ → ℕ → ZMod P)
    (LC : ℕ → ℕ → ℕ → ZMod P) (MC : ℕ → ℕ → ℕ → ℕ → ZMod P) (CR : ℕ → ℕ → ZMod P)
    (iG : ImplN w base gOf G) (iSB : ImplN w base sBit SB) (iCG : ImplN w base cGroup CG)
    (iAR : ImplN w base arity AR) (iRN : ImplN2 w base rowNum RN)
    (iCp : ImplN3 w base posAll Cp) (iCn : ImplN3 w base negAll Cn)
    (iWt : ImplZ2 w base P weight Wt) (iLC : ImplZ3 w base P localC LC)
    (iMC : ImplZ4 w base P measCoef MC) (iCR : ImplZ2 w base P corr CR)
    (hG : ∀ v (h : v < n), G v = (groupOf ⟨v, h⟩).val)
    (hSB : ∀ v (h : v < n), SB v = (supportBit ⟨v, h⟩).toNat) (hSB01 : ∀ v, SB v ≤ 1)
    (hCG : ∀ e (h : e < formula.constraints.length), CG e = (clauseGroup ⟨e, h⟩).val)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    (hRN : ∀ g ρ (hg : g < r) (hρ : ρ < R), RN g ρ = (rowNumber ⟨⟨g, hg⟩, rowAt ⟨ρ, hρ⟩⟩).val)
    (hcoef : ∀ g ρ (hg : g < r) (hρ : ρ < R) v, measurement ⟨g, hg⟩ (rowAt ⟨ρ, hρ⟩) v =
      (Cp g ρ v.val.val : ℤ) - Cn g ρ v.val.val)
    (hWt : ∀ e (h : e < formula.constraints.length) A,
      Wt e A = ((formula.constraints[e]).weight (AssignmentLoop.assignment _ A) : ZMod P))
    (hLC : ∀ e i v (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hv : v < n),
      LC e i v = localCoefficient ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨v, hv⟩)
    (hMC : ∀ e i g ρ (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hg : g < r) (hρ : ρ < R),
      MC e i g ρ = measurementCoefficient ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨g, hg⟩ (rowAt ⟨ρ, hρ⟩))
    (hCR : ∀ e i (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length),
      CR e i = correctionValue ⟨⟨e, he⟩, ⟨i, hi⟩⟩)
    (hP2 : 2 < P) :
    ((formulaLoopT p nT groups rows width D m gOf sBit cGroup arity rowNum posAll negAll weight
        localC measCoef corr).denote w base : ZMod P) =
      WGroupedFormulaLoop.evaluate formula groupOf clauseGroup rowAt rowNumber b measurement
        localCoefficient measurementCoefficient supportBit correctionValue := by
  have hrad : StableAt w (add (mul (const 2) D) (const 1)) base :=
    ((stableAt_const 2 _).mul hD).add (stableAt_const 1 _)
  have hradv : (add (mul (const 2) D) (const 1)).denote w base = 2 * b + 1 := by simp [hDv]
  rw [WGroupedFormulaLoop.evaluate, MeasurementEnumeration.sumGrouped, sumLoop_correct, add_zero,
    formulaLoopT, denote_sumModZ p _ _ base P (fun T => ∏ g : Fin r,
      WGroupedInnerLoop.sumGroup formula groupOf clauseGroup g rowAt measurement localCoefficient
        measurementCoefficient
        (fun g row => (MeasurementEnumeration.groupedTuple rowNumber b T g row).val)
        supportBit correctionValue) hp hpv (fun acc T _ => ?_),
    powT_denote _ _ base hrad, hradv, hwidthv]
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [scanProduct_correct, mul_one]
  · have hpv1 : p.denote w (acc :: T :: base) = P := by rw [hp.cons₂]; exact hpv
    rw [denote_prodModZ p groups _ (acc :: T :: base) P (fun g => if h : g < r then
        WGroupedInnerLoop.sumGroup formula groupOf clauseGroup ⟨g, h⟩ rowAt measurement
          localCoefficient measurementCoefficient
          (fun g row => (MeasurementEnumeration.groupedTuple rowNumber b T g row).val)
          supportBit correctionValue else 1) (hp.extend₂ acc T) hpv1 (fun acc' g hg => ?_),
      hgroups.cons₂, hgroupsv]
    · rw [← Fin.prod_univ_eq_prod_range]
      exact Finset.prod_congr rfl fun g _ => by rw [dif_pos g.isLt]
    · have hg' : g < r := by rw [hgroups.cons₂, hgroupsv] at hg; exact hg
      rw [dif_pos hg']
      have hTs : StableAt w (lvl base.length) ([acc', g, acc, T] ++ base) :=
        (stableAt_index base acc T).extend [acc', g]
      have hTv : (lvl base.length).denote w ([acc', g, acc, T] ++ base) = T :=
        ((stableAt_index (w := w) base acc T) [acc', g]).trans (denote_lvl_index base acc T)
      exact groupTerm_eq formula groupOf clauseGroup rowAt rowNumber measurement localCoefficient measurementCoefficient supportBit correctionValue p nT groups rows width D m gOf sBit cGroup arity rowNum posAll negAll weight localC measCoef corr base hp hpv hn hnv hgroups hgroupsv hrows hrowsv hwidth hwidthv hD hDv hm hmv G SB CG AR RN Cp Cn Wt LC MC CR iG iSB iCG iAR iRN iCp iCn iWt iLC iMC iCR hG hSB hSB01 hCG hAR hRN hcoef hWt hLC hMC hCR hP2 (lvl base.length) (lvl (acc :: T :: base).length) T g hg'
        ([acc', g, acc, T] ++ base) ⟨[acc', g, acc, T], rfl⟩ hTs hTv
        (stableAt_index (acc :: T :: base) acc' g) (denote_lvl_index _ _ _)

end NtimeDspace.ProgTerm
