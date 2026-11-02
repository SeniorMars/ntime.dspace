import NtimeDspace.TaylorLoopTerm

/-!
# The compressed Taylor loop term

`supportValueT` is one support's contribution (the signed sum over masks of the
formula loop term), and `taylorLoopT` sums it over all valid candidate codes.
`supportValueT_eq` and `taylorLoopT_eq` show they compute
`WCompressedTaylorLoop.supportValue` and `WCompressedTaylorLoop.evaluate`.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

section Def

variable (p B Cap Lb M K nT groups rows width D m : Term) (gOf cGroup arity : Term → Term)
  (rowNum : Term → Term → Term) (posAll negAll : Term → Term → Term → Term)
  (weight : Term → Term → Term) (localC : Term → Term → Term → Term)
  (measCoef : Term → Term → Term → Term → Term) (evalC : Term → Term → Term → Term → Term)
  (node point : Term)

/-- One support's contribution: the signed sum over masks of the formula loop. -/
def supportValueT (c : Term) : Term :=
  Term.sumMod p (pow2 (codeSizeT B Cap Lb M K c)) fun mask =>
    mod (mul (signT p (sub (codeSizeT B Cap Lb M K c)
        (sumT (codeSizeT B Cap Lb M K c) fun j => bit mask j)))
      (formulaLoopT p nT groups rows width D m gOf (sBitT B Cap Lb M K nT c) cGroup arity rowNum
        posAll negAll weight localC measCoef
        (corrT B Cap Lb M K p nT evalC node point c mask))) p

/-- **The compressed Taylor loop**: the sum over valid candidate codes. -/
def taylorLoopT : Term :=
  Term.sumMod p (sub (pow2 (add K (const 1))) (const 1)) fun idx =>
    ite (codeValidT B Cap Lb M K (add idx (const 1)))
      (supportValueT p B Cap Lb M K nT groups rows width D m gOf cGroup arity rowNum posAll negAll
        weight localC measCoef evalC node point (add idx (const 1)))
      (const 0)

end Def

theorem countOnes_assignment (width A : ℕ) :
    SupportSubsetLoop.countOnes width (AssignmentLoop.assignment width A) =
      ∑ j ∈ Finset.range width, (A.testBit j).toNat := by
  rw [SupportSubsetLoop.countOnes_eq_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [AssignmentLoop.assignment]
  by_cases h : A.testBit j <;> simp [h]

theorem assignmentBit_eq_selN {n cap : ℕ} (E : List (Fin n)) (valid : SupportAssignment.Valid cap E)
    (A : ℕ) (v : Fin n) :
    SupportAssignment.assignmentBit E (Nat.le_refl _) (AssignmentLoop.assignment E.length A) v =
      selN E A v := by
  unfold SupportAssignment.assignmentBit selN
  rw [dif_pos v.isLt]
  by_cases hv : v ∈ E
  · rw [dif_pos hv]
    simp only [AssignmentLoop.assignment, hv, decide_true, Bool.true_and, Fin.eta]
    rw [idxOf_eq_countBelow E valid.1 v hv]
  · rw [dif_neg hv]
    simp [hv]

set_option maxHeartbeats 1000000 in
/-- **One support's contribution.** -/
theorem supportValueT_eq {n r R W b P cap budget : ℕ} [Fact P.Prime] {Row : Type*}
    (formula : WeightedSystem.System n) (groupOf : Fin n → Fin r)
    (clauseGroup : Fin formula.constraints.length → Fin r) (rowAt : Fin R → Row)
    (rowNumber : (Σ _ : Fin r, Row) → Fin W)
    (measurement : ∀ g, Row → GroupedDeformation.LocalVariable groupOf g → ℤ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → ZMod P)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin r → Row → ZMod P)
    (evaluateCoefficient : WeightedSystem.Incidence formula → Fin n → ZMod P → ZMod P)
    (p B Cap Lb M K nT groups rows width D m : Term) (gOf cGroup arity : Term → Term)
    (rowNum : Term → Term → Term) (posAll negAll : Term → Term → Term → Term)
    (weight : Term → Term → Term) (localC : Term → Term → Term → Term)
    (measCoef : Term → Term → Term → Term → Term) (evalC : Term → Term → Term → Term → Term)
    (node point : Term) (env : List ℕ)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    (hgroups : StableAt w groups env) (hgroupsv : groups.denote w env = r)
    (hrows : StableAt w rows env) (hrowsv : rows.denote w env = R)
    (hwidth : StableAt w width env) (hwidthv : width.denote w env = W)
    (hD : StableAt w D env) (hDv : D.denote w env = b)
    (hm : StableAt w m env) (hmv : m.denote w env = formula.constraints.length)
    (pp : ParserParams w env n cap budget B Cap Lb M K)
    (G CG AR : ℕ → ℕ) (RN : ℕ → ℕ → ℕ) (Cp Cn : ℕ → ℕ → ℕ → ℕ) (Wt : ℕ → ℕ → ZMod P)
    (LC : ℕ → ℕ → ℕ → ZMod P) (MC : ℕ → ℕ → ℕ → ℕ → ZMod P) (EC : ℕ → ℕ → ℕ → ℕ → ZMod P)
    (iG : ImplN w env gOf G) (iCG : ImplN w env cGroup CG)
    (iAR : ImplN w env arity AR) (iRN : ImplN2 w env rowNum RN)
    (iCp : ImplN3 w env posAll Cp) (iCn : ImplN3 w env negAll Cn)
    (iWt : ImplZ2 w env P weight Wt) (iLC : ImplZ3 w env P localC LC)
    (iMC : ImplZ4 w env P measCoef MC) (iEC : ImplZ4 w env P evalC EC)
    (hG : ∀ v (h : v < n), G v = (groupOf ⟨v, h⟩).val)
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
    (hEC : ∀ e i v x (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hv : v < n),
      EC e i v x = evaluateCoefficient ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨v, hv⟩ (x : ZMod P))
    (hnode : StableAt w node env) (hpoint : StableAt w point env)
    {c : Term} (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env)
    (hlt : c.denote w env < 2 ^ (budget + 1))
    {E : List (Fin n)} (valid : SupportAssignment.Valid cap E)
    (code : SupportEncoding.binaryTail (c.denote w env) = SupportAssignment.encode E)
    (hP2 : 2 < P) :
    ((supportValueT p B Cap Lb M K nT groups rows width D m gOf cGroup arity rowNum posAll negAll
        weight localC measCoef evalC node point c).denote w env : ZMod P) =
      WCompressedTaylorLoop.supportValue formula groupOf clauseGroup rowAt rowNumber b cap
        measurement localCoefficient measurementCoefficient evaluateCoefficient
        (node.denote w env : ZMod P) (point.denote w env : ZMod P) (SupportAssignment.encode E) := by
  have hP0 : 0 < P := by omega
  have hsize := denote_codeSizeT pp hc hpos hlt valid code
  unfold WCompressedTaylorLoop.supportValue
  rw [SupportCardinality.count_encode E valid]
  simp only []
  unfold SupportSubsetLoop.sumSignedSubsets AssignmentLoop.sumAssignments
  rw [sumLoop_correct, add_zero]
  unfold supportValueT
  rw [denote_sumModZ p _ _ env P _ hp hpv, denote_pow2, hsize]
  intro acc A hA
  rw [denote_pow2, hsize] at hA
  set env' := acc :: A :: env with henv'
  have e' : env' = [acc, A] ++ env := rfl
  have hp' : StableAt w p env' := by rw [e']; exact hp.extend _
  have hpv' : p.denote w env' = P := by rw [e', hp _, hpv]
  have hsize' : (codeSizeT B Cap Lb M K c).denote w env' = E.length := by
    rw [e']; rw [denote_codeSizeT (pp.extend _) (hc.extend _) (by rw [hc _]; exact hpos)
      (by rw [hc _]; exact hlt) valid (by rw [hc _]; exact code)]
  have hAv : (lvl env.length).denote w env' = A := denote_lvl_index env acc A
  have hcv : c.denote w env' = c.denote w env := by rw [e']; exact hc _
  -- the sign
  have hsign : ((signT p (sub (codeSizeT B Cap Lb M K c)
      (sumT (codeSizeT B Cap Lb M K c) fun j => bit (lvl env.length) j))).denote w env' : ZMod P) =
      (-1) ^ (E.length - SupportSubsetLoop.countOnes E.length
        (AssignmentLoop.assignment E.length A)) := by
    rw [signT_denote p _ env' P (by omega) hpv', denote_sub, hsize', countOnes_assignment,
      denote_sumT _ _ env' (fun j => (A.testBit j).toNat), hsize']
    intro acc' j
    simp only [denote_bit, denote_lvl_index]
    congr 2
    rw [show (lvl env.length).denote w (acc' :: j :: env') = A by
      rw [denote_lvl]; simp only [env', List.length_cons]
      rw [show env.length + 1 + 1 + 1 + 1 - env.length - 1 = 3 by omega]; rfl]
  have ext : ∀ {t : Term} {x : ℕ}, StableAt w t env → t.denote w env = x →
      StableAt w t env' ∧ t.denote w env' = x := fun h hx => ⟨h.extend [acc, A], by rw [e', h _, hx]⟩
  have hAs : StableAt w (lvl env.length) env' := stableAt_lvl (by simp [env'])
  have iSB := implN_sBitT (pp.extend [acc, A]) (ext hn hnv).1 (ext hn hnv).2 (hc.extend _)
    (by rw [hc _]; exact hpos) (by rw [hc _]; exact hlt) valid (by rw [hc _]; exact code)
  have iCR := implZ2_corrT (pp.extend [acc, A]) hP0 hp' hpv' (ext hn hnv).1 (ext hn hnv).2
    (hc.extend _) (by rw [hc _]; exact hpos) (by rw [hc _]; exact hlt) hAs (hnode.extend _)
    (hpoint.extend _) valid (by rw [hc _]; exact code) (iEC.extend [acc, A])
  rw [denote_mod, denote_mul, hpv', ZMod.natCast_mod, Nat.cast_mul, hsign]
  congr 1
  refine formulaLoopT_eq formula groupOf clauseGroup rowAt rowNumber measurement localCoefficient
    measurementCoefficient _ _ p nT groups rows width D m gOf (sBitT B Cap Lb M K nT c) cGroup arity
    rowNum posAll negAll weight localC measCoef
    (corrT B Cap Lb M K p nT evalC node point c (lvl env.length)) env' hp' hpv'
    (ext hn hnv).1 (ext hn hnv).2 (ext hgroups hgroupsv).1 (ext hgroups hgroupsv).2
    (ext hrows hrowsv).1 (ext hrows hrowsv).2 (ext hwidth hwidthv).1 (ext hwidth hwidthv).2
    (ext hD hDv).1 (ext hD hDv).2 (ext hm hmv).1 (ext hm hmv).2
    G (sBitN E) CG AR RN Cp Cn Wt LC MC _ (iG.extend [acc, A]) iSB (iCG.extend [acc, A])
    (iAR.extend [acc, A]) (iRN.extend [acc, A]) (iCp.extend [acc, A]) (iCn.extend [acc, A])
    (iWt.extend [acc, A]) (iLC.extend [acc, A]) (iMC.extend [acc, A])
    iCR hG ?_ (sBitN_le E) hCG hAR hRN hcoef hWt hLC hMC ?_ hP2
  · intro v h
    rw [WCompressedTaylorLoop.membershipBit_encode cap E valid]
    unfold sBitN
    rw [dif_pos h]
    simp [List.mem_toFinset]
  · intro e i he hi
    have hA2 : (lvl env.length).denote w ([acc, A] ++ env) = A := denote_lvl_index env acc A
    have hnd : node.denote w ([acc, A] ++ env) = node.denote w env := hnode _
    have hpt : point.denote w ([acc, A] ++ env) = point.denote w env := hpoint _
    rw [hA2, hnd, hpt, SparseCorrection.compressed_encode _ E valid, Option.getD_some,
      SparseCorrection.correction_eq_sum]
    rw [← Fin.sum_univ_eq_sum_range (fun v => if selN E A v then
      EC e i v (node.denote w env + point.denote w env) - EC e i v (node.denote w env) else 0) n]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [SupportAssignment.assignmentBit_extendMask, assignmentBit_eq_selN E valid,
      hEC _ _ _ _ he hi v.isLt, hEC _ _ _ _ he hi v.isLt]
    push_cast
    rfl

set_option maxHeartbeats 1000000 in
/-- **The compressed Taylor loop term computes the compressed Taylor loop.** -/
theorem taylorLoopT_eq {n r R W b P k : ℕ} [Fact P.Prime] {Row : Type*}
    (formula : WeightedSystem.System n) (groupOf : Fin n → Fin r)
    (clauseGroup : Fin formula.constraints.length → Fin r) (rowAt : Fin R → Row)
    (rowNumber : (Σ _ : Fin r, Row) → Fin W)
    (measurement : ∀ g, Row → GroupedDeformation.LocalVariable groupOf g → ℤ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → ZMod P)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin r → Row → ZMod P)
    (evaluateCoefficient : WeightedSystem.Incidence formula → Fin n → ZMod P → ZMod P)
    (p B Cap Lb M K nT groups rows width D m : Term) (gOf cGroup arity : Term → Term)
    (rowNum : Term → Term → Term) (posAll negAll : Term → Term → Term → Term)
    (weight : Term → Term → Term) (localC : Term → Term → Term → Term)
    (measCoef : Term → Term → Term → Term → Term) (evalC : Term → Term → Term → Term → Term)
    (node point : Term) (env : List ℕ)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    (hgroups : StableAt w groups env) (hgroupsv : groups.denote w env = r)
    (hrows : StableAt w rows env) (hrowsv : rows.denote w env = R)
    (hwidth : StableAt w width env) (hwidthv : width.denote w env = W)
    (hD : StableAt w D env) (hDv : D.denote w env = b)
    (hm : StableAt w m env) (hmv : m.denote w env = formula.constraints.length)
    (pp : ParserParams w env n (Parameters.q n k) (SupportBudget.limit n k) B Cap Lb M K)
    (G CG AR : ℕ → ℕ) (RN : ℕ → ℕ → ℕ) (Cp Cn : ℕ → ℕ → ℕ → ℕ) (Wt : ℕ → ℕ → ZMod P)
    (LC : ℕ → ℕ → ℕ → ZMod P) (MC : ℕ → ℕ → ℕ → ℕ → ZMod P) (EC : ℕ → ℕ → ℕ → ℕ → ZMod P)
    (iG : ImplN w env gOf G) (iCG : ImplN w env cGroup CG)
    (iAR : ImplN w env arity AR) (iRN : ImplN2 w env rowNum RN)
    (iCp : ImplN3 w env posAll Cp) (iCn : ImplN3 w env negAll Cn)
    (iWt : ImplZ2 w env P weight Wt) (iLC : ImplZ3 w env P localC LC)
    (iMC : ImplZ4 w env P measCoef MC) (iEC : ImplZ4 w env P evalC EC)
    (hG : ∀ v (h : v < n), G v = (groupOf ⟨v, h⟩).val)
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
    (hEC : ∀ e i v x (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hv : v < n),
      EC e i v x = evaluateCoefficient ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨v, hv⟩ (x : ZMod P))
    (hnode : StableAt w node env) (hpoint : StableAt w point env) (hP2 : 2 < P) :
    ((taylorLoopT p B Cap Lb M K nT groups rows width D m gOf cGroup arity rowNum posAll negAll
        weight localC measCoef evalC node point).denote w env : ZMod P) =
      WCompressedTaylorLoop.evaluate formula groupOf clauseGroup rowAt rowNumber b k
        measurement localCoefficient measurementCoefficient evaluateCoefficient
        (node.denote w env : ZMod P) (point.denote w env : ZMod P) := by
  set budget := SupportBudget.limit n k
  set cap := Parameters.q n k
  unfold WCompressedTaylorLoop.evaluate SupportEnumeration.enumerateValid
    SupportEnumeration.enumerate
  rw [SupportEnumeration.foldFrom_eq_sum, zero_add]
  unfold taylorLoopT
  have hbound : (sub (pow2 (add K (const 1))) (const 1)).denote w env =
      SupportEnumeration.candidateCount budget := by
    simp [pp.hKv, SupportEnumeration.candidateCount]
  rw [denote_sumModZ p _ _ env P (fun idx => if h : idx < SupportEnumeration.candidateCount budget
      then SupportEnumeration.guarded n cap (WCompressedTaylorLoop.supportValue formula groupOf
        clauseGroup rowAt rowNumber b cap measurement localCoefficient measurementCoefficient
        evaluateCoefficient (node.denote w env : ZMod P) (point.denote w env : ZMod P))
        (SupportEnumeration.candidate ⟨idx, h⟩) else 0) hp hpv, hbound, Finset.sum_range]
  · refine Finset.sum_congr rfl fun idx _ => ?_
    rw [dif_pos idx.isLt]
    simp only [Nat.zero_add]
    rfl
  intro acc idx hidx
  rw [hbound] at hidx
  rw [dif_pos hidx]
  set env' := acc :: idx :: env with henv'
  have e' : env' = [acc, idx] ++ env := rfl
  have hc : StableAt w (add (lvl env.length) (const 1)) env' :=
    (stableAt_lvl (by simp [env'])).add (stableAt_const _ _)
  have hcv : (add (lvl env.length) (const 1)).denote w env' = idx + 1 := by
    simp [env', denote_lvl_index]
  have hpos : 1 ≤ (add (lvl env.length) (const 1)).denote w env' := by rw [hcv]; omega
  have hlt : (add (lvl env.length) (const 1)).denote w env' < 2 ^ (budget + 1) := by
    rw [hcv]; unfold SupportEnumeration.candidateCount at hidx; omega
  have pp' : ParserParams w env' n cap budget B Cap Lb M K := pp.extend [acc, idx]
  rw [denote_ite, denote_codeValidT pp' hc hpos hlt, hcv]
  unfold SupportEnumeration.guarded SupportEnumeration.candidate
  simp only [Fin.val_mk]
  cases hval : SupportEnumeration.validate n cap (SupportEncoding.binaryTail (idx + 1)) with
  | none => simp
  | some _ =>
    have hne : SupportEnumeration.validate n cap (SupportEncoding.binaryTail (idx + 1)) ≠ none := by
      rw [hval]; simp
    obtain ⟨E, valid, code⟩ := exists_support_of_valid hne
    simp only []
    rw [code]
    have ext : ∀ {t : Term} {x : ℕ}, StableAt w t env → t.denote w env = x →
        StableAt w t env' ∧ t.denote w env' = x :=
      fun h hx => ⟨h.extend [acc, idx], by rw [e', h _, hx]⟩
    have hnd : node.denote w env' = node.denote w env := by rw [e']; exact hnode _
    have hpt : point.denote w env' = point.denote w env := by rw [e']; exact hpoint _
    rw [← hnd, ← hpt]
    exact supportValueT_eq formula groupOf clauseGroup rowAt rowNumber measurement localCoefficient
      measurementCoefficient evaluateCoefficient p B Cap Lb M K nT groups rows width D m gOf cGroup
      arity rowNum posAll negAll weight localC measCoef evalC node point env'
      (ext hp hpv).1 (ext hp hpv).2 (ext hn hnv).1 (ext hn hnv).2 (ext hgroups hgroupsv).1
      (ext hgroups hgroupsv).2 (ext hrows hrowsv).1 (ext hrows hrowsv).2 (ext hwidth hwidthv).1
      (ext hwidth hwidthv).2 (ext hD hDv).1 (ext hD hDv).2 (ext hm hmv).1 (ext hm hmv).2 pp'
      G CG AR RN Cp Cn Wt LC MC EC (iG.extend [acc, idx]) (iCG.extend [acc, idx])
      (iAR.extend [acc, idx]) (iRN.extend [acc, idx]) (iCp.extend [acc, idx])
      (iCn.extend [acc, idx]) (iWt.extend [acc, idx]) (iLC.extend [acc, idx])
      (iMC.extend [acc, idx]) (iEC.extend [acc, idx]) hG hCG hAR hRN hcoef hWt hLC hMC hEC
      (hnode.extend [acc, idx]) (hpoint.extend [acc, idx]) hc hpos hlt valid
      (by rw [hcv]; exact code) hP2

end NtimeDspace.ProgTerm
