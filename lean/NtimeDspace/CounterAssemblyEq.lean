import NtimeDspace.CounterAssembly

/-!
# The system counter term computes the weighted count

`systemCounterT_eq`: with a balanced seed number and the parameter conditions of
`WConcreteCountingLoop.countModP_correct`, the system counter term computes
`S.count` modulo `p`.
-/

namespace NtimeDspace.ProgTerm

open Term Placement WeightedSystem

variable {w : List Bool} {n : ℕ}

set_option maxHeartbeats 4000000 in
theorem systemCounterT_eq {P Q bits k s sP sN width : ℕ} [Fact P.Prime] (S : System n)
    (npos : 0 < n) (hbal : balN S Q bits s)
    (hP3 : 2 < P) (hQP : Q < P) (large : 6 ≤ k) (small : width < P)
    (below : Parameters.q n k + 1 < P)
    (capacity : incidenceCount S * (width - 1) < Q * (Parameters.q n k + 1))
    (no_alias : incidenceCount S * (width - 1) + Q * Parameters.q n k ≤ P - 2)
    {pT QT orderT B Cap Lb M K nT mT bitsT IBT sT sPT sNT widthT copiesT : Term}
    {arity : Term → Term} {varT : Term → Term → Term} {weight : Term → Term → Term}
    {env : List ℕ}
    (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q)
    (ho : StableAt w orderT env) (hov : orderT.denote w env = Parameters.q n k + 1)
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    (hm : StableAt w mT env) (hmv : mT.denote w env = S.constraints.length)
    (hb : StableAt w bitsT env) (hbv : bitsT.denote w env = bits)
    (hIB : StableAt w IBT env) (hIBv : IBT.denote w env = WSchedulePlacement.inputBits S)
    (hs : StableAt w sT env) (hsv : sT.denote w env = s)
    (hsP : StableAt w sPT env) (hsPv : sPT.denote w env = sP)
    (hsN : StableAt w sNT env) (hsNv : sNT.denote w env = sN)
    (hwd : StableAt w widthT env) (hwdv : widthT.denote w env = width)
    (hcp : StableAt w copiesT env) (hcpv : copiesT.denote w env = copiesOf S Q bits)
    (pp : ParserParams w env n (Parameters.q n k) (SupportBudget.limit n k) B Cap Lb M K)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = (S.constraints[e]).scope.length)
    {V : ℕ → ℕ → ℕ} (iV : ImplN2 w env varT V)
    (hV : ∀ inc : Incidence S, V inc.1 inc.2 = (incidenceVariable S inc).val)
    {Wt : ℕ → ℕ → ZMod P} (iWt : ImplZ2 w env P weight Wt)
    (hWt : ∀ e (h : e < S.constraints.length) A,
      Wt e A = ((S.constraints[e]).weight (AssignmentLoop.assignment _ A) : ZMod P)) :
    ((systemCounterT pT QT orderT B Cap Lb M K nT mT bitsT IBT sT sPT sNT widthT copiesT arity varT
        weight).denote w env : ZMod P) = (S.count : ZMod P) := by
  classical
  have positive : 0 < 2 ^ bits := Nat.two_pow_pos bits
  set r := 2 ^ bits with hr_def
  set start : ℤ := (sP : ℤ) - sN with hstart
  set seed := seedOf S Q bits s
  set copies := copiesOf S Q bits
  set BC := SpectralIndexing.badCount r Q positive start width
  let copyOf : Incidence S → Fin copies := copyOfS S Q bits s hbal
  let labelOf : Incidence S → TensorEvaluation.Label r Q := fun inc =>
    WSchedulePlacement.incidenceLabel S bits seed inc
  set LBf : ℕ → ℕ → ℕ := fun e i => labelN Q bits s (WSchedulePlacement.inputBits S) (V e i) e
  set CPf := rankNum S LBf
  have hrS : StableAt w (rT' bitsT) env := hb.pow2
  have hrv : (rT' bitsT).denote w env = r := by simp [rT', hbv, r]
  have iLB : ImplN2 w env (lbT' QT bitsT IBT sT varT) LBf := by
    have h := implN2_labelT hQ hb hIB hs iV
    rw [hQv, hbv, hsv, hIBv] at h
    exact h
  have iCP : ImplN2 w env (cpT' QT mT bitsT IBT sT arity varT) CPf :=
    implN2_copyRankT S hm hmv iAR hAR iLB
  have hBC : (badCountT (rT' bitsT) QT sPT sNT widthT).denote w env = BC := by
    rw [denote_badCountT positive hrS hrv hQ hQv hsP hsN hwd, hsPv, hsNv, hwdv]
  have hBCs : StableAt w (badCountT (rT' bitsT) QT sPT sNT widthT) env :=
    StableAt.badCountT positive hrS hrv hQ hQv hsP hsN hwd
  have hrowsS : StableAt w (rowsT' QT bitsT sPT sNT widthT copiesT) env := hcp.mul hBCs
  have hrowsv : (rowsT' QT bitsT sPT sNT widthT copiesT).denote w env = copies * BC := by
    simp only [rowsT', denote_mul, hcpv, hBC, copies]
  have hV' : ∀ inc : Incidence S, V inc.1 inc.2 = (WIncidenceEvaluation.variableOf S inc).val :=
    fun inc => hV inc
  have hLBinc : ∀ inc : Incidence S, labelOf inc = SpectralIndexing.label r Q positive (LBf inc.1 inc.2) :=
    fun inc => by
      have h := incidenceLabel_seedOf S Q bits s inc
      simp only [labelOf, LBf, hV inc]
      exact h
  have hLfun : (fun b : Incidence S => LBf b.1 b.2) = incLabelN S Q bits s := by
    funext b; simp only [LBf, incLabelN, hV b]
  have hCPinc : ∀ inc : Incidence S, CPf inc.1 inc.2 = (copyOf inc).val := fun inc => by
    simp only [CPf, rankNum_eq_rankN, hLfun, copyOf, copyOfS]
  -- values at extensions
  have xP : ∀ pre : List ℕ, pT.denote w (pre ++ env) = P := fun pre => by rw [hp pre, hpv]
  have xQ : ∀ pre : List ℕ, QT.denote w (pre ++ env) = Q := fun pre => by rw [hQ pre, hQv]
  have xb : ∀ pre : List ℕ, bitsT.denote w (pre ++ env) = bits := fun pre => by rw [hb pre, hbv]
  have xIB : ∀ pre : List ℕ, IBT.denote w (pre ++ env) = WSchedulePlacement.inputBits S :=
    fun pre => by rw [hIB pre, hIBv]
  have xs : ∀ pre : List ℕ, sT.denote w (pre ++ env) = s := fun pre => by rw [hs pre, hsv]
  have xsP : ∀ pre : List ℕ, sPT.denote w (pre ++ env) = sP := fun pre => by rw [hsP pre, hsPv]
  have xsN : ∀ pre : List ℕ, sNT.denote w (pre ++ env) = sN := fun pre => by rw [hsN pre, hsNv]
  have xwd : ∀ pre : List ℕ, widthT.denote w (pre ++ env) = width := fun pre => by rw [hwd pre, hwdv]
  have xr : ∀ pre : List ℕ, (rT' bitsT).denote w (pre ++ env) = r := fun pre => by rw [hrS pre, hrv]
  have xrows : ∀ pre : List ℕ, (rowsT' QT bitsT sPT sNT widthT copiesT).denote w (pre ++ env) =
      copies * BC := fun pre => by rw [hrowsS pre, hrowsv]
  -- node-dependent contracts
  have iG : ∀ (pre : List ℕ) (nd : Term), StableAt w nd (pre ++ env) →
      ImplN w (pre ++ env) (fun v => grpT QT bitsT IBT sT (const 0) nd v)
        (grpN Q bits (WSchedulePlacement.inputBits S) s 0 (nd.denote w (pre ++ env))) := by
    intro pre nd hnd
    have h := implN_grpT (hQ.extend pre) (hb.extend pre) (hIB.extend pre) (hs.extend pre)
      (stableAt_const 0 _) hnd
    rw [xQ, xb, xIB, xs, denote_const] at h
    exact h
  have iCG : ∀ (pre : List ℕ) (nd : Term), StableAt w nd (pre ++ env) →
      ImplN w (pre ++ env) (fun e => grpT QT bitsT IBT sT (const 1) nd e)
        (grpN Q bits (WSchedulePlacement.inputBits S) s 1 (nd.denote w (pre ++ env))) := by
    intro pre nd hnd
    have h := implN_grpT (hQ.extend pre) (hb.extend pre) (hIB.extend pre) (hs.extend pre)
      (stableAt_const 1 _) hnd
    rw [xQ, xb, xIB, xs, denote_const] at h
    exact h
  have iRN : ∀ (pre : List ℕ) (nd : Term), StableAt w nd (pre ++ env) →
      ImplN2 w (pre ++ env) (rowNumT (rowsT' QT bitsT sPT sNT widthT copiesT) nd)
        ((fun _ν g ρ => ρ + copies * BC * g) (nd.denote w (pre ++ env))) := by
    intro pre nd _
    have h := implN2_rowNumT (nd := nd) (hrowsS.extend pre)
    rw [xrows] at h
    exact h
  have iCp : ∀ (pre : List ℕ) (nd : Term), StableAt w nd (pre ++ env) →
      ImplN3 w (pre ++ env) (measSignT (rT' bitsT) QT sPT sNT widthT mT arity
        (cpT' QT mT bitsT IBT sT arity varT) (lbT' QT bitsT IBT sT varT) varT
        (signPosT (rT' bitsT) QT) nd)
        ((fun _ν _g ρ v => measSignN (Q := Q) positive S start width CPf LBf V 0 ρ v)
          (nd.denote w (pre ++ env))) := by
    intro pre nd _
    have h := implN3_measSignT positive S 0 (fun E u w' hrE hrvE hQvE hu hw' =>
        pos_signPos positive hrE hrvE hQvE hu hw') (hrS.extend pre) (xr pre) (hQ.extend pre)
      (xQ pre) (hsP.extend pre) (hsN.extend pre) (hwd.extend pre) (hm.extend pre)
      (by rw [hm pre, hmv]) (iAR.extend pre) hAR (iCP.extend pre) (iLB.extend pre) (iV.extend pre) nd
    rw [xsP, xsN, xwd] at h
    exact h
  have iCn : ∀ (pre : List ℕ) (nd : Term), StableAt w nd (pre ++ env) →
      ImplN3 w (pre ++ env) (measSignT (rT' bitsT) QT sPT sNT widthT mT arity
        (cpT' QT mT bitsT IBT sT arity varT) (lbT' QT bitsT IBT sT varT) varT
        (signNegT (rT' bitsT) QT) nd)
        ((fun _ν _g ρ v => measSignN (Q := Q) positive S start width CPf LBf V 1 ρ v)
          (nd.denote w (pre ++ env))) := by
    intro pre nd _
    have h := implN3_measSignT positive S 1 (fun E u w' hrE hrvE hQvE hu hw' =>
        neg_signNeg positive hrE hrvE hQvE hu hw') (hrS.extend pre) (xr pre) (hQ.extend pre)
      (xQ pre) (hsP.extend pre) (hsN.extend pre) (hwd.extend pre) (hm.extend pre)
      (by rw [hm pre, hmv]) (iAR.extend pre) hAR (iCP.extend pre) (iLB.extend pre) (iV.extend pre) nd
    rw [xsP, xsN, xwd] at h
    exact h
  have iLC : ∀ (pre : List ℕ) (nd : Term), StableAt w nd (pre ++ env) →
      ImplZ3 w (pre ++ env) P (lcT pT (rT' bitsT) QT sPT sNT widthT mT arity
        (cpT' QT mT bitsT IBT sT arity varT) (lbT' QT bitsT IBT sT varT) varT nd)
        (lcN (P := P) (Q := Q) positive S start width CPf LBf V (nd.denote w (pre ++ env))) := by
    intro pre nd hnd
    have h := implZ3_lcT positive hP3 S (hp.extend pre) (xP pre) (hrS.extend pre) (xr pre)
      (hQ.extend pre) (xQ pre) (hsP.extend pre) (hsN.extend pre) (hwd.extend pre) (hm.extend pre)
      (by rw [hm pre, hmv]) (iAR.extend pre) hAR (iCP.extend pre) (iLB.extend pre) (iV.extend pre)
      hnd
    rw [xsP, xsN, xwd] at h
    exact h
  have iMC : ∀ (pre : List ℕ) (nd : Term), StableAt w nd (pre ++ env) →
      ImplZ4 w (pre ++ env) P (mcT pT (rT' bitsT) QT sPT sNT widthT
        (cpT' QT mT bitsT IBT sT arity varT) (lbT' QT bitsT IBT sT varT))
        ((fun _ν => mcN (P := P) r Q positive start width CPf LBf) (nd.denote w (pre ++ env))) := by
    intro pre nd _
    have h := implZ4_mcT positive hP3 (hp.extend pre) (xP pre) (hrS.extend pre) (xr pre)
      (hQ.extend pre) (xQ pre) (hsP.extend pre) (hsN.extend pre) (hwd.extend pre)
      (iCP.extend pre) (iLB.extend pre)
    rw [xsP, xsN, xwd] at h
    exact h
  have iEC : ImplZ4 w env P (evalCT pT (rT' bitsT) QT sPT sNT widthT mT arity
      (cpT' QT mT bitsT IBT sT arity varT) (lbT' QT bitsT IBT sT varT) varT)
      (evalCN (P := P) (Q := Q) S positive start width CPf LBf V) := by
    have h := implZ4_evalCT hP3 positive S hp hpv hrS hrv hQ hQv hsP hsN hwd hm hmv iAR hAR iCP iLB iV
    rw [hsPv, hsNv, hwdv] at h
    exact h
  have hD : StableAt w (powT (rT' bitsT) (mul (const 2) QT)) env :=
    StableAt.powT hrS ((stableAt_const _ _).mul hQ)
  have hDv : (powT (rT' bitsT) (mul (const 2) QT)).denote w env = r ^ (2 * Q) := by
    rw [powT_denote _ _ _ hrS, hrv]; simp [hQv]
  have hWS : StableAt w (mul (rT' bitsT) (rowsT' QT bitsT sPT sNT widthT copiesT)) env :=
    hrS.mul hrowsS
  have hWv : (mul (rT' bitsT) (rowsT' QT bitsT sPT sNT widthT copiesT)).denote w env =
      r * (copies * BC) := by rw [denote_mul, hrv, hrowsv]
  unfold systemCounterT
  rw [counterT_eq S (WSchedulePlacement.variableGroup S bits seed)
    (WSchedulePlacement.constraintGroup S bits seed)
    (fun _ => SpectralIndexing.rowAt r Q positive copies start width)
    (fun _ => SpectralIndexing.measurementRowNumber r Q positive copies start width)
    (fun node => WGroupedAccessorEvaluation.measurement S copyOf labelOf
      (WSchedulePlacement.variableGroup S bits seed node) start width)
    (fun node => WGroupedAccessorEvaluation.localCoefficient P positive S copyOf labelOf
      (nodeValues (P := P) Q) start width node)
    (fun _ => WGroupedAccessorEvaluation.measurementCoefficient P S copyOf labelOf start width)
    (WIncidenceEvaluation.finiteField P positive S copyOf labelOf (nodeValues (P := P) Q) start width)
    pT QT orderT B Cap Lb M K nT (rT' bitsT) (rowsT' QT bitsT sPT sNT widthT copiesT)
    (mul (rT' bitsT) (rowsT' QT bitsT sPT sNT widthT copiesT)) (powT (rT' bitsT) (mul (const 2) QT))
    mT _ _ arity (rowNumT (rowsT' QT bitsT sPT sNT widthT copiesT)) _ _ weight _ _ _ env
    hp hpv hQ hQv hQP ho hov (by omega) hn hnv hrS hrv hrowsS hrowsv hWS hWv hD hDv hm hmv pp
    (fun ν v => grpN Q bits (WSchedulePlacement.inputBits S) s 0 ν v)
    (fun ν e => grpN Q bits (WSchedulePlacement.inputBits S) s 1 ν e) AR
    (fun _ν g ρ => ρ + copies * BC * g)
    (fun _ν _g ρ v => measSignN (Q := Q) positive S start width CPf LBf V 0 ρ v)
    (fun _ν _g ρ v => measSignN (Q := Q) positive S start width CPf LBf V 1 ρ v) Wt
    (lcN (P := P) (Q := Q) positive S start width CPf LBf V)
    (fun _ν => mcN (P := P) r Q positive start width CPf LBf)
    (evalCN (P := P) (Q := Q) S positive start width CPf LBf V)
    iG iCG iAR iRN iCp iCn iWt iLC iMC iEC
    (fun ν hν v hv => (variableGroup_seedOf S Q bits s ⟨ν, hν⟩ ⟨v, hv⟩).symm)
    (fun ν hν e he => (constraintGroup_seedOf S Q bits s ⟨ν, hν⟩ ⟨e, he⟩).symm) hAR
    (fun ν hν g ρ hg hρ => (measurementRowNumber_rowAt positive copies start width ⟨g, hg⟩ ⟨ρ, hρ⟩).symm)
    (fun ν hν g ρ hg hρ v => measurement_eq_parts positive S start width copyOf labelOf CPf LBf V
      hCPinc hLBinc hV' _ ⟨g, hg⟩ ⟨ρ, hρ⟩ v) hWt
    (fun ν hν e i v he hi hv => lcN_spec positive S start width copyOf labelOf CPf LBf V hCPinc
      hLBinc hV' ⟨ν, hν⟩ ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨v, hv⟩)
    (fun ν hν e i g ρ he hi hg hρ => mcN_spec positive S start width copyOf labelOf CPf LBf hCPinc
      hLBinc ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨g, hg⟩ ⟨ρ, hρ⟩)
    (fun e i v x he hi hv => evalCN_spec S positive start width copyOf labelOf CPf LBf V hCPinc
      hLBinc hV' ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨v, hv⟩ x) hP3]
  exact WConcreteCountingLoop.countModP_correct P positive (two_ne_zero_of_lt hP3) S ⟨0, npos⟩
    copyOf labelOf (placement_injective_S S Q bits s hbal)
    (WSchedulePlacement.variableGroup S bits seed) (WSchedulePlacement.constraintGroup S bits seed)
    (nodeValues (P := P) Q) (nodeValues_injective hQP) (nodeValues_ne_zero hQP) k large start width
    small below (fun _ _ => rfl) (fun _ _ => rfl) capacity no_alias

end NtimeDspace.ProgTerm
