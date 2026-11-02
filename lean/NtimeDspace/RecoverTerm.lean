import NtimeDspace.WeightTerm
import NtimeDspace.WScalarRecoveryLoop

/-!
# Hermite recovery as a term

`recoverT` computes `WScalarRecoveryLoop.recover` with the node values
`node + 1`: the product `Ω(0)` and the double sum over nodes and nonzero
residues of `z^(p-J) · weight(node, z) · data(node, z)`, with the weight given
by `weightT`.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- Flat weights read only the supplied factor slots. -/
theorem flatWeightEvaluation_congr {P : ℕ} [Fact P.Prime] (f g : IntervalCoefficients.Factors P)
    (count order : ℕ) (z : ZMod P) (agree : ∀ i < count, f i = g i) :
    FlatHermite.flatWeightEvaluation f count order z =
      FlatHermite.flatWeightEvaluation g count order z := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [agree i (Finset.mem_range.mp hi)]

/-- The node skipping `node`: `s` below it, `s + 1` above. -/
def skipT (nd s : Term) : Term := ite (lt s nd) s (add s (const 1))

/-- The factor constant of slot `slot` for node `nd` with node values `· + 1`. -/
def factorAT (p nd slot : Term) : Term :=
  ite (eqT slot (const 0)) (mod (add nd (const 1)) p)
    (mod (sub (add nd p) (skipT nd (sub slot (const 1)))) p)

/-- The factor multiplicity of slot `slot`. -/
def factorMT (order slot : Term) : Term := ite (eqT slot (const 0)) (const 1) order

def skipSpec (node s : ℕ) : ℕ := if s < node then s else s + 1

def factorASpec (P node slot : ℕ) : ℕ :=
  if slot = 0 then (node + 1) % P else (node + P - skipSpec node (slot - 1)) % P

def factorMSpec (J slot : ℕ) : ℕ := if slot = 0 then 1 else J

theorem factorAT_implements (p nd : Term) (base : List ℕ) (P node : ℕ)
    (hp : StableAt w p base) (hpv : p.denote w base = P)
    (hnd : StableAt w nd base) (hndv : nd.denote w base = node) :
    ImplementsFun w base (factorAT p nd) (factorASpec P node) := by
  intro extra a ha
  have hp' := hp.extend extra
  have hnd' := hnd.extend extra
  refine ⟨?_, ?_⟩
  · simp only [factorAT, skipT, denote_ite, denote_eqT, denote_const, denote_mod, denote_add,
      denote_sub, denote_lt, hp extra, hpv, hnd extra, hndv, factorASpec, skipSpec]
    by_cases h : a.denote w (extra ++ base) = 0
    · simp [h]
    · by_cases h2 : a.denote w (extra ++ base) - 1 < node <;> simp [h, h2]
  · exact (ha.eqT (stableAt_const _ _)).ite ((hnd'.add (stableAt_const _ _)).mod hp')
      (((hnd'.add hp').sub ((ha.sub (stableAt_const _ _)).lt hnd' |>.ite
        (ha.sub (stableAt_const _ _)) ((ha.sub (stableAt_const _ _)).add
          (stableAt_const _ _)))).mod hp')

theorem factorMT_implements (order : Term) (base : List ℕ) (J : ℕ)
    (ho : StableAt w order base) (hov : order.denote w base = J) :
    ImplementsFun w base (factorMT order) (factorMSpec J) := by
  intro extra a ha
  refine ⟨?_, (ha.eqT (stableAt_const _ _)).ite (stableAt_const _ _) (ho.extend extra)⟩
  simp only [factorMT, denote_ite, denote_eqT, denote_const, ho extra, hov, factorMSpec]
  by_cases h : a.denote w (extra ++ base) = 0 <;> simp [h]

variable {P : ℕ} [Fact P.Prime]

/-- The node values `node + 1`. -/
def nodeValues (Q : ℕ) : Fin Q → ZMod P := fun i => ((i : ℕ) + 1 : ℕ)

theorem factorSpec_eq (Q J node : ℕ) (hnode : node < Q) (hQ : Q < P) (slot : ℕ)
    (hslot : slot < Q) :
    (((factorASpec P node slot : ℕ) : ZMod P), factorMSpec J slot) =
      WScalarRecoveryLoop.factorAccessor (nodeValues (P := P) Q) ⟨node, hnode⟩ J slot := by
  rcases slot with _ | slot
  · simp [factorASpec, factorMSpec, WScalarRecoveryLoop.factorAccessor, nodeValues]
  · have hin : slot < Q - 1 := by omega
    simp only [factorASpec, factorMSpec, WScalarRecoveryLoop.factorAccessor, dif_pos hin,
      nodeValues, WScalarRecoveryLoop.skipNode, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false,
      skipSpec]
    have hskip : (if slot < node then slot else slot + 1) ≤ node + P := by split_ifs <;> omega
    refine Prod.ext ?_ rfl
    simp only [ZMod.natCast_mod]
    rw [Nat.cast_sub hskip]
    split_ifs <;> push_cast <;> simp [ZMod.natCast_self]

theorem factorSpec_valid (Q J node : ℕ) (hnode : node < Q) (hQ : Q < P) (hJ : 0 < J) :
    IntervalCoefficients.Valid (fun i => (((factorASpec P node i : ℕ) : ZMod P),
      factorMSpec J i)) Q := by
  intro slot hslot
  have e := factorSpec_eq (P := P) Q J node hnode hQ slot hslot
  refine ⟨?_, ?_⟩
  · show ((factorASpec P node slot : ℕ) : ZMod P) ≠ 0
    rw [show ((factorASpec P node slot : ℕ) : ZMod P) = (WScalarRecoveryLoop.factorAccessor
      (nodeValues (P := P) Q) ⟨node, hnode⟩ J slot).1 from congrArg Prod.fst e]
    rcases slot with _ | slot
    · simp only [WScalarRecoveryLoop.factorAccessor, nodeValues]
      rw [Ne, ← Nat.cast_zero, ZMod.natCast_eq_natCast_iff', Nat.zero_mod,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · have hin : slot < Q - 1 := by omega
      simp only [WScalarRecoveryLoop.factorAccessor, dif_pos hin, nodeValues]
      rw [sub_ne_zero, Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt]
      · simp only [WScalarRecoveryLoop.skipNode]; split_ifs <;> omega
      · simp only [WScalarRecoveryLoop.skipNode]; split_ifs <;> omega
  · simp only [factorMSpec]; split_ifs <;> omega

/-- `Ω(0) = ∏_{node<Q} (-(node+1))^J` modulo `p`. -/
def omegaT (p Q order : Term) : Term :=
  Term.prodMod p Q fun nd => powModT p (sub p (add nd (const 1))) order

theorem omegaT_denote (p Q order : Term) (env : List ℕ)
    (hp : StableAt w p env) (hpv : p.denote w env = P) (hQ : StableAt w Q env)
    (hQP : Q.denote w env < P) (ho : StableAt w order env) :
    ((omegaT p Q order).denote w env : ZMod P) =
      WScalarRecoveryLoop.omegaZero (nodeValues (P := P) (Q.denote w env)) (order.denote w env) := by
  rw [omegaT, denote_prodModZ p Q _ env P (fun nd => (-(((nd + 1 : ℕ)) : ZMod P)) ^
    order.denote w env) hp hpv (fun acc nd hnd => ?_), WScalarRecoveryLoop.omegaZero,
    WGroupedAssignmentEvaluation.scanProduct_correct, mul_one, Finset.prod_range]
  · rfl
  · rw [powModT_denote p _ order _ P (hp.extend₂ acc nd) (by rw [hp.cons₂]; exact hpv)
      (((hp.extend₂ acc nd).sub ((stableAt_index env acc nd).add (stableAt_const _ _)))),
      ho.cons₂]
    simp only [denote_sub, denote_add, denote_const, hp.cons₂, hpv, denote_lvl_index]
    rw [Nat.cast_sub (by omega)]
    simp

/-- Hermite recovery: `Ω(0) · ∑_{node} ∑_{z≠0} z^(p-J) · weight(node,z) · data(node,z)`. -/
def recoverT (p Q order : Term) (dataT : Term → Term → Term) : Term :=
  mod (mul (omegaT p Q order) (Term.sumMod p Q fun nd => Term.sumMod p (sub p (const 1)) fun idx =>
    mod (mul (mod (mul (powModT p (add idx (const 1)) (sub p order))
      (weightT p order Q (factorAT p nd) (factorMT order) (add idx (const 1)))) p)
      (dataT nd (add idx (const 1)))) p)) p

/-- **The recovery term computes `WScalarRecoveryLoop.recover`** with node values
`node + 1`, for any data term implementing `data`. -/
theorem recoverT_denote (p Q order : Term) (dataT : Term → Term → Term) (env : List ℕ)
    (hP : 2 < P) (QN J : ℕ)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hQ : StableAt w Q env) (hQv : Q.denote w env = QN) (hQP : QN < P)
    (ho : StableAt w order env) (hov : order.denote w env = J) (hJ : 0 < J) (hJP : J ≤ P)
    (data : Fin QN → ZMod P → ZMod P)
    (hdata : ∀ (pre : List ℕ) (nd zt : Term), StableAt w nd (pre ++ env) →
      StableAt w zt (pre ++ env) → ∀ h : nd.denote w (pre ++ env) < QN,
        ((dataT nd zt).denote w (pre ++ env) : ZMod P) =
          data ⟨nd.denote w (pre ++ env), h⟩ (zt.denote w (pre ++ env) : ZMod P)) :
    ((recoverT p Q order dataT).denote w env : ZMod P) =
      WScalarRecoveryLoop.recover (nodeValues (P := P) QN) J data := by
  have hom := omegaT_denote p Q order env hp hpv hQ (by rw [hQv]; exact hQP) ho
  rw [hQv, hov] at hom
  let inner : ℕ → ℕ → ZMod P := fun nd idx =>
    if h : nd < QN then
      (((idx + 1 : ℕ)) : ZMod P) ^ (P - J) *
        WScalarRecoveryLoop.weight (nodeValues (P := P) QN) ⟨nd, h⟩ J ((idx + 1 : ℕ) : ZMod P) *
          data ⟨nd, h⟩ ((idx + 1 : ℕ) : ZMod P)
    else 0
  simp only [recoverT, denote_mod, denote_mul, ZMod.natCast_mod, Nat.cast_mul, hpv, hom]
  rw [denote_sumModZ p Q _ env P (fun nd => ∑ idx ∈ Finset.range (P - 1), inner nd idx) hp hpv
    (fun acc nd hnd => ?_), hQv, WScalarRecoveryLoop.recover,
    WGroupedAssignmentEvaluation.scanSum_correct, add_zero, Finset.sum_range]
  · congr 1
    refine Finset.sum_congr rfl fun nd _ => ?_
    rw [WScalarRecoveryLoop.sumNonzero, WGroupedAssignmentEvaluation.scanSum_correct, add_zero,
      Finset.sum_range]
    refine Finset.sum_congr rfl fun idx _ => ?_
    simp only [inner, dif_pos nd.isLt, WScalarRecoveryLoop.residue]
  · -- the body at node `nd`
    have hnd' : nd < QN := by rw [← hQv]; exact hnd
    set env1 := acc :: nd :: env with henv1
    have hp1 : StableAt w p env1 := hp.extend₂ acc nd
    have hpv1 : p.denote w env1 = P := by rw [hp.cons₂]; exact hpv
    rw [denote_sumModZ p _ _ env1 P (fun idx => inner nd idx) hp1 hpv1 (fun acc' idx hidx => ?_)]
    · simp only [denote_sub, denote_const, hpv1]
    · set env2 := acc' :: idx :: env1 with henv2
      have hidx' : StableAt w (lvl env1.length) env2 := stableAt_index env1 acc' idx
      have hz : StableAt w (add (lvl env1.length) (const 1)) env2 :=
        hidx'.add (stableAt_const _ _)
      have hzv : (add (lvl env1.length) (const 1)).denote w env2 = idx + 1 := by simp [env2]
      have hpv2 : p.denote w env2 = P := by rw [hp1.cons₂]; exact hpv1
      have hnd1 : StableAt w (lvl env.length) env1 := stableAt_index env acc nd
      have hndv1 : (lvl env.length).denote w env1 = nd := denote_lvl_index env acc nd
      have hA := factorAT_implements p (lvl env.length) env1 P nd hp1 hpv1 hnd1 hndv1
      have hM := factorMT_implements order env1 J (ho.extend₂ acc nd)
        (by rw [ho.cons₂]; exact hov)
      have hw := weightT_denote p order Q (factorAT p (lvl env.length)) (factorMT order)
        (add (lvl env1.length) (const 1)) [acc', idx] P hP (factorASpec P nd) (factorMSpec J)
        hA hM (hp1.extend₂ acc' idx) hpv2 ((ho.extend₂ acc nd).extend₂ acc' idx)
        ((hQ.extend₂ acc nd).extend₂ acc' idx) hz
        (by show order.denote w ([acc', idx, acc, nd] ++ env) ≤ P; rw [ho, hov]; exact hJP)
        (by
          show IntervalCoefficients.Valid _ (Q.denote w ([acc', idx, acc, nd] ++ env))
          rw [hQ, hQv]
          exact factorSpec_valid QN J nd hnd' hQP hJ)
      simp only [List.cons_append, List.nil_append] at hw
      have hd := hdata [acc', idx, acc, nd] (lvl env.length) (add (lvl env1.length) (const 1))
        (hnd1.extend [acc', idx]) hz (by
          show (lvl env.length).denote w env2 < QN
          simp [env2, env1, Term.denote_lvl, Nat.add_assoc]; exact hnd')
      simp only [List.cons_append, List.nil_append] at hd
      have hov2 : order.denote w env2 = J := by
        show order.denote w ([acc', idx, acc, nd] ++ env) = J; rw [ho, hov]
      have hQ2 : Q.denote w (acc' :: idx :: acc :: nd :: env) = QN := by
        show Q.denote w ([acc', idx, acc, nd] ++ env) = QN; rw [hQ, hQv]
      have ho2 : order.denote w (acc' :: idx :: acc :: nd :: env) = J := hov2
      have hndv2 : (lvl env.length).denote w (acc' :: idx :: acc :: nd :: env) = nd := by
        simp [Term.denote_lvl, Nat.add_assoc]
      simp only [denote_mod, denote_mul, ZMod.natCast_mod, Nat.cast_mul, hpv2]
      rw [powModT_denote p _ _ env2 P (hp1.extend₂ acc' idx) hpv2 hz, hzv]
      simp only [denote_sub, hpv2, hov2]
      rw [henv2, henv1, hw, hd, hQ2, ho2]
      have hfin : (⟨(lvl env.length).denote w (acc' :: idx :: acc :: nd :: env), by
          rw [hndv2]; exact hnd'⟩ : Fin QN) = ⟨nd, hnd'⟩ := Fin.ext hndv2
      have hzv' : (add (lvl (acc :: nd :: env).length) (const 1)).denote w
          (acc' :: idx :: acc :: nd :: env) = idx + 1 := hzv
      simp only [inner, dif_pos hnd', hzv']
      rw [hfin, WScalarRecoveryLoop.weight, flatWeightEvaluation_congr _ _ QN J _ (fun i hi =>
        factorSpec_eq QN J nd hnd' hQP i hi)]
      simp only [Term.denote_add, Term.denote_const, Term.denote_lvl, env1, List.length_cons,
        Nat.add_assoc, Nat.add_sub_cancel_left]
      simp

end NtimeDspace.ProgTerm
