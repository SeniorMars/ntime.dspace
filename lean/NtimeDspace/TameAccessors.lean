import NtimeDspace.TameArity
import NtimeDspace.TameWeight
import NtimeDspace.TameNet
import NtimeDspace.TameLocal
import NtimeDspace.TameParams
import NtimeDspace.DeciderValues
import NtimeDspace.TameCounterAt

/-!
# Tiers of the decider's network accessors

`tm_accessors`: inside the loops (an extension `env` of `[n]`), for a stable
schedule term of tier `1`, the arity, the ports, the weights and `2^arity`
of the decider's network have tier `1`, given numeric facts about `n` and `L`
and a degree bound for the schedule.
-/

namespace NtimeDspace.ProgTerm

open Term Budget Parameters Cslib.Complexity.CountingSimulation LocalSim Turing

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool} {L : ℕ}

theorem sgnCode_le (x : SignType) : sgnCode x ≤ 2 := by cases x <;> simp [sgnCode]

theorem wCode_le (x : Option (Option Bool)) : wCode x ≤ 3 := by
  cases x with
  | none => simp [wCode]
  | some c => have := cc_lt c; simp only [wCode]; omega

/-- The machine's tables have entries at most `s + 3`. -/
theorem tables_le (x : ℕ) : fSt e machine x ≤ s + 3 ∧ fIn e machine x ≤ s + 3 ∧
    fOut e machine x ≤ s + 3 ∧ fEmit x ≤ s + 3 ∧ fW e machine x ≤ s + 3 ∧ fM e machine x ≤ s + 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := stc_lt e (actOf e machine x).state; unfold fSt; omega
  · have := sgnCode_le (actOf e machine x).inputTape; unfold fIn; omega
  · have := cc_lt (actOf e machine x).output; unfold fOut; omega
  · have := trc_lt ((trOf (x % 3)).emit (cellOf (x / 3))); unfold fEmit; omega
  · unfold fW; split
    · have := wCode_le ((actOf e machine (x % keyCount k s)).workTapes ⟨x / keyCount k s, by omega⟩).1
      omega
    · omega
  · unfold fM; split
    · have := sgnCode_le ((actOf e machine (x % keyCount k s)).workTapes ⟨x / keyCount k s, by omega⟩).2
      omega
    · omega

set_option maxHeartbeats 1000000 in
-- Instantiating the accessor lemmas involves many large terms.
theorem tm_accessors {env : List ℕ} {σT : Term} {D0 : ℕ}
    (he : Ext L env [w.length])
    (hL : 8 ≤ L) (hn : w.length < 2 ^ L) (hcube : NN k s c w.length ^ 3 < 2 ^ L)
    (hconst : 4 * k + s + c + 100 < 2 ^ L) (hc : 2 ≤ c)
    (hlarge : ParameterChoice.cost 6 ≤ lgN k s c w.length) (hN72 : 72 ≤ NN k s c w.length)
    (hkey : keyCount k s * k + keyCount k s + width k + 3 ^ k < 2 ^ L)
    (hRw : LocalSim.radix (blockLength (clk c w.length)) w.length s ^ width k < 2 ^ L)
    (h3b : 3 ^ (3 * blockLength (clk c w.length)) < 2 ^ L)
    (hccv : (s + 1) * (blockLength (clk c w.length) ^ (k + 1) * 3) < 2 ^ L)
    (hm0 : MultiTapePTM.letterBits k s (blockLength (clk c w.length)) < L)
    (hσ : Tm w L 1 σT env) (hσs : StableAt w σT env)
    (hD0 : D0 < L)
    (hdeg : ∀ v < verticesN k s (tN c w.length),
      (MultiTapePTM.explicitPortsNum k (numBlocks (clk c w.length)) (MultiTapePTM.letterBits k s (blockLength (clk c w.length)))
        (σT.denote w env) v).length ≤ D0) :
    TmF w L (arityAt k s c (lvl 0) σT) 4 1 env ∧
      TmF2 w L (portAt k s c (lvl 0) σT) 4 4 1 env ∧
      TmF2v w L (weightAt k s c e machine (lvl 0) σT) 4 (verticesN k s (tN c w.length)) 4 1 env ∧
      TmFv w L (fun e' => pow2 (arityAt k s c (lvl 0) σT e')) 4 (verticesN k s (tN c w.length)) 1 env := by
  set n := w.length with hn_def
  set b := blockLength (clk c n) with hb_def
  have hL2 : 2 ≤ L := by omega
  have hp3k : 0 < 3 ^ k := by positivity
  have hp4b : 0 < 3 ^ (4 * b) := by positivity
  have hp3b : 0 < 3 ^ (3 * b) := by positivity
  have hpbk : 0 ≤ b ^ (k + 1) := Nat.zero_le _
  have hxs0 : StableAt w (lvl 0) [n] := hx_stable
  have hxv0 : (lvl 0).denote w [n] = n := hx_value
  have hxs : StableAt w (lvl 0) env := hxs0.extend' he
  have hxv : (lvl 0).denote w env = n := by rw [hxs0.extend'_eq he, hxv0]
  have hconst' : 4 * k + s + 100 < 2 ^ L := by omega
  have hq := (tm_numBlocksT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hb := (tm_blockLenT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hqs := StableAt.numBlocksT (c := c) hxs hxv
  have hqv := denote_numBlocksT (c := c) hxs hxv
  have hbs := StableAt.blockLenT (c := c) hxs hxv
  have hbv : (blockLenT c (lvl 0)).denote w env = b := denote_blockLenT (c := c) hxs hxv
  have hbpos : 0 < b := Cslib.Complexity.CountingSimulation.one_le_blockLength _
  have hbp : Pos w L (blockLenT c (lvl 0)) env := Pos.of_stable hbs (by rw [hbv]; exact hbpos)
  have hbm : b ≤ MultiTapePTM.letterBits k s b := by
    unfold MultiTapePTM.letterBits; nlinarith
  have hbL : b < L := by omega
  have hRle : LocalSim.radix b n s ≤ LocalSim.radix b n s ^ width k := by
    have : 0 < LocalSim.radix b n s := by unfold LocalSim.radix; positivity
    exact Nat.le_self_pow (by unfold width; omega) _
  have hR := (tm_localRadixT (w := w) hL hn hcube hconst hc hlarge hN72 (lt_of_le_of_lt hRle hRw)).ext he
  have hRs := StableAt.localRadixT (s := s) (c := c) hxs hxv
  have hRv := denote_localRadixT (s := s) (c := c) hxs hxv
  have hRpos : Pos w L (localRadixT s c (lvl 0)) env :=
    Pos.of_stable hRs (by rw [hRv]; unfold LocalSim.radix; positivity)
  have hN : Tm w L 1 (lvl 0) env := (tm_x hn).ext he
  have hinit : LocalSim.stc e (some machine.initial) < 2 ^ L := lt_of_lt_of_le (stc_lt e _) (by omega)
  have hwk : width k < 2 ^ L := by omega
  have hW : Le w L (const (width k)) (width k) env := Le.of_stable (stableAt_const _ _) le_rfl
  have hpowR : TmFv w L (fun i => powT (localRadixT s c (lvl 0)) i) 4 (width k) 1 env :=
    fun env' he' i hi his hiv => t_powT_lt (hR.ext he') (hRs.extend' he') hi (by omega) hiv (by omega)
      le_rfl (by rw [hRs.extend'_eq he', hRv, one_mul]; exact hRw) (by omega) (by omega)
  have h3 : TmFv w L (fun j => powT (const 3) j) 8 (3 * b) 1 env :=
    fun env' he' j hj hjs hjv => t_powT_lt (t_const (by omega)) (stableAt_const _ _) hj (by omega) hjv
      (by omega) le_rfl (by rw [denote_const, one_mul]; exact h3b) (by omega) (by omega)
  have h3bLe : Le w L (mul (const 3) (blockLenT c (lvl 0))) (3 * b) env :=
    Le.of_stable ((stableAt_const _ _).mul hbs) (by rw [denote_mul, denote_const, hbv])
  have hbk : b ^ (k + 1) < 2 ^ L := by
    have h1 : b ^ (k + 1) ≤ b ^ (k + 1) * 3 := Nat.le_mul_of_pos_right _ (by norm_num)
    have h2 := Nat.le_mul_of_pos_left (b ^ (k + 1) * 3) (by omega : 0 < s + 1)
    omega
  have hcr : Tm w L 1 (powT (blockLenT c (lvl 0)) (const (k + 1))) env :=
    tm_powT_stable hL hb hbs (t_const (by omega)) (stableAt_const _ _) (by omega) (by omega)
      (by rw [hbv, denote_const]; exact hbk)
  have hcc : Tm w L 1 (ccountT k s (blockLenT c (lvl 0))) env := by
    refine tm_retier (d := 3) (by unfold ccountT cradT; tame) ((stableAt_const _ _).mul
      ((hbs.powT (stableAt_const _ _)).mul (stableAt_const _ _))) ?_
    simp only [ccountT, cradT, denote_mul, denote_const, powT_denote _ _ _ hbs, hbv, one_mul]
    exact hccv
  have h2b : Tm w L 1 (pow2 (blockLenT c (lvl 0))) env :=
    t_pow2_stable hb (by omega) hbs (by rw [hbv, one_mul]; exact hbL) (by omega) hL2
  have hfSt : TmF w L (tabT (fSt e machine) (keyCount k s)) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by have := (tables_le (e := e) (machine := machine) i).1; omega)
  have hfIn : TmF w L (tabT (fIn e machine) (keyCount k s)) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by have := (tables_le (e := e) (machine := machine) i).2.1; omega)
  have hfOut : TmF w L (tabT (fOut e machine) (keyCount k s)) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by
      have := (tables_le (e := e) (machine := machine) i).2.2.1; omega)
  have hfEmit : TmF w L (tabT fEmit 9) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by
      have := (tables_le (e := e) (machine := machine) i).2.2.2.1; omega)
  have hfW : TmF w L (tabT (fW e machine) (keyCount k s * k)) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by
      have := (tables_le (e := e) (machine := machine) i).2.2.2.2.1; omega)
  have hfM : TmF w L (tabT (fM e machine) (keyCount k s * k)) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by
      have := (tables_le (e := e) (machine := machine) i).2.2.2.2.2; omega)
  have hK : Le w L (const k) k env := Le.of_stable (stableAt_const _ _) le_rfl
  have hpow3 : TmFv w L (fun h => powT (const 3) h) 4 k 1 env :=
    fun env' he' j hj hjs hjv => t_powT_lt (t_const (by omega)) (stableAt_const _ _) hj (by omega) hjv
      (by omega) le_rfl (by rw [denote_const, one_mul]; omega) (by omega) (by omega)
  have hrun := tm_runT (e := e) (machine := machine) (bT := blockLenT c (lvl 0)) hL hR hRpos hN hb
    hconst' hwk (by omega) (by omega) hW hpowR hK hpow3 hfSt hfIn hfOut hfEmit hfW hfM
  have hlet := tm_pow2_letter (w := w) (env := env) hm0 hL
  have hletLe : Le w L (letterBitsT k s (blockLenT c (lvl 0))) (MultiTapePTM.letterBits k s b) env :=
    Le.of_stable ((stableAt_const _ _).mul hbs) (by
      rw [letterBitsT, denote_mul, denote_const, hbv]; unfold MultiTapePTM.letterBits; exact le_rfl)
  have hm0' : MultiTapePTM.letterBits k s b < 2 ^ L := lt_trans hm0 Nat.lt_two_pow_self
  have hm1 := tm_letterBitsT hL hR hRpos hN hq hb hbs hbv hbpos hbp hσ hconst' hinit hwk hW hpowR
    h3 h3bLe hcr hcc h2b hrun hlet hletLe hm0'
  have hpa := tm_pow2_arityNT (mv := verticesN k s (tN c n)) hL hq hb hσ hqs hbs hσs
    (by rw [hqv, hbv]; exact hdeg) hD0 hconst'
  have hwt := tm_weightNT1 hL hR hRpos hN hq hb hbs hbv hbpos hbp hσ hconst' hinit hwk hW hpowR
    h3 h3bLe hcr hcc h2b hrun hlet hletLe hm0' hpa (Nat.pow_lt_pow_right (by norm_num) hbL)
  have hEs : StableAt w (edgesT k s (numBlocksT c (lvl 0)) (blockLenT c (lvl 0))) env := fun extra => by
    rw [denote_edgesT, denote_edgesT, hqs extra, hbs extra]
  have hEv : (edgesT k s (numBlocksT c (lvl 0)) (blockLenT c (lvl 0))).denote w env = NN k s c n := by
    rw [denote_edgesT, hqv, hbv]
  have hE : (edgesT k s (numBlocksT c (lvl 0)) (blockLenT c (lvl 0))).denote w env *
      (edgesT k s (numBlocksT c (lvl 0)) (blockLenT c (lvl 0))).denote w env < 2 ^ L := by
    rw [hEv]
    have : NN k s c n * NN k s c n ≤ NN k s c n ^ 3 := by
      rw [show NN k s c n ^ 3 = NN k s c n * NN k s c n * NN k s c n by ring]
      exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hcst : 4 * k + 100 < 2 ^ L := by omega
  exact ⟨tm_arityNT1 hL hq hb hσ hm1 hcst hEs hE, tm_portAtT1 hL hq hb hσ hm1 hcst hEs hE, hwt, hpa⟩

end NtimeDspace.ProgTerm
