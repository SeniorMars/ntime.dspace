import NtimeDspace.TameCounter
import NtimeDspace.TameSeedAt
import NtimeDspace.TameGroup
import NtimeDspace.TameNet
import NtimeDspace.TameBadCount
import NtimeDspace.BadCountBridge
import NtimeDspace.Budget

/-!
# Tier of the decider's counter at one schedule and prime

`tm_counterAt`: inside the loops (an extension `env` of `[n]`), for a stable
schedule `σ` and a prime `p > 4N²`, the counter has tier `1`, given the tiers
of the network accessors for `σ` and the numeric facts of the budget.
-/

namespace NtimeDspace.ProgTerm

open Term Budget Parameters Cslib.Complexity.CountingSimulation LocalSim Placement WeightedSystem
  NetworkSystem

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : Turing.MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool} {L : ℕ}

/-- Stable powers have tier `1` when their values are below `2^L`. -/
theorem tm_powT_stable {x y : Term} {env : List ℕ} {dx dy : ℕ} (hL : 8 ≤ L)
    (hx : Tm w L dx x env) (hxs : StableAt w x env) (hy : Tm w L dy y env) (hys : StableAt w y env)
    (hdy : dy ≤ 32) (hdx : dx ≤ 100)
    (hv : x.denote w env ^ y.denote w env < 2 ^ L) : Tm w L 1 (powT x y) env :=
  t_powT hx hxs hy hdy le_rfl (by omega) (fun pre _ => by rw [hxs pre, hys pre, one_mul]; exact hv)
    (by omega) (by omega)

set_option maxHeartbeats 1000000 in
-- Instantiating the counter's tier lemma involves many large terms.
theorem tm_counterAt {env : List ℕ} {σT pT : Term} {σ0 : ℕ}
    (he : Ext L env [w.length])
    (hL : 8 ≤ L) (hn : w.length < 2 ^ L) (hcube : NN k s c w.length ^ 3 < 2 ^ L)
    (hconst : 4 * k + s + c + 100 < 2 ^ L) (hc : 2 ≤ c)
    (hlarge : ParameterChoice.cost 6 ≤ lgN k s c w.length) (hN72 : 72 ≤ NN k s c w.length)
    (hD : (2 ^ kN k s c w.length * 2 ^ kN k s c w.length) ^ Q (kN k s c w.length) < 2 ^ L)
    (hDr : (2 ^ kN k s c w.length) ^ (2 * Q (kN k s c w.length)) < 2 ^ L)
    (hlim : SupportBudget.limit (NN k s c w.length) (kN k s c w.length) + 1 < L)
    (hblk : 2 ^ (2 * blk (Q (kN k s c w.length)) (kN k s c w.length)
      ((max (NN k s c w.length) (verticesN k s (tN c w.length))).log2 + 1)) < 2 ^ L)
    (hgroup : 2 * NN k s c w.length / 2 ^ kN k s c w.length < L)
    (hqL : q (NN k s c w.length) (kN k s c w.length) < L)
    (htup : (2 * (2 ^ kN k s c w.length) ^ (2 * Q (kN k s c w.length)) + 1) ^
      tupleWidth k s c w.length < 2 ^ L)
    (hσ : Tm w L 1 σT env) (hσs : StableAt w σT env) (hσv : σT.denote w env = σ0)
    (hp : Tm w L 1 pT env) (hppos : Pos w L pT env)
    (hex : ∀ pos : 0 < (blockNetworkOf machine e (w, clk c w.length, σ0)).2.numEdges,
      ∃ sd < 2 ^ (2 * blk (Q (kp k s c w.length)) (kp k s c w.length)
        (WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (w, clk c w.length, σ0)).2 pos))),
        balN (toSystem (blockNetworkOf machine e (w, clk c w.length, σ0)).2 pos)
          (Q (kp k s c w.length)) (kp k s c w.length) sd)
    (har : TmF w L (arityAt k s c (lvl 0) σT) 4 1 env)
    (hvar : TmF2 w L (portAt k s c (lvl 0) σT) 4 4 1 env)
    (hwt : TmF2v w L (weightAt k s c e machine (lvl 0) σT) 4 (verticesN k s (tN c w.length)) 4 1 env)
    (hpa : TmFv w L (fun e' => pow2 (arityAt k s c (lvl 0) σT e')) 4 (verticesN k s (tN c w.length)) 1 env) :
    Tm w L 1 (counterAt k s c e machine (lvl 0) σT pT) env := by
  set n := w.length with hn_def
  have hL2 : 2 ≤ L := by omega
  -- the input length and the parameters, at `[n]` and at `env`
  have hxs0 : StableAt w (lvl 0) [n] := hx_stable
  have hxv0 : (lvl 0).denote w [n] = n := hx_value
  have hxs : StableAt w (lvl 0) env := hxs0.extend' he
  have hxv : (lvl 0).denote w env = n := by rw [hxs0.extend'_eq he, hxv0]
  have hpos : 0 < edgesN k s (clk c n) := by simp only [NN, tN] at hN72; omega
  have hN := (tm_edgesNT (w := w) hL hn hcube hconst).ext he
  have hk := (tm_kpT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hr := (tm_spT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hQ := (tm_QpT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hRt := (tm_RpT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hq1 := (tm_qpT1 (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hq := (tm_qpT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hlg := (tm_lgNT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hM := (tm_radixPT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hK := (tm_limitT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hV := (tm_verticesT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hIB := (tm_inputBitsT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hsP := (tm_startPT (w := w) hL hn hcube hconst hc hlarge hN72).ext he
  have hcp := (tm_copiesT (w := w) hL hn hcube hconst hc hlarge hN72 hD).ext he
  -- stability and values at `env`
  have hks := StableAt.kpT (k := k) (s := s) (c := c) hxs hxv
  have hkv := denote_kpT (k := k) (s := s) (c := c) hxs hxv
  have hQs : StableAt w (QpT k s c (lvl 0)) env := fun extra => by
    rw [denote_QpT (hxs.extend extra) (by rw [hxs extra, hxv]), denote_QpT hxs hxv]
  have hQv := denote_QpT (k := k) (s := s) (c := c) hxs hxv
  have hNs := StableAt.edgesNT (k := k) (s := s) (c := c) hxs hxv
  have hNv := denote_edgesNT (k := k) (s := s) (c := c) hxs hxv
  have hVs := StableAt.verticesT (k := k) (s := s) (c := c) hxs hxv
  have hVv := denote_verticesT (k := k) (s := s) (c := c) hxs hxv
  have hIBs : StableAt w (inputBitsT k s c (lvl 0)) env := fun extra => by
    rw [denote_inputBitsT (hxs.extend extra) (by rw [hxs extra, hxv]) hpos, denote_inputBitsT hxs hxv hpos]
  have hIBv := denote_inputBitsT (k := k) (s := s) (c := c) hxs hxv hpos
  have hkL : (kpT k s c (lvl 0)).denote w env ≤ L := by
    have h1 := kN_le_lgN hL hn hcube hconst hc hlarge hN72
    have h2 := lgN_lt_L hL hn hcube hconst hc hlarge hN72
    rw [hkv]; simp only [NN, tN, lgN, kN, kp] at *; omega
  -- the label space and the powers of `r`
  have hrs : StableAt w (pow2 (kpT k s c (lvl 0))) env := hks.pow2
  have hrv : (pow2 (kpT k s c (lvl 0))).denote w env = 2 ^ kN k s c n := by rw [denote_pow2, hkv]
  have hls : Tm w L 1 (powT (mul (pow2 (kpT k s c (lvl 0))) (pow2 (kpT k s c (lvl 0)))) (QpT k s c (lvl 0))) env :=
    tm_powT_stable hL (t_mul hr hr (by omega)) (hrs.mul hrs) hQ hQs (by omega) (by omega)
      (by rw [denote_mul, hrv, hQv]; exact hD)
  have hpw : Tm w L 1 (powT (pow2 (kpT k s c (lvl 0))) (mul (const 2) (QpT k s c (lvl 0)))) env :=
    tm_powT_stable hL hr hrs (t_mul (t_const (lit_lt_two_pow (by omega) hL2)) hQ (by omega))
      ((stableAt_const _ _).mul hQs) (by omega) (by omega)
      (by rw [hrv, denote_mul, denote_const, hQv]; exact hDr)
  have hKs : StableAt w (limitT k s c (lvl 0)) env := fun extra => by
    rw [denote_limitT (hxs.extend extra) (by rw [hxs extra, hxv]), denote_limitT hxs hxv]
  have hKv := denote_limitT (k := k) (s := s) (c := c) hxs hxv
  have hK1 : Tm w L 1 (pow2 (add (limitT k s c (lvl 0)) (const 1))) env :=
    t_pow2_stable (t_add hK (t_const (lit_lt_two_pow (by omega) hL2)) (by omega) (by omega)) (by omega)
      (hKs.add (stableAt_const _ _)) (by rw [denote_add, hKv, denote_const, one_mul]; exact hlim)
      (by omega) hL2
  -- the seed
  obtain ⟨hss, hsv, hsb⟩ := seedAt_value (machine := machine) (e := e) (env := env) hxs hxv hσs hσv
    hpos hex
  have hblkT : Tm w L 1 (pow2 (mul (const 2) (blkT (QpT k s c (lvl 0)) (kpT k s c (lvl 0))
      (inputBitsT k s c (lvl 0))))) env := by
    refine t_pow2_stable (de := 8) ?_ (by omega)
      ((stableAt_const _ _).mul ((hQs.mul hks).mul (hIBs.add (stableAt_const _ _)))) ?_ (by omega) hL2
    · unfold blkT; tame
    · simp only [blkT, denote_mul, denote_add, denote_const, hQv, hkv, hIBv, one_mul]
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hblk
  have hlb : TmF3 w L (fun sd e' i => labelT (QpT k s c (lvl 0)) (kpT k s c (lvl 0))
      (inputBitsT k s c (lvl 0)) sd (portAt k s c (lvl 0) σT e' i) e') 1 1 1 14 env := by
    intro env' he' sd e' i hsd he1 hi
    have hl := tm_labelT (env := env') hL2 (hQ.ext he') (hQs.extend' he') (hk.ext he') (hks.extend' he')
      (by rw [hks.extend'_eq he']; exact hkL) (hIB.ext he') hsd (hr.ext he')
      (by rw [hks.extend'_eq he', hQs.extend'_eq he', hkv, hQv]; exact hD)
    exact hl.app (Ext.refl _) ((hvar.app he' (he1.mono (by omega)) (hi.mono (by omega))).mono (by omega))
      (he1.mono (by omega))
  have hsT : Tm w L 1 (seedAt k s c (lvl 0) σT) env := by
    have h2 := tm_firstSeedT (env := env) hL hQ hk hks hkL hIB hN hV (har.mono_in (by omega)) hlb
      (by omega) hls hr hblkT
    refine tm_retier (tm_sub h2 (t_const (lit_lt_two_pow (by omega) hL2))) hss ?_
    rw [one_mul]; exact lt_trans hsv hblk
  -- the remaining parameters
  have hsPs : StableAt w (startPT k s c (lvl 0)) env := fun extra => by
    have hxe := hxs.extend extra
    have hxe' : (lvl 0).denote w (extra ++ env) = n := by rw [hxs extra, hxv]
    simp only [startPT, denote_div, denote_add, denote_mul, denote_sub, denote_const]
    rw [denote_spT hxe hxe', denote_kpT hxe hxe', denote_spT hxs hxv, denote_kpT hxs hxv]
  have hRs : StableAt w (RpT k s c (lvl 0)) env := fun extra => by
    rw [denote_RpT (hxs.extend extra) (by rw [hxs extra, hxv]), denote_RpT hxs hxv]
  have hRv := denote_RpT (k := k) (s := s) (c := c) hxs hxv
  have hcps := StableAt.copiesT (k := k) (s := s) (c := c) hxs hxv
  have hcpv := denote_copiesT (k := k) (s := s) (c := c) hxs hxv
  have h6 := six_le_kN hL hn hcube hconst hc hlarge hN72
  have h9 : 9 ≤ Parameters.s (kp k s c n) := by
    have : 2 ^ 6 ≤ 2 ^ kp k s c n := Nat.pow_le_pow_right (by norm_num) (by simp only [kN] at h6; omega)
    unfold Parameters.s; omega
  have hrpos : 0 < 2 ^ kp k s c n := by positivity
  have hb0 : Tm w L 1 (const 0) env := t_const (lit_lt_two_pow (by omega) hL2)
  -- the measurement tuples
  have hbad8 := tm_badCountT (rT := rT' (kpT k s c (lvl 0))) (sN := const 0) hL hr hQ hsP hb0 hRt hls
  have hbads : StableAt w (badCountT (rT' (kpT k s c (lvl 0))) (QpT k s c (lvl 0)) (startPT k s c (lvl 0))
      (const 0) (RpT k s c (lvl 0))) env :=
    StableAt.badCountT hrpos hrs hrv hQs hQv hsPs (stableAt_const _ _) hRs
  have hbadv : (badCountT (rT' (kpT k s c (lvl 0))) (QpT k s c (lvl 0)) (startPT k s c (lvl 0))
      (const 0) (RpT k s c (lvl 0))).denote w env = TailParameters.badCount (kp k s c n) := by
    rw [show rT' (kpT k s c (lvl 0)) = pow2 (kpT k s c (lvl 0)) from rfl,
      denote_badCountT hrpos hrs hrv hQs hQv hsPs (stableAt_const 0 _) hRs,
      startPT_eq hxs hxv h9, denote_const, Nat.cast_zero, sub_zero, hRv, ← badCount_bridge]
    rfl
  have hEs : StableAt w (mul (rT' (kpT k s c (lvl 0))) (rowsT' (QpT k s c (lvl 0)) (kpT k s c (lvl 0))
      (startPT k s c (lvl 0)) (const 0) (RpT k s c (lvl 0)) (copiesT k s c (lvl 0)))) env :=
    hrs.mul (hcps.mul hbads)
  have hEv : (mul (rT' (kpT k s c (lvl 0))) (rowsT' (QpT k s c (lvl 0)) (kpT k s c (lvl 0))
      (startPT k s c (lvl 0)) (const 0) (RpT k s c (lvl 0)) (copiesT k s c (lvl 0)))).denote w env =
      tupleWidth k s c n := by
    have hpq : (2 ^ kp k s c n * 2 ^ kp k s c n) ^ Q (kp k s c n) = D (kp k s c n) := by
      rw [D, Parameters.s, ← pow_add, ← pow_mul, ← pow_mul]; congr 1; ring
    rw [denote_mul, rowsT', denote_mul, hbadv, hcpv, hpq]
    rw [show (rT' (kpT k s c (lvl 0))).denote w env = 2 ^ kN k s c n from hrv]
    unfold tupleWidth
    simp only [Parameters.s, NN, tN, kN, kp]
    ring
  have hBs : StableAt w (add (mul (const 2) (powT (rT' (kpT k s c (lvl 0))) (mul (const 2) (QpT k s c (lvl 0)))))
      (const 1)) env :=
    ((stableAt_const _ _).mul (hrs.powT ((stableAt_const _ _).mul hQs))).add (stableAt_const _ _)
  have hBv : (add (mul (const 2) (powT (rT' (kpT k s c (lvl 0))) (mul (const 2) (QpT k s c (lvl 0)))))
      (const 1)).denote w env = 2 * (2 ^ kN k s c n) ^ (2 * Q (kN k s c n)) + 1 := by
    have hrs' : StableAt w (rT' (kpT k s c (lvl 0))) env := hrs
    simp only [denote_add, denote_mul, powT_denote _ _ _ hrs', denote_const]
    rw [show (rT' (kpT k s c (lvl 0))).denote w env = 2 ^ kN k s c n from hrv, hQv]
  have hBge : 2 ≤ 2 * (2 ^ kN k s c n) ^ (2 * Q (kN k s c n)) + 1 := by
    have : 0 < (2 ^ kN k s c n) ^ (2 * Q (kN k s c n)) := by positivity
    omega
  have hEtm : Tm w L 1 (mul (rT' (kpT k s c (lvl 0))) (rowsT' (QpT k s c (lvl 0)) (kpT k s c (lvl 0))
      (startPT k s c (lvl 0)) (const 0) (RpT k s c (lvl 0)) (copiesT k s c (lvl 0)))) env := by
    refine tm_retier (tm_mul (d := 10) hr (tm_mul hcp hbad8 le_rfl (by omega)) (by omega) (by omega)) hEs ?_
    rw [hEv, one_mul]
    have h1 : tupleWidth k s c n < 2 ^ tupleWidth k s c n := Nat.lt_two_pow_self
    have h2 : 2 ^ tupleWidth k s c n ≤ (2 * (2 ^ kN k s c n) ^ (2 * Q (kN k s c n)) + 1) ^
        tupleWidth k s c n := Nat.pow_le_pow_left hBge _
    omega
  have htupT : Tm w L 1 (powT (add (mul (const 2) (powT (rT' (kpT k s c (lvl 0)))
      (mul (const 2) (QpT k s c (lvl 0))))) (const 1))
      (mul (rT' (kpT k s c (lvl 0))) (rowsT' (QpT k s c (lvl 0)) (kpT k s c (lvl 0))
        (startPT k s c (lvl 0)) (const 0) (RpT k s c (lvl 0)) (copiesT k s c (lvl 0))))) env :=
    tm_powT_stable hL (tm_add (d := 4) (tm_mul (t_const (lit_lt_two_pow (by omega) hL2)) hpw le_rfl (by omega))
        (t_const (lit_lt_two_pow (by omega) hL2)) (by omega) (by omega) (by omega) (by omega))
      hBs hEtm hEs (by omega) (by omega) (by rw [hBv, hEv]; exact htup)
  -- the parser
  have hMs : StableAt w (radixPT k s c (lvl 0)) env := fun extra => by
    rw [denote_radixPT (hxs.extend extra) (by rw [hxs extra, hxv]), denote_radixPT hxs hxv]
  have hMv := denote_radixPT (k := k) (s := s) (c := c) hxs hxv
  have hqs : StableAt w (qpT k s c (lvl 0)) env := fun extra => by
    rw [denote_qpT (hxs.extend extra) (by rw [hxs extra, hxv]), denote_qpT hxs hxv]
  have hqv := denote_qpT (k := k) (s := s) (c := c) hxs hxv
  have hlgs := StableAt.lgNT (k := k) (s := s) (c := c) hxs hxv
  have hlgv := denote_lgNT (k := k) (s := s) (c := c) hxs hxv
  have hMlt : (radixPT k s c (lvl 0)).denote w env < 2 ^ L := by
    have := hM.lt; rwa [one_mul] at this
  have hcap : 4 * ParserFold.radix (edgesN k s (clk c n)) (q (edgesN k s (clk c n)) (kp k s c n)) ^ 5 <
      2 ^ (6 * L) := by
    rw [hMv] at hMlt
    have h5 := Nat.pow_lt_pow_left hMlt (by norm_num : (5 : ℕ) ≠ 0)
    have h4 : 4 * (2 ^ L) ^ 5 = 2 ^ (5 * L + 2) := by rw [pow_add, ← pow_mul]; ring
    have h6' : 2 ^ (5 * L + 2) ≤ 2 ^ (6 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hMpos : Pos w L (radixPT k s c (lvl 0)) env :=
    Pos.of_stable hMs (by rw [hMv]; unfold ParserFold.radix; omega)
  have hparse := tm_parseT hNs hNv hqs hqv hlgs hlgv hMs hMv
    (by unfold ParserFold.radix; omega) (by unfold ParserFold.radix; omega)
    (by unfold ParserFold.radix; omega) (by unfold ParserFold.radix; omega)
    hL hN hq hlg hM hK hMpos hcap
  have hsz := tm_pow2_codeSizeT hNs hNv hqs hqv hlgs hlgv hMs hMv
    (by unfold ParserFold.radix; omega) (by unfold ParserFold.radix; omega)
    (by unfold ParserFold.radix; omega) (by unfold ParserFold.radix; omega)
    hL hN hq hlg hM hK hMpos hcap (by simp only [NN, tN, kN] at hqL; exact hqL)
  -- the groups
  have hNE : (blockNetworkOf machine e (w, clk c n, σ0)).2.numEdges = edgesN k s (clk c n) :=
    numEdges_blockNetworkOf machine e w (clk c n) σ0
  have pos : 0 < (blockNetworkOf machine e (w, clk c n, σ0)).2.numEdges := by rw [hNE]; exact hpos
  have hlenS := length_constraints_toSystem machine e w (clk c n) σ0 pos
  have hIBv' : (inputBitsT k s c (lvl 0)).denote w env =
      WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (w, clk c n, σ0)).2 pos) := by
    rw [hIBv, WSchedulePlacement.inputBits, SchedulePlacement.identifierBits, hlenS, hNE]
  have hgs := tm_pow2_groupSize (toSystem (blockNetworkOf machine e (w, clk c n, σ0)).2 pos) (hsb pos)
    hL hQs hQv hks hkv (by rw [hkv] at hkL; exact hkL) hIBs hIBv' hss rfl hNs (by rw [hNv, hNE]) hQ hk hIB hsT hN
    (by rw [hNE]; simp only [NN, tN, kN, kp, Parameters.s] at hgroup ⊢; exact hgroup)
  -- the components
  have hgrp := tm_grpT hL2 hQ hk hks hkL hIB hsT
  have hlabTm := tm_labelT hL2 hQ hQs hk hks hkL hIB hsT hr (by rw [hkv, hQv]; exact hD)
  unfold counterAt
  exact tm_systemCounterT (mv := verticesN k s (tN c n)) (Qv := Q (kp k s c n)) hL hp hppos hQ hq1 hN hq hlg hM hK hN hV hk hIB hsT hsP hb0 hRt hcp hMpos
    (Le.of_stable hVs (by rw [hVv])) (Le.of_stable hQs hQv.le) har hvar hwt hpa hr Pos.pow2' hr Pos.pow2'
    hls hls hpw hK1 htupT hgrp hlabTm hparse hsz hgs

end NtimeDspace.ProgTerm
