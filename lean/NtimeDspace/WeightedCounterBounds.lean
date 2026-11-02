/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.WeightedTameParams
import NtimeDspace.TameCounterAt

-- upstream: local-only (register bounds for the weighted counting application)

/-!
# Register bounds for the general weighted counter

`tm_counterT` composes the generic parser, balanced-seed search, group enumerator,
and flat interpolation loop. Its hypotheses concern numeric buffer bounds and
the actual accessor programs. There is no machine, clock, or computation-network
assumption. Semantic equality with the weighted count is `counterT_cast`.

The import of `TameCounterAt` supplies the existing general stable-power lemma;
none of that module's machine-specific hypotheses are used here.
-/

namespace NtimeDspace.WeightedCounterTerm

open ProgTerm ProgTerm.Term Parameters WeightedSystem Placement

/-- The number of measurement coordinates for the selected weighted system. -/
noncomputable def tupleWidth {N : ℕ} (S : System N) : ℕ :=
  s (ParameterChoice.choose N) * (2 * incidenceCount S / D (ParameterChoice.choose N)) *
    TailParameters.badCount (ParameterChoice.choose N)

variable {w : List Bool} {env : List ℕ} {N L : ℕ}

/-- The selected modular counter has tier one when its explicit buffers fit
the scale and its arity, variable, and weight accessors satisfy their tier
contracts. The weighted values need not be Boolean. -/
theorem tm_counterT (S : System N) {nT mT pT : Term}
    {arity : Term → Term} {varT weight : Term → Term → Term}
    {AR : ℕ → ℕ} {V : ℕ → ℕ → ℕ}
    (hL : 8 ≤ L) (h72 : 72 ≤ N) (hcube : N ^ 3 < 2 ^ L)
    (hk6 : 6 ≤ ParameterChoice.choose N) (hinc : incidenceCount S ≤ 3 * N)
    (hD : (2 ^ ParameterChoice.choose N * 2 ^ ParameterChoice.choose N) ^
      Q (ParameterChoice.choose N) < 2 ^ L)
    (hDr : (2 ^ ParameterChoice.choose N) ^ (2 * Q (ParameterChoice.choose N)) < 2 ^ L)
    (hlim : SupportBudget.limit N (ParameterChoice.choose N) + 1 < L)
    (hblk : 2 ^ (2 * blk (Q (ParameterChoice.choose N)) (ParameterChoice.choose N)
      (WSchedulePlacement.inputBits S)) < 2 ^ L)
    (hgroup : 2 * N / 2 ^ ParameterChoice.choose N < L)
    (hqL : q N (ParameterChoice.choose N) < L)
    (htup : (2 * (2 ^ ParameterChoice.choose N) ^ (2 * Q (ParameterChoice.choose N)) + 1) ^
      tupleWidth S < 2 ^ L)
    (hn : StableAt w nT env) (hnv : nT.denote w env = N)
    (hm : StableAt w mT env) (hmv : mT.denote w env = S.constraints.length)
    (hN : Tm w L 1 nT env) (hM : Tm w L 1 mT env)
    (hp : Tm w L 1 pT env) (hppos : Pos w L pT env)
    (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = S.constraints[e].scope.length)
    (iV : ImplN2 w env varT V)
    (hV : ∀ inc : Incidence S, V inc.1 inc.2 = (incidenceVariable S inc).val)
    (hex : ∃ sd < 2 ^ (2 * blk (Q (ParameterChoice.choose N))
        (ParameterChoice.choose N) (WSchedulePlacement.inputBits S)),
      balN S (Q (ParameterChoice.choose N)) (ParameterChoice.choose N) sd)
    (har : TmF w L arity 4 1 env)
    (hvar : TmF2 w L varT 4 4 1 env)
    (hwt : TmF2v w L weight 4 S.constraints.length 4 1 env)
    (hpa : TmFv w L (fun e => pow2 (arity e)) 4 S.constraints.length 1 env) :
    Tm w L 1 (counterT nT mT pT arity varT weight) env := by
  have hL2 : 2 ≤ L := by omega
  have hk := tm_kT hL hn hnv hN h72 hcube
  have hr := tm_sT hL hn hnv hN h72 hcube
  have hQ := tm_QT hL hn hnv hN h72 hcube hk6
  have hRt := tm_RT hL hn hnv hN h72 hcube hk6
  have hq1 := tm_orderT hL hn hnv hN h72 hcube hk6
  have hq := tm_qT hL hn hnv hN h72 hcube hk6
  have hlg := tm_lgT hL hn hnv hN h72 hcube
  have hrad := tm_radixT hL hn hnv hN h72 hcube hk6
  have hK := tm_limitT hL hn hnv hN h72 hcube
  have hIB := tm_inputBitsT hL hn hm hN hM
  have hsP := tm_startT hL hn hnv hN h72 hcube hk6
  have hcp := tm_copiesT S hL hn hnv hm hmv hN hM h72 hcube hk6 hD hinc iAR hAR har
  have hks := stable_kT hn
  have hkv : (kT nT).denote w env = ParameterChoice.choose N := by rw [denote_kT hn, hnv]
  have hQs := stable_QT hn
  have hQv : (QT nT).denote w env = Q (ParameterChoice.choose N) := by rw [denote_QT hn, hnv]
  have hIBs := stable_inputBitsT hn hm
  have hIBv : (inputBitsT nT mT).denote w env = WSchedulePlacement.inputBits S := by
    rw [denote_inputBitsT hn hm, hnv, hmv]; rfl
  have hkL : (kT nT).denote w env ≤ L := by rw [hkv]; exact (selected_lt_L h72 hcube).le
  have hrs : StableAt w (pow2 (kT nT)) env := hks.pow2
  have hrv : (pow2 (kT nT)).denote w env = 2 ^ ParameterChoice.choose N := by
    rw [denote_pow2, hkv]
  have hls := tm_DT hL hn hnv hN h72 hcube hk6 hD
  have hpw : Tm w L 1 (powT (pow2 (kT nT)) (mul (const 2) (QT nT))) env :=
    tm_powT_stable hL hr hrs (t_mul (t_const (lit_lt_two_pow (by omega) hL2)) hQ (by omega))
      ((stableAt_const _ _).mul hQs) (by omega) (by omega)
      (by rw [hrv, denote_mul, denote_const, hQv]; exact hDr)
  have hKs := stable_limitT hn
  have hKv : (limitT nT).denote w env = SupportBudget.limit N (ParameterChoice.choose N) := by
    rw [denote_limitT hn, hnv]
  have hK1 : Tm w L 1 (pow2 (add (limitT nT) (const 1))) env :=
    t_pow2_stable (t_add hK (t_const (lit_lt_two_pow (by omega) hL2)) (by omega) (by omega))
      (by omega) (hKs.add (stableAt_const _ _))
      (by rw [denote_add, hKv, denote_const, one_mul]; exact hlim) (by omega) hL2
  obtain ⟨hss, hbal⟩ := seedT_spec S hn hnv hm hmv iAR hAR iV hV hex
  have hsv := seedT_lt S hn hnv hm hmv iAR hAR iV hV hex
  have hblkT : Tm w L 1 (pow2 (mul (const 2)
      (blkT (QT nT) (kT nT) (inputBitsT nT mT)))) env := by
    refine t_pow2_stable (de := 8) ?_ (by omega)
      ((stableAt_const _ _).mul ((hQs.mul hks).mul (hIBs.add (stableAt_const _ _))))
      ?_ (by omega) hL2
    · unfold blkT; tame
    · simp only [blkT, denote_mul, denote_add, denote_const, hQv, hkv, hIBv, one_mul]
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hblk
  have hlb : TmF3 w L (fun sd e i =>
      labelT (QT nT) (kT nT) (inputBitsT nT mT) sd (varT e i) e) 1 1 1 14 env := by
    intro env' he sd e i hsd he1 hi
    have hl := tm_labelT (env := env') hL2 (hQ.ext he) (hQs.extend' he) (hk.ext he)
      (hks.extend' he) (by rw [hks.extend'_eq he]; exact hkL) (hIB.ext he) hsd (hr.ext he)
      (by rw [hks.extend'_eq he, hQs.extend'_eq he, hkv, hQv]; exact hD)
    exact hl.app (Ext.refl _)
      ((hvar.app he (he1.mono (by omega)) (hi.mono (by omega))).mono (by omega))
      (he1.mono (by omega))
  have hsT : Tm w L 1 (seedT nT mT arity varT) env := by
    have h2 := tm_firstSeedT hL hQ hk hks hkL hIB hN hM (har.mono_in (by omega))
      hlb (by omega) hls hr hblkT
    refine tm_retier (tm_sub h2 (t_const (lit_lt_two_pow (by omega) hL2))) hss ?_
    rw [one_mul]; exact hsv.trans hblk
  have hsPs := stable_startT hn
  have hRs := stable_RT hn
  have hRv : (RT nT).denote w env = R (ParameterChoice.choose N) := by rw [denote_RT hn, hnv]
  have hcps := stable_copiesT S hn hm hmv iAR hAR
  have hDeq : (2 ^ ParameterChoice.choose N * 2 ^ ParameterChoice.choose N) ^
      Q (ParameterChoice.choose N) = D (ParameterChoice.choose N) := by
    rw [D, s, ← pow_two, ← pow_mul]
  have hcpv : (copiesT nT mT arity).denote w env =
      2 * incidenceCount S / D (ParameterChoice.choose N) := by
    rw [denote_copiesT S hn hmv iAR hAR, hnv, copiesOf, hDeq]
  have h9 : 9 ≤ s (ParameterChoice.choose N) := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk6
    unfold s; omega
  have hrpos : 0 < 2 ^ ParameterChoice.choose N := by positivity
  have hb0 : Tm w L 1 (const 0) env := t_const (lit_lt_two_pow (by omega) hL2)
  have hbad8 := tm_badCountT (rT := rT' (kT nT)) (sN := const 0) hL hr hQ hsP hb0 hRt hls
  have hbads : StableAt w (badCountT (rT' (kT nT)) (QT nT) (startT nT) (const 0) (RT nT)) env :=
    StableAt.badCountT hrpos hrs hrv hQs hQv hsPs (stableAt_const _ _) hRs
  have hbadv : (badCountT (rT' (kT nT)) (QT nT) (startT nT) (const 0) (RT nT)).denote w env =
      TailParameters.badCount (ParameterChoice.choose N) := by
    rw [show rT' (kT nT) = pow2 (kT nT) from rfl,
      denote_badCountT hrpos hrs hrv hQs hQv hsPs (stableAt_const 0 _) hRs,
      startT_eq hn (by rw [hnv]; exact h9), hnv, denote_const, Nat.cast_zero, sub_zero,
      hRv, ← badCount_bridge]
    rfl
  have hEs : StableAt w (mul (rT' (kT nT))
      (rowsT' (QT nT) (kT nT) (startT nT) (const 0) (RT nT) (copiesT nT mT arity))) env :=
    hrs.mul (hcps.mul hbads)
  have hEv : (mul (rT' (kT nT))
      (rowsT' (QT nT) (kT nT) (startT nT) (const 0) (RT nT) (copiesT nT mT arity))).denote w env =
      tupleWidth S := by
    rw [denote_mul, rowsT', denote_mul, hbadv, hcpv]
    change (pow2 (kT nT)).denote w env * _ = _
    rw [hrv]; unfold tupleWidth s; ring
  have hBs : StableAt w (add (mul (const 2)
      (powT (rT' (kT nT)) (mul (const 2) (QT nT)))) (const 1)) env :=
    ((stableAt_const _ _).mul (hrs.powT ((stableAt_const _ _).mul hQs))).add (stableAt_const _ _)
  have hBv : (add (mul (const 2) (powT (rT' (kT nT)) (mul (const 2) (QT nT))))
      (const 1)).denote w env = 2 * (2 ^ ParameterChoice.choose N) ^
        (2 * Q (ParameterChoice.choose N)) + 1 := by
    have hrs' : StableAt w (rT' (kT nT)) env := hrs
    simp only [denote_add, denote_mul, powT_denote _ _ _ hrs', denote_const]
    rw [show (rT' (kT nT)).denote w env = 2 ^ ParameterChoice.choose N from hrv, hQv]
  have hBge : 2 ≤ 2 * (2 ^ ParameterChoice.choose N) ^ (2 * Q (ParameterChoice.choose N)) + 1 := by
    have : 0 < (2 ^ ParameterChoice.choose N) ^ (2 * Q (ParameterChoice.choose N)) := by positivity
    omega
  have hEtm : Tm w L 1 (mul (rT' (kT nT))
      (rowsT' (QT nT) (kT nT) (startT nT) (const 0) (RT nT) (copiesT nT mT arity))) env := by
    refine tm_retier (tm_mul (d := 10) hr (tm_mul hcp hbad8 le_rfl (by omega))
      (by omega) (by omega)) hEs ?_
    rw [hEv, one_mul]
    exact Nat.lt_two_pow_self.trans_le
      ((Nat.pow_le_pow_left hBge _).trans htup.le)
  have htupT : Tm w L 1 (powT
      (add (mul (const 2) (powT (rT' (kT nT)) (mul (const 2) (QT nT)))) (const 1))
      (mul (rT' (kT nT))
        (rowsT' (QT nT) (kT nT) (startT nT) (const 0) (RT nT) (copiesT nT mT arity)))) env :=
    tm_powT_stable hL
      (tm_add (d := 4) (tm_mul (t_const (lit_lt_two_pow (by omega) hL2)) hpw le_rfl (by omega))
        (t_const (lit_lt_two_pow (by omega) hL2)) (by omega) (by omega) (by omega) (by omega))
      hBs hEtm hEs (by omega) (by omega) (by rw [hBv, hEv]; exact htup)
  have hrads := stable_radixT hn
  have hradv : (radixT nT).denote w env = ParserFold.radix N (q N (ParameterChoice.choose N)) := by
    rw [denote_radixT hn, hnv]
  have hqs := stable_qT hn
  have hqv : (qT nT).denote w env = q N (ParameterChoice.choose N) := by rw [denote_qT hn, hnv]
  have hlgs := stable_lgT hn
  have hlgv : (lgT nT).denote w env = N.log2 := by rw [denote_lgT hn, hnv]
  have hradlt : ParserFold.radix N (q N (ParameterChoice.choose N)) < 2 ^ L := by
    have := hrad.lt; rwa [one_mul, hradv] at this
  have hcap : 4 * ParserFold.radix N (q N (ParameterChoice.choose N)) ^ 5 < 2 ^ (6 * L) := by
    have h5 := Nat.pow_lt_pow_left hradlt (by norm_num : (5 : ℕ) ≠ 0)
    have h4 : 4 * (2 ^ L) ^ 5 = 2 ^ (5 * L + 2) := by rw [pow_add, ← pow_mul]; ring
    have h6 : 2 ^ (5 * L + 2) ≤ 2 ^ (6 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hradpos : Pos w L (radixT nT) env :=
    Pos.of_stable hrads (by rw [hradv]; unfold ParserFold.radix; omega)
  have hparse := tm_parseT hn hnv hqs hqv hlgs hlgv hrads hradv
    (by unfold ParserFold.radix; omega) (by unfold ParserFold.radix; omega)
    (by unfold ParserFold.radix; omega) (by unfold ParserFold.radix; omega)
    hL hN hq hlg hrad hK hradpos hcap
  have hsz := tm_pow2_codeSizeT hn hnv hqs hqv hlgs hlgv hrads hradv
    (by unfold ParserFold.radix; omega) (by unfold ParserFold.radix; omega)
    (by unfold ParserFold.radix; omega) (by unfold ParserFold.radix; omega)
    hL hN hq hlg hrad hK hradpos hcap hqL
  have hgs := tm_pow2_groupSize S hbal hL hQs hQv hks hkv (by rw [hkv] at hkL; exact hkL)
    hIBs hIBv hss rfl hn hnv hQ hk hIB hsT hN hgroup
  have hgrp := tm_grpT hL2 hQ hk hks hkL hIB hsT
  have hlab := tm_labelT hL2 hQ hQs hk hks hkL hIB hsT hr (by rw [hkv, hQv]; exact hD)
  exact tm_systemCounterT (mv := S.constraints.length) (Qv := Q (ParameterChoice.choose N))
    hL hp hppos hQ hq1 hN hq hlg hrad hK hN hM hk hIB hsT hsP hb0 hRt hcp hradpos
    (Le.of_stable hm hmv.le) (Le.of_stable hQs hQv.le) har hvar hwt hpa
    hr Pos.pow2' hr Pos.pow2' hls hls hpw hK1 htupT hgrp hlab hparse hsz hgs

end NtimeDspace.WeightedCounterTerm
