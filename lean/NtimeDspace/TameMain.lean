import NtimeDspace.TameAccessors
import NtimeDspace.ArithHelpers

/-!
# Tier of the main loop

`tm_mainT`: at input length `n`, the decider's main loop has tier `3` under
any scale `L` satisfying the numeric facts of the budget, given that every
schedule's network has a balanced seed and degree at most `D0 < L`.
-/

namespace NtimeDspace.ProgTerm

open Term Budget Parameters Cslib.Complexity.CountingSimulation LocalSim Placement WeightedSystem
  NetworkSystem Turing

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool} {L : ℕ}

theorem StableAt.primeT {p : Term} {env : List ℕ} (hp : StableAt w p env) :
    StableAt w (primeT p) env := fun extra => by
  rw [denote_primeT (hp.extend extra), denote_primeT hp, hp extra]

set_option maxHeartbeats 1000000 in
-- Instantiating the loop bodies involves many large terms.
theorem tm_mainT {D0 : ℕ}
    (hL : 8 ≤ L) (hn : w.length < 2 ^ L) (hcube : NN k s c w.length ^ 3 < 2 ^ L)
    (hcube1 : NN k s c w.length ^ 3 + 1 < 2 ^ L)
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
    (hkey : keyCount k s * k + keyCount k s + width k + 3 ^ k < 2 ^ L)
    (hRw : LocalSim.radix (blockLength (clk c w.length)) w.length s ^ width k < 2 ^ L)
    (h3b : 3 ^ (3 * blockLength (clk c w.length)) < 2 ^ L)
    (hccv : (s + 1) * (blockLength (clk c w.length) ^ (k + 1) * 3) < 2 ^ L)
    (hm0 : MultiTapePTM.letterBits k s (blockLength (clk c w.length)) < L)
    (hsched : 3 ^ ((k + 1) * numBlocks (clk c w.length)) < 2 ^ L)
    (hD0 : D0 < L)
    (hdeg : ∀ σ, ∀ v < verticesN k s (tN c w.length),
      (MultiTapePTM.explicitPortsNum k (numBlocks (clk c w.length))
        (MultiTapePTM.letterBits k s (blockLength (clk c w.length))) σ v).length ≤ D0)
    (hex : ∀ σ, ∀ pos : 0 < (blockNetworkOf machine e (w, clk c w.length, σ)).2.numEdges,
      ∃ sd < 2 ^ (2 * blk (Q (kp k s c w.length)) (kp k s c w.length)
        (WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos))),
        balN (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos)
          (Q (kp k s c w.length)) (kp k s c w.length) sd) :
    Tm w L 3 (mainT k s c e machine (lvl 0)) [w.length] := by
  set n := w.length with hn_def
  have hL1 : 1 ≤ L := by omega
  have hxs0 : StableAt w (lvl 0) [n] := hx_stable
  have hxv0 : (lvl 0).denote w [n] = n := hx_value
  have hN0 := tm_edgesNT (w := w) hL hn hcube hconst
  have hNs0 := StableAt.edgesNT (k := k) (s := s) (c := c) hxs0 hxv0
  have hNv0 := denote_edgesNT (k := k) (s := s) (c := c) hxs0 hxv0
  have hqb0 := tm_numBlocksT (w := w) hL hn hcube hconst hc hlarge hN72
  have hqbs0 := StableAt.numBlocksT (c := c) hxs0 hxv0
  have hqbv0 := denote_numBlocksT (c := c) hxs0 hxv0
  -- the schedule loop
  have hSs : StableAt w (powT (const 3) (mul (const (k + 1)) (numBlocksT c (lvl 0)))) [n] :=
    (stableAt_const _ _).powT ((stableAt_const _ _).mul hqbs0)
  have hSv : (powT (const 3) (mul (const (k + 1)) (numBlocksT c (lvl 0)))).denote w [n] =
      3 ^ ((k + 1) * numBlocks (clk c n)) := by
    rw [powT_denote _ _ _ (stableAt_const _ _), denote_const, denote_mul, denote_const, hqbv0]
  have hS : Tm w L 1 (powT (const 3) (mul (const (k + 1)) (numBlocksT c (lvl 0)))) [n] :=
    tm_powT_stable hL (t_const (by omega)) (stableAt_const _ _)
      (t_mul (t_const (by omega)) hqb0 (by omega)) ((stableAt_const _ _).mul hqbs0) (by omega) (by omega)
      (by rw [denote_const, denote_mul, denote_const, hqbv0]; exact hsched)
  unfold mainT
  refine t_sumTv (dn := 1) (db := 2) (V := 3 ^ ((k + 1) * numBlocks (clk c n))) hS
    (fun pre _ => by rw [hSs pre, hSv]) (fun env' he' y hy hys _ => ?_) hL1 (by omega)
  -- the prime loop
  have hNs' := hNs0.extend' he'
  have hNv' : (edgesNT k s c (lvl 0)).denote w env' = NN k s c n := by rw [hNs0.extend'_eq he', hNv0]
  have hN' := hN0.ext he'
  have hPs : StableAt w (add (mul (edgesNT k s c (lvl 0)) (mul (edgesNT k s c (lvl 0)) (edgesNT k s c (lvl 0))))
      (const 1)) env' := (hNs'.mul (hNs'.mul hNs')).add (stableAt_const _ _)
  have hPv : (add (mul (edgesNT k s c (lvl 0)) (mul (edgesNT k s c (lvl 0)) (edgesNT k s c (lvl 0))))
      (const 1)).denote w env' = NN k s c n ^ 3 + 1 := by
    rw [denote_add, denote_mul, denote_mul, hNv', denote_const]; ring
  have hP : Tm w L 1 (add (mul (edgesNT k s c (lvl 0)) (mul (edgesNT k s c (lvl 0)) (edgesNT k s c (lvl 0))))
      (const 1)) env' :=
    tm_retier (d := 4) (by tame) hPs (by rw [hPv, one_mul]; exact hcube1)
  refine t_sumTv (dn := 1) (db := 1) (V := NN k s c n ^ 3 + 1) hP
    (fun pre _ => by rw [hPs pre, hPv]) (fun env'' he'' p hp hps _ => ?_) hL1 (by omega)
  have hext : Ext L env'' [n] := Ext.trans he'' he'
  have hNs'' := hNs0.extend' hext
  have hNv'' : (edgesNT k s c (lvl 0)).denote w env'' = NN k s c n := by rw [hNs0.extend'_eq hext, hNv0]
  have hN'' := hN0.ext hext
  have hcs : StableAt w (mul (lt (mul (const 4) (mul (edgesNT k s c (lvl 0)) (edgesNT k s c (lvl 0)))) p)
      (primeT p)) env'' :=
    (((stableAt_const _ _).mul (hNs''.mul hNs'')).lt hps).mul hps.primeT
  have hcond : Tm w L 4 (mul (lt (mul (const 4) (mul (edgesNT k s c (lvl 0)) (edgesNT k s c (lvl 0)))) p)
      (primeT p)) env'' := by
    unfold primeT allT; tame
  refine tm_ite_cond hcond hcs (fun hpos => ?_) (t_const (by omega))
  have hp0 : 0 < p.denote w env'' := by
    rw [denote_mul] at hpos
    have h1 : 0 < (lt (mul (const 4) (mul (edgesNT k s c (lvl 0)) (edgesNT k s c (lvl 0)))) p).denote w env'' :=
      Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0))
    rw [denote_lt] at h1
    split_ifs at h1 with h2
    · omega
    · exact absurd h1 (lt_irrefl 0)
  have hppos : Pos w L p env'' := Pos.of_stable hps hp0
  have hσ := hy.ext he''
  have hσs := hys.extend' he''
  obtain ⟨har, hvar, hwt, hpa⟩ := tm_accessors (machine := machine) (e := e) hext hL hn hcube hconst hc
    hlarge hN72 hkey hRw h3b hccv hm0 hσ hσs hD0 (hdeg _)
  have hctr := tm_counterAt (machine := machine) (e := e) hext hL hn hcube hconst hc hlarge hN72 hD hDr
    hlim hblk hgroup hqL htup hσ hσs rfl hp hppos (hex _) har hvar hwt hpa
  exact t_lt (t_const (by omega)) (tm_mod_left hctr hp) hL1

end NtimeDspace.ProgTerm
