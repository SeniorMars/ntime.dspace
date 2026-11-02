import NtimeDspace.TameParts
import NtimeDspace.PlacementBalance
import NtimeDspace.CounterLocal

/-!
# The group-size bound

With a balanced seed number, a group at a node has at most `2n/2^bits`
variables, so the inner loop's `2 ^ |group|` is below `2^L` once
`2n/2^bits < L`.
-/

namespace NtimeDspace.ProgTerm

open Term Placement

variable {w : List Bool} {L : ℕ} {env : List ℕ}

theorem countBefore_grp_denote {QT bitsT IBT sT nT nd g : Term} {env' : List ℕ}
    (hQ : StableAt w QT env') (hb : StableAt w bitsT env') (hIB : StableAt w IBT env')
    (hs : StableAt w sT env') (hn : StableAt w nT env') (hnd : StableAt w nd env')
    (hg : StableAt w g env') :
    (countBeforeT nT (fun v => grpT QT bitsT IBT sT (const 0) nd v) g nT).denote w env' =
      ∑ v ∈ Finset.range (nT.denote w env'),
        if grpN (QT.denote w env') (bitsT.denote w env') (IBT.denote w env') (sT.denote w env') 0
          (nd.denote w env') v = g.denote w env' then 1 else 0 := by
  show (sumT nT fun i => mul (lt i nT) (eqT (grpT QT bitsT IBT sT (const 0) nd i) g)).denote w env' = _
  rw [denote_sumT _ _ env' (fun k => (if k < nT.denote w env' then 1 else 0) *
    (if grpN (QT.denote w env') (bitsT.denote w env') (IBT.denote w env') (sT.denote w env') 0
      (nd.denote w env') k = g.denote w env' then 1 else 0)) (fun acc k => ?_)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_range.mp hk), one_mul]
  · have e2 : acc :: k :: env' = [acc, k] ++ env' := rfl
    rw [denote_mul, denote_lt, denote_eqT, e2,
      denote_grpT (hIB.extend _) (hQ.extend _) (hb.extend _) (hs.extend _) (stableAt_const _ _)
        (hnd.extend _) (stableAt_lvl (by simp))]
    simp only [← e2, denote_lvl_index, denote_const, hn.cons₂, hQ.cons₂, hb.cons₂, hIB.cons₂,
      hs.cons₂, hnd.cons₂, hg.cons₂]

theorem tm_pow2_groupSize {n : ℕ} (S : WeightedSystem.System n) {Q bits sd : ℕ}
    (hbal : balN S Q bits sd) {QT bitsT IBT sT nT : Term} (hL : 8 ≤ L)
    (hQs : StableAt w QT env) (hQv : QT.denote w env = Q)
    (hbs : StableAt w bitsT env) (hbv : bitsT.denote w env = bits) (hbL : bits ≤ L)
    (hIBs : StableAt w IBT env) (hIBv : IBT.denote w env = WSchedulePlacement.inputBits S)
    (hss : StableAt w sT env) (hsv : sT.denote w env = sd)
    (hns : StableAt w nT env) (hnv : nT.denote w env = n)
    (hQ : Tm w L 1 QT env) (hb : Tm w L 1 bitsT env) (hIB : Tm w L 1 IBT env)
    (hs : Tm w L 1 sT env) (hn : Tm w L 1 nT env) (hsize : 2 * n / 2 ^ bits < L) :
    TmF2v w L (fun nd g => pow2 (countBeforeT nT (fun v => grpT QT bitsT IBT sT (const 0) nd v) g nT))
      4 Q 4 1 env := by
  have hgrp := tm_grpT (by omega) hQ hb hbs (by rw [hbv]; exact hbL) hIB hs
  intro env' he nd g hnd hnds hndv hg hgs
  refine t_pow2_lt (de := 3) (V := 2 * n / 2 ^ bits + 1) ?_ (by omega) (fun pre hp => ?_)
    (by omega) (by omega) (by omega)
  · tame
  · have hext : Ext L (pre ++ env') env := Ext.trans ⟨pre, hp, rfl⟩ he
    rw [countBefore_grp_denote (hQs.extend' hext) (hbs.extend' hext) (hIBs.extend' hext)
      (hss.extend' hext) (hns.extend' hext) (hnds.extend pre) (hgs.extend pre),
      hQs.extend'_eq hext, hbs.extend'_eq hext, hIBs.extend'_eq hext, hss.extend'_eq hext,
      hns.extend'_eq hext, hQv, hbv, hIBv, hsv, hnv]
    have hndQ : nd.denote w (pre ++ env') < Q := hndv pre hp
    rw [Nat.lt_succ_iff]
    by_cases hgb : g.denote w (pre ++ env') < 2 ^ bits
    · exact (Nat.le_div_iff_mul_le (by positivity)).mpr (hbal.2 _ hndQ _ hgb)
    · rw [Finset.sum_eq_zero fun v _ => if_neg (fun h => hgb (by
        rw [← h]; exact grpN_lt Q bits sd _ _ _ _))]
      exact Nat.zero_le _

end NtimeDspace.ProgTerm
