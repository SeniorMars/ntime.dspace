import NtimeDspace.TameParser
import NtimeDspace.TameSeed
import NtimeDspace.TameGroup
import NtimeDspace.CounterAssembly

/-!
# The tier of the counter term

`tm_systemCounterT`: the counter has tier `1`, so every value arising in it is at
most `2^(128L)`, given tiers of its parameters, the stable powers (as
hypotheses, discharged by the budget), and the manual tiers of the group,
label, parser and group-size terms.
-/

namespace NtimeDspace.ProgTerm
open Term
variable {w : List Bool} {L : ℕ} {env : List ℕ}

set_option maxHeartbeats 0 in
/-- **The counter's tier**: every value is at most `2^(128L)`, given tiers of the
parameters, the stable powers, and the manual lemmas for the loop-counter powers. -/
theorem tm_systemCounterT {pT QT orderT B Cap Lb M K nT mT bitsT IBT sT sPT sNT widthT copiesT : Term}
    {arity : Term → Term} {varT weight : Term → Term → Term} {mv Qv : ℕ} (hL : 8 ≤ L)
    (hp : Tm w L 1 pT env) (hpos : Pos w L pT env)
    (hQ : Tm w L 1 QT env) (ho : Tm w L 1 orderT env) (hB : Tm w L 1 B env) (hCap : Tm w L 1 Cap env)
    (hLb : Tm w L 1 Lb env) (hM : Tm w L 1 M env) (hK : Tm w L 1 K env) (hn : Tm w L 1 nT env)
    (hm : Tm w L 1 mT env) (hb : Tm w L 1 bitsT env) (hIB : Tm w L 1 IBT env) (hs : Tm w L 1 sT env)
    (hsP : Tm w L 1 sPT env) (hsN : Tm w L 1 sNT env) (hwd : Tm w L 1 widthT env)
    (hcp : Tm w L 1 copiesT env) (hMpos : Pos w L M env)
    (hmLe : Le w L mT mv env) (hQLe : Le w L QT Qv env)
    (har : TmF w L arity 4 1 env) (hv : TmF2 w L varT 4 4 1 env) (hwt : TmF2v w L weight 4 mv 4 1 env)
    (hpa : TmFv w L (fun e => pow2 (arity e)) 4 mv 1 env)
    (hr : Tm w L 1 (pow2 bitsT) env) (hrpos : Pos w L (pow2 bitsT) env)
    (hr' : Tm w L 1 (rT' bitsT) env) (hrpos' : Pos w L (rT' bitsT) env)
    (hls : Tm w L 1 (powT (mul (pow2 bitsT) (pow2 bitsT)) QT) env)
    (hls' : Tm w L 1 (powT (mul (rT' bitsT) (rT' bitsT)) QT) env)
    (hpw : Tm w L 1 (powT (rT' bitsT) (mul (const 2) QT)) env)
    (hK1 : Tm w L 1 (pow2 (add K (const 1))) env)
    (htup : Tm w L 1 (powT (add (mul (const 2) (powT (rT' bitsT) (mul (const 2) QT))) (const 1))
      (mul (rT' bitsT) (rowsT' QT bitsT sPT sNT widthT copiesT))) env)
    (hgrp : TmF3 w L (grpT QT bitsT IBT sT) 4 4 4 9 env)
    (hlab : TmF2 w L (labelT QT bitsT IBT sT) 4 4 14 env)
    (hparse : TmF2 w L (parseT B Cap Lb M K) 8 8 6 env)
    (hsz : TmF w L (fun c => pow2 (codeSizeT B Cap Lb M K c)) 8 1 env)
    (hgs : TmF2v w L (fun nd g => pow2 (countBeforeT nT (fun v => grpT QT bitsT IBT sT (const 0) nd v) g nT))
      4 Qv 4 1 env) :
    Tm w L 1 (systemCounterT pT QT orderT B Cap Lb M K nT mT bitsT IBT sT sPT sNT widthT copiesT
      arity varT weight) env := by
  tame

end NtimeDspace.ProgTerm
