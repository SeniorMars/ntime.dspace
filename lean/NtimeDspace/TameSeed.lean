import NtimeDspace.TameParts
import NtimeDspace.PlacementSearch

/-!
# Tier of the seed search

The search keeps one more than the first balanced seed number, so its
accumulator has the tier of the search range.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool} {L : ℕ} {env : List ℕ}

theorem tm_firstSeedT {QT bitsT IBT nT mT : Term} {arity : Term → Term}
    {lbOf : Term → Term → Term → Term} {dl : ℕ} (hL : 8 ≤ L) (hQ : Tm w L 1 QT env)
    (hb : Tm w L 1 bitsT env) (hbs : StableAt w bitsT env) (hbv : bitsT.denote w env ≤ L)
    (hIB : Tm w L 1 IBT env) (hn : Tm w L 1 nT env) (hm : Tm w L 1 mT env)
    (har : TmF w L arity 1 1 env) (hlb : TmF3 w L lbOf 1 1 1 dl env) (hdl : dl ≤ 32)
    (hls : Tm w L 1 (labelSpaceT QT bitsT) env) (hr : Tm w L 1 (pow2 bitsT) env)
    (hsc : Tm w L 1 (pow2 (mul (const 2) (blkT QT bitsT IBT))) env) :
    Tm w L 2 (firstSeedT QT bitsT IBT nT mT arity lbOf) env := by
  unfold firstSeedT
  refine tm_foldT hsc (by omega) (tm_small_const (by omega) (by omega) (by omega) (by omega))
    (fun env' he x y hx hy => ?_) (by omega)
  have hg := tm_grpT (by omega) (hQ.ext he) (hb.ext he) (hbs.extend' he)
    (by rw [hbs.extend'_eq he]; exact hbv) (hIB.ext he) hy
  unfold balT
  tame

end NtimeDspace.ProgTerm
