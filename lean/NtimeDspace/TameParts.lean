import NtimeDspace.TameTac
import NtimeDspace.PlacementTerm

/-!
# Tiers of the placement terms

The group and label terms use the loop counter as an exponent (`2^j` for
`j < bits`, `(r²)^node` for `node < Q`), so their tiers use the counter bounds
of `TameV`.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool} {L : ℕ} {env : List ℕ}

theorem Sm.le_of_stable {t : Term} {V : ℕ} (hs : StableAt w t env) (hv : t.denote w env ≤ V)
    {env' : List ℕ} (he : Ext L env' env) : ∀ pre, Small L pre → t.denote w (pre ++ env') ≤ V := by
  obtain ⟨p, _, rfl⟩ := he
  intro pre _
  rw [← List.append_assoc, hs]; exact hv

theorem tm_grpT {QT bitsT IBT sT : Term} (hL : 2 ≤ L) (hQ : Tm w L 1 QT env)
    (hb : Tm w L 1 bitsT env) (hbs : StableAt w bitsT env) (hbv : bitsT.denote w env ≤ L)
    (hIB : Tm w L 1 IBT env) (hs : Tm w L 1 sT env) :
    TmF3 w L (grpT QT bitsT IBT sT) 4 4 4 9 env := by
  intro env' he h node x hh hn hx
  unfold grpT
  refine Tm.mono (t_sumTv (V := bitsT.denote w env) (hb.ext he) (Sm.le_of_stable hbs le_rfl he)
    (fun env'' he' j hj _ hjv => ?_) (by omega) (db := 8) (by omega)) (by omega)
  refine Tm.mono (t_mul (d1 := 7) ?_ (t_pow2_lt (d := 1) hj (by omega) hjv (by simpa using hbv)
    (by omega) hL) (by omega)) (by omega)
  unfold parityNT
  tame

theorem tm_labelT {QT bitsT IBT sT : Term} (hL : 2 ≤ L) (hQ : Tm w L 1 QT env)
    (hQs : StableAt w QT env) (hb : Tm w L 1 bitsT env) (hbs : StableAt w bitsT env)
    (hbv : bitsT.denote w env ≤ L) (hIB : Tm w L 1 IBT env) (hs : Tm w L 1 sT env)
    (hr : Tm w L 1 (pow2 bitsT) env)
    (hlab : (2 ^ bitsT.denote w env * 2 ^ bitsT.denote w env) ^ QT.denote w env < 2 ^ L) :
    TmF2 w L (labelT QT bitsT IBT sT) 4 4 14 env := by
  have hg := tm_grpT hL hQ hb hbs hbv hIB hs
  intro env' he v e hv he1
  unfold labelT
  refine Tm.mono (t_sumTv (V := QT.denote w env) (hQ.ext he) (Sm.le_of_stable hQs le_rfl he)
    (fun env'' he' node hn _ hnv => ?_) (by omega) (db := 13) (by omega)) (by omega)
  have hrr : Tm w L 2 (mul (pow2 bitsT) (pow2 bitsT)) env := t_mul hr hr (by omega)
  have hrrs : StableAt w (mul (pow2 bitsT) (pow2 bitsT)) env := hbs.pow2.mul hbs.pow2
  have hpow : Tm w L 1 (powT (mul (pow2 bitsT) (pow2 bitsT)) node) env'' := by
    refine t_powT_lt (hrr.ext (he'.trans he)) (hrrs.extend' (he'.trans he)) hn (by omega) hnv
      (by omega) le_rfl ?_ (by omega) (by omega)
    rw [hrrs.extend'_eq (he'.trans he)]
    simpa [denote_pow2] using hlab
  refine Tm.mono (t_mul (d1 := 12) ?_ hpow (by omega)) (by omega)
  tame

end NtimeDspace.ProgTerm
