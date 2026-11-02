import NtimeDspace.TameTac
import NtimeDspace.TameParts
import NtimeDspace.SupportQueryTerm
import NtimeDspace.PackBound

/-!
# Tiers of the support parser

Every state of a scan is a `Good` packed state (`ParserFold.stepNat_good`), for
any candidate and any query, so a scan has tier `6` when `4·M⁵ < 2^(6L)`. Its
rank field is at most the capacity, which bounds `2 ^ codeSize`.
-/

namespace NtimeDspace.ProgTerm

open Term ParserFold

variable {w : List Bool} {L : ℕ} {env : List ℕ}

section Scan

variable {B Cap Lb M K : Term} {bv cv lv mv : ℕ}
  (hBs : StableAt w B env) (hBv : B.denote w env = bv)
  (hCs : StableAt w Cap env) (hCv : Cap.denote w env = cv)
  (hLs : StableAt w Lb env) (hLv : Lb.denote w env = lv)
  (hMs : StableAt w M env) (hMv : M.denote w env = mv)
  (hbm : bv < mv) (hcm : cv < mv) (hlm : lv < mv) (hm2 : 2 ≤ mv)
include hBs hBv hCs hCv hLs hLv hMs hMv hbm hcm hlm hm2

theorem scan_acc_good {env' : List ℕ} (he : Ext L env' env) (c q : Term) (k : ℕ) :
    Good mv cv (foldAcc w (fun acc j => stepT B Cap Lb q M acc (bit c j)) env'
      ((const 1).denote w env') k) := by
  obtain ⟨p, _, rfl⟩ := he
  induction k with
  | zero => exact ⟨by have := four_mul_pow_pos hm2; simp; omega, by simp⟩
  | succ k ih =>
    rw [foldAcc_succ, denote_stepT]
    simp only [denote_lvl_acc]
    rw [(hBs.extend p).cons₂, (hCs.extend p).cons₂, (hLs.extend p).cons₂, (hMs.extend p).cons₂,
      hBs p, hCs p, hLs p, hMs p, hBv, hCv, hLv, hMv]
    exact stepNat_good hbm hcm hlm hm2 ih

theorem scan_good {env' : List ℕ} (he : Ext L env' env) (c q : Term) :
    Good mv cv ((scanT B Cap Lb q M K c).denote w env') := by
  rw [scanT, denote_foldT]
  exact scan_acc_good hBs hBv hCs hCv hLs hLv hMs hMv hbm hcm hlm hm2 he c q _

theorem tm_parseT (hL : 8 ≤ L) (hB : Tm w L 1 B env) (hC : Tm w L 1 Cap env)
    (hLb : Tm w L 1 Lb env) (hM : Tm w L 1 M env) (hK : Tm w L 1 K env) (hMpos : Pos w L M env)
    (hcap : 4 * mv ^ 5 < 2 ^ (6 * L)) :
    TmF2 w L (parseT B Cap Lb M K) 8 8 6 env := by
  intro env' he c q hc hq
  unfold parseT scanT
  refine tm_foldT_inv (dn := 3) (di := 1) (db := 60) ?_ (by omega)
    (t_const (lit_lt_two_pow (by omega) (by omega))) (fun env'' he' x y hx hy => ?_) (by omega)
    (fun pre hp k _ => ?_)
  · unfold log2T
    tame
  · unfold stepT
    tame
  · exact (scan_acc_good hBs hBv hCs hCv hLs hLv hMs hMv hbm hcm hlm hm2
      (Ext.trans ⟨pre, hp, rfl⟩ he) c q k).1.trans hcap

theorem tm_pow2_codeSizeT (hL : 8 ≤ L) (hB : Tm w L 1 B env) (hC : Tm w L 1 Cap env)
    (hLb : Tm w L 1 Lb env) (hM : Tm w L 1 M env) (hK : Tm w L 1 K env) (hMpos : Pos w L M env)
    (hcap : 4 * mv ^ 5 < 2 ^ (6 * L)) (hcL : cv < L) :
    TmF w L (fun c => pow2 (codeSizeT B Cap Lb M K c)) 8 1 env := by
  have hp := tm_parseT hBs hBv hCs hCv hLs hLv hMs hMv hbm hcm hlm hm2 hL hB hC hLb hM hK hMpos hcap
  intro env' he c hc
  refine t_pow2_lt (de := 6) (V := cv + 1) ?_ (by omega) (fun pre hp' => ?_) (by omega) (by omega)
    (by omega)
  · unfold codeSizeT rankT
    tame
  · have hg := scan_good (K := K) hBs hBv hCs hCv hLs hLv hMs hMv hbm hcm hlm hm2
      (Ext.trans ⟨pre, hp', rfl⟩ he) c (const 0)
    simp only [codeSizeT, rankT, parseT, denote_mod, denote_div, denote_const]
    rw [show M.denote w (pre ++ env') = mv by
      obtain ⟨p, _, rfl⟩ := he; rw [← List.append_assoc, hMs, hMv]]
    have := hg.2
    omega

end Scan

end NtimeDspace.ProgTerm
