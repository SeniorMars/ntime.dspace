import NtimeDspace.CounterLocal
import NtimeDspace.ModularBinomial
import Mathlib.FieldTheory.Finite.Basic

/-!
# Modular arithmetic terms

Terms for modular powers, Fermat inverses and the falling products used by the
Hermite weights. Each lemma states the meaning of the term as a residue in
`ZMod P`, given stable arguments.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- `x ^ e mod p`. -/
def powModT (p x e : Term) : Term := Term.prodMod p e fun _ => x

/-- The base may be any term whose residue in the loop environments is `X`. -/
theorem powModT_denote' (p x e : Term) (env : List ℕ) (P : ℕ) (X : ZMod P)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hx : ∀ acc k, (x.denote w (acc :: k :: env) : ZMod P) = X) :
    ((powModT p x e).denote w env : ZMod P) = X ^ e.denote w env := by
  rw [powModT, denote_prodModZ p e _ env P (fun _ => X) hp hpv (fun acc k _ => hx acc k)]
  simp

theorem powModT_denote (p x e : Term) (env : List ℕ) (P : ℕ)
    (hp : StableAt w p env) (hpv : p.denote w env = P) (hx : StableAt w x env) :
    ((powModT p x e).denote w env : ZMod P) =
      (x.denote w env : ZMod P) ^ e.denote w env :=
  powModT_denote' p x e env P _ hp hpv (fun acc k => by rw [hx.cons₂])

/-- `x⁻¹` in `ZMod p` by Fermat: `x ^ (p - 2)`. -/
def invModT (p x : Term) : Term := powModT p x (sub p (const 2))

theorem invModT_denote (p x : Term) (env : List ℕ) (P : ℕ) [Fact P.Prime] (hP : 2 < P)
    (hp : StableAt w p env) (hpv : p.denote w env = P) (hx : StableAt w x env) :
    ((invModT p x).denote w env : ZMod P) = (x.denote w env : ZMod P)⁻¹ := by
  rw [invModT, powModT_denote p x _ env P hp hpv hx]
  simp only [denote_sub, denote_const, hpv]
  set a : ZMod P := (x.denote w env : ZMod P)
  by_cases ha : a = 0
  · rw [ha, inv_zero, zero_pow (by omega)]
  · have hF := ZMod.pow_card_sub_one_eq_one ha
    rw [show P - 1 = (P - 2) + 1 by omega, pow_succ] at hF
    exact (eq_inv_of_mul_eq_one_left hF)

theorem StableAt.extend₂ {t : Term} {env : List ℕ} (h : StableAt w t env) (acc k : ℕ) :
    StableAt w t (acc :: k :: env) := h.extend [acc, k]

theorem stableAt_index (env : List ℕ) (acc k : ℕ) :
    StableAt w (lvl env.length) (acc :: k :: env) := stableAt_lvl (by simp)

/-- The rising binomial `∏_{i<d} (m+i)/(i+1)` modulo `p`. -/
def binomT (p m d : Term) : Term :=
  Term.prodMod p d fun i => mod (mul (add m i) (invModT p (add i (const 1)))) p

theorem binomialLoop_eq {P : ℕ} [Fact P.Prime] (m : ZMod P) (d : ℕ) (acc : ZMod P) :
    HermiteRecovery.modularBinomialLoop m d acc =
      acc * ∏ i ∈ Finset.range d, ((m + i) / ((i + 1 : ℕ) : ZMod P)) := by
  induction d generalizing acc with
  | zero => simp [HermiteRecovery.modularBinomialLoop]
  | succ d ih =>
    rw [HermiteRecovery.modularBinomialLoop, ih, Finset.prod_range_succ]
    ring

theorem binomT_denote (p m d : Term) (env : List ℕ) (P : ℕ) [Fact P.Prime] (hP : 2 < P)
    (hp : StableAt w p env) (hpv : p.denote w env = P) (hm : StableAt w m env) :
    ((binomT p m d).denote w env : ZMod P) =
      HermiteRecovery.modularBinomial (m.denote w env) (d.denote w env) := by
  rw [binomT, denote_prodModZ p d _ env P (fun k => ((m.denote w env : ZMod P) + k) /
      ((k + 1 : ℕ) : ZMod P)) hp hpv (fun acc k _ => ?_)]
  · rw [HermiteRecovery.modularBinomial, binomialLoop_eq, one_mul]
  · have hpk := hp.extend₂ acc k
    have e1 := invModT_denote p (add (lvl env.length) (const 1)) (acc :: k :: env) P hP hpk
      (by rw [hp.cons₂]; exact hpv) ((stableAt_index env acc k).add (stableAt_const _ _))
    simp only [denote_mod, denote_mul, denote_add, hm.cons₂, hp.cons₂, hpv, denote_lvl_index,
      ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, e1, denote_const] at e1 ⊢
    rw [div_eq_mul_inv]

/-- `(-1)^d` modulo `p`. -/
def signT (p d : Term) : Term := ite (mod d (const 2)) (sub p (const 1)) (const 1)

theorem signT_denote (p d : Term) (env : List ℕ) (P : ℕ) (hP : 1 ≤ P)
    (hpv : p.denote w env = P) :
    ((signT p d).denote w env : ZMod P) = (-1) ^ d.denote w env := by
  simp only [signT, denote_ite, denote_mod, denote_const, denote_sub, hpv]
  rcases Nat.mod_two_eq_zero_or_one (d.denote w env) with h | h
  · rw [h, if_neg (lt_irrefl 0)]
    rw [(Nat.even_iff.mpr h).neg_one_pow]; simp
  · rw [h, if_pos one_pos, (Nat.odd_iff.mpr h).neg_one_pow, Nat.cast_sub hP]
    simp

/-- The reciprocal coefficient `[z^d] (a + z)^{-m}` modulo `p`. -/
def leafT (p a m d : Term) : Term :=
  mod (mul (mod (mul (signT p d) (binomT p m d)) p) (powModT p (invModT p a) (add m d))) p

theorem leafT_denote (p a m d : Term) (env : List ℕ) (P : ℕ) [Fact P.Prime] (hP : 2 < P)
    (hp : StableAt w p env) (hpv : p.denote w env = P) (ha : StableAt w a env)
    (hm : StableAt w m env) :
    ((leafT p a m d).denote w env : ZMod P) =
      HermiteRecovery.modularReciprocalCoefficient (a.denote w env : ZMod P) (m.denote w env)
        (d.denote w env) := by
  have hinv : ∀ acc k, ((invModT p a).denote w (acc :: k :: env) : ZMod P) =
      (a.denote w env : ZMod P)⁻¹ := fun acc k => by
    rw [invModT_denote p a _ P hP (hp.extend₂ acc k) (by rw [hp.cons₂]; exact hpv)
      (ha.extend₂ acc k), ha.cons₂]
  simp only [leafT, denote_mod, denote_mul, hpv, ZMod.natCast_mod, Nat.cast_mul,
    signT_denote p d env P (by omega) hpv, binomT_denote p m d env P hP hp hpv hm,
    powModT_denote' p (invModT p a) (add m d) env P _ hp hpv hinv, denote_add,
    HermiteRecovery.modularReciprocalCoefficient]

end NtimeDspace.ProgTerm
