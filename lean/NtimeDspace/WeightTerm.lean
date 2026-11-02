import NtimeDspace.ArithTerm
import NtimeDspace.FlatHorner

/-!
# The Hermite weight as a term

The running weight multiplies separately truncated reciprocal factors. Each
factor is evaluated by a scalar Horner loop with a cached inverse and one
modular accumulator; no degree tuple is enumerated by `weightT`. Projection correctness requires the flat-weight no-alias bound.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- `x ^ e` exactly. -/
def powT (x e : Term) : Term := foldT e (const 1) fun acc _ => mul acc x

theorem powT_denote (x e : Term) (env : List ℕ) (hx : StableAt w x env) :
    (powT x e).denote w env = x.denote w env ^ e.denote w env := by
  simp only [powT, denote_foldT, denote_const]
  rw [foldAcc_eq _ env (fun acc _ => acc * x.denote w env) (fun acc k => by
    simp [hx.cons₂])]
  induction e.denote w env with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.foldl_append, ih]; simp [pow_succ]

theorem StableAt.powT {x e : Term} {env : List ℕ} (hx : StableAt w x env)
    (he : StableAt w e env) : StableAt w (powT x e) env := fun extra => by
  rw [powT_denote x e _ (hx.extend extra), powT_denote x e env hx, hx extra, he extra]

/-- `T / x^i`, by dividing `i` times; every value is at most `T`. -/
def divPowT (x T i : Term) : Term := foldT i T fun acc _ => div acc x

theorem divPowT_denote (x T i : Term) (env : List ℕ) (hx : StableAt w x env) :
    (divPowT x T i).denote w env = T.denote w env / x.denote w env ^ i.denote w env := by
  simp only [divPowT, denote_foldT]
  rw [foldAcc_eq _ env (fun acc _ => acc / x.denote w env) (fun acc k => by simp [hx.cons₂])]
  induction i.denote w env with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.foldl_append, ih]; simp [pow_succ, Nat.div_div_eq_div_mul]

/-- The digit `T / x^i % x`. -/
def digitT (x T i : Term) : Term := mod (divPowT x T i) x

theorem digitT_denote (x T i : Term) (env : List ℕ) (hx : StableAt w x env) :
    (digitT x T i).denote w env =
      T.denote w env / x.denote w env ^ i.denote w env % x.denote w env := by
  simp [digitT, divPowT_denote x T i env hx]

theorem StableAt.digitT {x T i : Term} {env : List ℕ} (hx : StableAt w x env)
    (hT : StableAt w T env) (hi : StableAt w i env) : StableAt w (digitT x T i) env :=
  fun extra => by
    rw [digitT_denote x T i _ (hx.extend extra), digitT_denote x T i env hx, hx extra, hT extra,
      hi extra]

/-- A scalar fold reducing its accumulator modulo `p` after every step. -/
def foldModT (p n : Term) (body : Term → Term → Term) : Term :=
  foldT n (const 0) fun acc i => mod (body acc i) p

theorem foldModT_denote (p n : Term) (body : Term → Term → Term) (env : List ℕ)
    (P : ℕ) (step : ZMod P → ℕ → ZMod P)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hb : ∀ acc i,
      ((body (lvl (env.length + 1)) (lvl env.length)).denote w (acc :: i :: env) : ZMod P) =
        step acc i) :
    ((foldModT p n body).denote w env : ZMod P) =
      (List.range (n.denote w env)).foldl step 0 := by
  simp only [foldModT, denote_foldT, denote_const]
  generalize n.denote w env = count
  induction count with
  | zero => simp
  | succ count ih =>
    rw [foldAcc_succ, List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, denote_mod, hp.cons₂, hpv,
      ZMod.natCast_mod, hb, ih]

/-- One Horner step. `ai` is a cached inverse of the factor's constant term. -/
def hornerStepT (p ai m z d acc : Term) : Term :=
  mod (sub (add p (const 1))
    (mod (mul (mul (mul (mul acc (add m d)) ai) z)
      (invModT p (add d (const 1)))) p)) p

theorem hornerStepT_denote (p ai m z d acc : Term) (env : List ℕ)
    (P : ℕ) [Fact P.Prime] (hP : 2 < P)
    (hp : StableAt w p env) (hpv : p.denote w env = P) (hd : StableAt w d env) :
    ((hornerStepT p ai m z d acc).denote w env : ZMod P) =
      1 - (acc.denote w env : ZMod P) * ((m.denote w env : ZMod P) + d.denote w env) *
        (ai.denote w env : ZMod P) * (z.denote w env : ZMod P) / (d.denote w env + 1 : ℕ) := by
  have hbound : (mul (mul (mul (mul acc (add m d)) ai) z)
      (invModT p (add d (const 1)))).denote w env % P ≤ P + 1 :=
    (Nat.mod_lt _ (by omega)).le.trans (by omega)
  simp only [hornerStepT, denote_mod, denote_sub, denote_add, denote_const, hpv]
  rw [ZMod.natCast_mod, Nat.cast_sub hbound]
  simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_one,
    ZMod.natCast_self, zero_add, denote_mul, denote_add, denote_const, Nat.cast_mul,
    invModT_denote p (add d (const 1)) env P hP hp hpv (hd.add (stableAt_const _ _)),
    div_eq_mul_inv]

/-- Evaluate one separately truncated reciprocal factor by scalar Horner steps. -/
def factorWeightT (p x a m z : Term) : Term :=
  letT (invModT p a) fun ai =>
    mod (mul (powModT p ai m) (foldModT p x fun acc i =>
      hornerStepT p ai m z (sub (sub x (const 1)) i) acc)) p

theorem factorWeightT_denote (p x a m z : Term) (env : List ℕ)
    (P : ℕ) [Fact P.Prime] (hP : 2 < P)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hx : StableAt w x env) (ha : StableAt w a env) (hm : StableAt w m env)
    (hz : StableAt w z env) :
    ((factorWeightT p x a m z).denote w env : ZMod P) =
      FlatHermite.factorHorner (a.denote w env : ZMod P) (m.denote w env)
        (z.denote w env : ZMod P) (x.denote w env) := by
  let av := (invModT p a).denote w env
  let env' := av :: env
  have hps : StableAt w p env' := hp.extend [av]
  have hpv' : p.denote w env' = P := (hp.cons av).trans hpv
  have hai : StableAt w (lvl env.length) env' := stableAt_lvl (by simp [env'])
  have haiv : ((lvl env.length).denote w env' : ZMod P) = (a.denote w env : ZMod P)⁻¹ := by
    simpa only [env', denote_lvl_let, av] using invModT_denote p a env P hP hp hpv ha
  have hf := foldModT_denote p x
    (fun acc i => hornerStepT p (lvl env.length) m z (sub (sub x (const 1)) i) acc)
    env' P (fun acc i => 1 - acc * ((m.denote w env : ZMod P) +
      ((x.denote w env - 1 - i : ℕ) : ZMod P)) * (a.denote w env : ZMod P)⁻¹ *
        (z.denote w env : ZMod P) / (x.denote w env - 1 - i + 1 : ℕ)) hps hpv' (by
      intro acc i
      rw [hornerStepT_denote _ _ _ _ _ _ _ P hP (hps.extend₂ acc i)
        (by rw [hps.cons₂]; exact hpv')
        ((((hx.extend [av]).extend₂ acc i).sub (stableAt_const _ _)).sub
          (stableAt_index env' acc i))]
      have hmx : m.denote w (acc :: i :: env') = m.denote w env := hm [acc, i, av]
      have hzx : z.denote w (acc :: i :: env') = z.denote w env := hz [acc, i, av]
      have hxx : x.denote w (acc :: i :: env') = x.denote w env := hx [acc, i, av]
      simp only [denote_sub, denote_const, denote_lvl_acc, denote_lvl_index,
        hai.cons₂, haiv, hmx, hzx, hxx])
  change ((mod (mul (powModT p (lvl env.length) m)
    (foldModT p x fun acc i => hornerStepT p (lvl env.length) m z
      (sub (sub x (const 1)) i) acc)) p).denote w env' : ZMod P) = _
  rw [denote_mod, hpv', ZMod.natCast_mod, denote_mul, Nat.cast_mul,
    powModT_denote p (lvl env.length) m env' P hps hpv' hai, haiv, hf]
  simp only [env', hm.cons, hx.cons, FlatHermite.factorHorner,
    FlatHermite.factorHornerLoop_eq_foldl]

/-- The flat Hermite weight: multiply separately evaluated reciprocal factors. -/
def weightT (p x count : Term) (A M : Term → Term) (z : Term) : Term :=
  Term.prodMod p count fun slot => factorWeightT p x (A slot) (M slot) z

/-- The running weight term computes the factorwise-truncated flat weight. -/
theorem weightT_denote {base : List ℕ} (p x count : Term) (A M : Term → Term) (z : Term)
    (extra : List ℕ) (P : ℕ) [Fact P.Prime] (hP : 2 < P)
    (Aspec Mspec : ℕ → ℕ) (hA : ImplementsFun w base A Aspec) (hM : ImplementsFun w base M Mspec)
    (hp : StableAt w p (extra ++ base)) (hpv : p.denote w (extra ++ base) = P)
    (hx : StableAt w x (extra ++ base)) (_hc : StableAt w count (extra ++ base))
    (hz : StableAt w z (extra ++ base))
    (hxP : x.denote w (extra ++ base) ≤ P)
    (valid : IntervalCoefficients.Valid (fun i => ((Aspec i : ZMod P), Mspec i))
      (count.denote w (extra ++ base))) :
    ((weightT p x count A M z).denote w (extra ++ base) : ZMod P) =
      FlatHermite.flatWeightEvaluation (fun i => ((Aspec i : ZMod P), Mspec i))
        (count.denote w (extra ++ base)) (x.denote w (extra ++ base))
        (z.denote w (extra ++ base) : ZMod P) := by
  set env := extra ++ base with henv
  rw [weightT, denote_prodModZ p count _ env P (fun slot =>
    FlatHermite.factorHorner (Aspec slot : ZMod P) (Mspec slot)
      (z.denote w env : ZMod P) (x.denote w env)) hp hpv (fun acc slot _ => ?_)]
  · exact FlatHermite.prod_factorHorner_eq_flatWeightEvaluation _ _ _ valid hxP _
  · have hi := stableAt_index (w := w) env acc slot
    have hAi := hA (acc :: slot :: extra) (lvl env.length) (by simpa [env] using hi)
    have hMi := hM (acc :: slot :: extra) (lvl env.length) (by simpa [env] using hi)
    simp only [List.cons_append, ← henv, denote_lvl_index] at hAi hMi
    rw [factorWeightT_denote _ _ _ _ _ _ P hP (hp.extend₂ acc slot)
      (by rw [hp.cons₂]; exact hpv) (hx.extend₂ acc slot) hAi.2 hMi.2 (hz.extend₂ acc slot),
      hAi.1, hMi.1, hz.cons₂, hx.cons₂]

end NtimeDspace.ProgTerm
