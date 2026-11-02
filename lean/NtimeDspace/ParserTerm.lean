import NtimeDspace.PackedParser
import NtimeDspace.CounterLocal
import NtimeDspace.WeightTerm

/-!
# The support parser as a term

`stepT` mirrors `ParserFold.stepNat` on packed states, and `scanT` folds it over
the bits of a candidate number. With `PackedParser` and `ParserFold.scan_eq_fold`
its meaning is the packed result of `BoundedSupportParser.scan` on the
candidate's word.
-/

namespace NtimeDspace.ProgTerm

open Term ParserFold

variable {w : List Bool}

@[simp] theorem zero_lt_ite_one (P : Prop) [Decidable P] :
    (0 < if P then (1 : ℕ) else 0) ↔ P := by
  split_ifs <;> simp_all

/-- `1` if `a ≤ b`. -/
def leT (a b : Term) : Term := sub (const 1) (lt b a)

@[simp] theorem denote_leT (a b : Term) (env : List ℕ) :
    (leT a b).denote w env = if a.denote w env ≤ b.denote w env then 1 else 0 := by
  simp only [leT, denote_sub, denote_const, denote_lt]
  split_ifs <;> omega

def packT (M t c r f z a : Term) : Term :=
  add t (mul (const 4) (add c (mul M (add r (mul M (add f (mul M (add z (mul M a)))))))))

@[simp] theorem denote_packT (M t c r f z a : Term) (env : List ℕ) :
    (packT M t c r f z a).denote w env = packFields (M.denote w env) (t.denote w env)
      (c.denote w env) (r.denote w env) (f.denote w env) (z.denote w env) (a.denote w env) := by
  simp [packT, packFields]

def finishT (B Cap q M c r f gap : Term) : Term :=
  ite (mul (mul (lt (const 0) gap) (leT gap (sub B c))) (lt r Cap))
    (packT M (const 1) (add c gap) (add r (const 1))
      (ite (add (eqT f (const 1)) (eqT (add c gap) q)) (const 1) (const 0)) (const 0) (const 0))
    (const 0)

theorem denote_finishT (B Cap q M c r f gap : Term) (env : List ℕ) :
    (finishT B Cap q M c r f gap).denote w env =
      finishNat (B.denote w env) (Cap.denote w env) (q.denote w env) (M.denote w env)
        (c.denote w env) (r.denote w env) (f.denote w env) (gap.denote w env) := by
  simp only [finishT, finishNat, denote_ite, denote_mul, denote_lt, denote_leT, denote_sub,
    denote_const, denote_packT, denote_add, denote_eqT]
  by_cases h1 : 0 < gap.denote w env <;>
    by_cases h2 : gap.denote w env ≤ B.denote w env - c.denote w env <;>
    by_cases h3 : r.denote w env < Cap.denote w env <;>
    simp [h1, h2, h3] <;>
    by_cases h4 : f.denote w env = 1 <;>
    by_cases h5 : c.denote w env + gap.denote w env = q.denote w env <;> simp [h4, h5]

def prefixT (B Cap Lb q M c r f z b : Term) : Term :=
  ite (eqT b (const 0))
    (ite (lt z Lb) (packT M (const 2) c r f (add z (const 1)) (const 0)) (const 0))
    (ite (lt (const 0) B)
      (ite (eqT z (const 0)) (finishT B Cap q M c r f (const 1))
        (packT M (const 3) c r f z (const 1)))
      (const 0))

theorem denote_prefixT (B Cap Lb q M c r f z b : Term) (env : List ℕ) :
    (prefixT B Cap Lb q M c r f z b).denote w env =
      prefixNat (B.denote w env) (Cap.denote w env) (Lb.denote w env) (q.denote w env)
        (M.denote w env) (c.denote w env) (r.denote w env) (f.denote w env) (z.denote w env)
        (b.denote w env) := by
  simp only [prefixT, prefixNat, denote_ite, denote_eqT, denote_lt, denote_const, denote_packT,
    denote_add, denote_finishT]
  by_cases h1 : b.denote w env = 0 <;> simp [h1] <;>
    by_cases h2 : z.denote w env < Lb.denote w env <;>
    by_cases h3 : 0 < B.denote w env <;>
    by_cases h4 : z.denote w env = 0 <;> simp [h2, h3, h4]

def payloadT (B Cap q M c r f z a b : Term) : Term :=
  ite (mul (leT b B) (leT a (div (sub B b) (const 2))))
    (ite (eqT (sub z (const 1)) (const 0))
      (finishT B Cap q M c r f (add (mul (const 2) a) b))
      (packT M (const 3) c r f (sub z (const 1)) (add (mul (const 2) a) b)))
    (const 0)

theorem denote_payloadT (B Cap q M c r f z a b : Term) (env : List ℕ) :
    (payloadT B Cap q M c r f z a b).denote w env =
      payloadNat (B.denote w env) (Cap.denote w env) (q.denote w env) (M.denote w env)
        (c.denote w env) (r.denote w env) (f.denote w env) (z.denote w env) (a.denote w env)
        (b.denote w env) := by
  simp only [payloadT, payloadNat, denote_ite, denote_mul, denote_leT, denote_div, denote_sub,
    denote_const, denote_eqT, denote_finishT, denote_add, denote_packT]
  by_cases h1 : b.denote w env ≤ B.denote w env <;>
    by_cases h2 : a.denote w env ≤ (B.denote w env - b.denote w env) / 2 <;>
    simp [h1, h2] <;>
    by_cases h3 : z.denote w env - 1 = 0 <;> simp [h3]

/-- The packed transition. -/
def stepT (B Cap Lb q M x b : Term) : Term :=
  ite (eqT (mod x (const 4)) (const 1))
    (ite (lt (mod (div (div x (const 4)) M) M) Cap)
      (prefixT B Cap Lb q M (mod (div x (const 4)) M) (mod (div (div x (const 4)) M) M)
        (mod (div (div (div x (const 4)) M) M) M) (const 0) b)
      (const 0))
    (ite (eqT (mod x (const 4)) (const 2))
      (prefixT B Cap Lb q M (mod (div x (const 4)) M) (mod (div (div x (const 4)) M) M)
        (mod (div (div (div x (const 4)) M) M) M)
        (mod (div (div (div (div x (const 4)) M) M) M) M) b)
      (ite (eqT (mod x (const 4)) (const 3))
        (payloadT B Cap q M (mod (div x (const 4)) M) (mod (div (div x (const 4)) M) M)
          (mod (div (div (div x (const 4)) M) M) M)
          (mod (div (div (div (div x (const 4)) M) M) M) M)
          (div (div (div (div (div x (const 4)) M) M) M) M) b)
        (const 0)))

theorem denote_stepT (B Cap Lb q M x b : Term) (env : List ℕ) :
    (stepT B Cap Lb q M x b).denote w env =
      stepNat (B.denote w env) (Cap.denote w env) (Lb.denote w env) (q.denote w env)
        (M.denote w env) (x.denote w env) (b.denote w env) := by
  simp only [stepT, stepNat, denote_ite, denote_eqT, denote_mod, denote_div, denote_const,
    denote_lt, denote_prefixT, denote_payloadT]
  by_cases h1 : x.denote w env % 4 = 1
  · by_cases hr : x.denote w env / 4 / M.denote w env % M.denote w env < Cap.denote w env <;>
      simp [h1, hr]
  · by_cases h2 : x.denote w env % 4 = 2
    · simp [h1, h2]
    · by_cases h3 : x.denote w env % 4 = 3 <;> simp [h1, h2, h3]

/-- `log₂ c` for `1 ≤ c < 2^(K+1)`: the number of `i < K` with `2^(i+1) ≤ c`. -/
def log2T (K c : Term) : Term :=
  sumT K fun i => lt (const 0) (divPowT (const 2) c (add i (const 1)))

theorem sum_lt_indicator (K L : ℕ) :
    ∑ i ∈ Finset.range K, (if i < L then 1 else 0) = min K L := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; split_ifs <;> omega

theorem log2T_denote (K c : Term) (env : List ℕ) (hc : StableAt w c env)
    (hpos : 1 ≤ c.denote w env) (hlt : c.denote w env < 2 ^ (K.denote w env + 1)) :
    (log2T K c).denote w env = (c.denote w env).log2 := by
  rw [log2T, denote_sumT _ _ env (fun i => if i < (c.denote w env).log2 then 1 else 0)
    (fun acc i => ?_), sum_lt_indicator]
  · have : (c.denote w env).log2 < K.denote w env + 1 :=
      (Nat.log2_lt (by omega)).mpr hlt
    omega
  · simp only [denote_lt, divPowT_denote _ _ _ _ (stableAt_const _ _), denote_add,
      denote_lvl_index, denote_const, hc.cons₂]
    have hne : c.denote w env ≠ 0 := by omega
    by_cases h : i < (c.denote w env).log2
    · rw [if_pos (Nat.div_pos_iff.mpr ⟨by positivity, (Nat.le_log2 hne).mp h⟩), if_pos h]
    · rw [if_neg (fun h' => h ((Nat.le_log2 hne).mpr (Nat.div_pos_iff.mp h').2)), if_neg h]

theorem bitValue_eq_toNat (b : Bool) : BoundedSupportParser.bitValue b = b.toNat := by
  cases b <;> rfl

/-- The parser over the word of candidate `c`. -/
def scanT (B Cap Lb q M K c : Term) : Term :=
  foldT (log2T K c) (const 1) fun acc j => stepT B Cap Lb q M acc (bit c j)

/-- The initial registers of a scan. -/
def initRegs (bound capacity : ℕ) : BoundedSupportParser.Registers bound capacity :=
  { cumulative := ⟨0, by omega⟩, rank := ⟨0, by omega⟩, found := false }

/-- **The scan term computes the packed parser state on the candidate's word.** -/
theorem scanT_denote {bound capacity : ℕ} (query : Fin (bound + 1))
    (B Cap Lb q M K c : Term) (env : List ℕ)
    (hB : StableAt w B env) (hBv : B.denote w env = bound)
    (hCap : StableAt w Cap env) (hCapv : Cap.denote w env = capacity)
    (hLb : StableAt w Lb env) (hLbv : Lb.denote w env = bound.log2)
    (hq : StableAt w q env) (hqv : q.denote w env = query)
    (hM : StableAt w M env) (hMv : M.denote w env = radix bound capacity)
    (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env)
    (hlt : c.denote w env < 2 ^ (K.denote w env + 1)) :
    (scanT B Cap Lb q M K c).denote w env =
      pack ((SupportEncoding.binaryTail (c.denote w env)).foldl (step query)
        (.ready (initRegs bound capacity))) := by
  rw [scanT, denote_foldT, log2T_denote K c env hc hpos hlt, denote_const,
    foldAcc_eq _ env (fun x j => stepNat bound capacity bound.log2 query (radix bound capacity)
      x (BoundedSupportParser.bitValue ((c.denote w env).testBit j))) (fun acc j => by
        rw [denote_stepT]
        simp only [hB.cons₂, hBv, hCap.cons₂, hCapv, hLb.cons₂, hLbv, hq.cons₂, hqv, hM.cons₂,
          hMv, denote_lvl_acc, denote_bit, hc.cons₂, denote_lvl_index, bitValue_eq_toNat])]
  have hpack1 : pack (State.ready (initRegs bound capacity)) = 1 := by
    simp [pack, packFields, initRegs]
  have key := fold_stepNat query (c.denote w env) (c.denote w env).log2
    (State.ready (initRegs bound capacity))
  rw [hpack1] at key
  rw [binaryTail_eq_map]
  exact key

/-- Validity of a packed final state. -/
def validT (x : Term) : Term := eqT (mod x (const 4)) (const 1)
/-- The membership register of a packed final state. -/
def foundT (M x : Term) : Term := mod (div (div (div x (const 4)) M) M) M
/-- The rank register of a packed final state. -/
def rankT (M x : Term) : Term := mod (div (div x (const 4)) M) M

theorem readout {bound capacity : ℕ} (query : Fin (bound + 1)) (input : List Bool)
    (x : ℕ) (hx : x = pack (input.foldl (step query) (.ready (initRegs bound capacity)))) :
    ((x % 4 = 1) ↔
      (BoundedSupportParser.scan bound capacity query (initRegs bound capacity) input).isSome) ∧
    ∀ regs, BoundedSupportParser.scan bound capacity query (initRegs bound capacity) input =
        some regs →
      x / 4 / radix bound capacity / radix bound capacity % radix bound capacity =
          regs.found.toNat ∧
        x / 4 / radix bound capacity % radix bound capacity = regs.rank := by
  rw [← scan_eq_fold]
  subst hx
  set s := input.foldl (step query) (.ready (initRegs bound capacity))
  refine ⟨?_, fun regs h => ?_⟩
  · rw [pack_tag_one]
    rcases s with _ | regs | _ | _ <;> simp [finalize]
  · rcases s with _ | r | _ | _ <;> simp [finalize] at h
    subst h
    exact ⟨pack_ready_found _, pack_ready_rank _⟩

end NtimeDspace.ProgTerm
