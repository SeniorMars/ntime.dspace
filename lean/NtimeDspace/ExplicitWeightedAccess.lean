/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.ExplicitWeightedEncoding
import NtimeDspace.TameLib
import NtimeDspace.TameIte

-- upstream: local-only (input accessors of the weighted counting application)

/-!
# Input accessors for the fixed-width weighted counter

The accessors use input-bit queries and small integer offsets. Their `Tm`
certificates bound every intermediate register, including partial field reads.
No accessor stores the complete input as an integer.
-/

namespace NtimeDspace.ProgTerm

open Term ExplicitWeightedEncoding

variable {w : List Bool} {env : List ℕ} {L : ℕ}

/-- Convert the input convention (including end marker `2`) to a zero-padded bit. -/
def readBitT (position : Term) : Term := mod (input position) (const 2)

theorem denote_readBitT (position : Term) (env : List ℕ) :
    (readBitT position).denote w env = readBit w (position.denote w env) := by
  simp only [readBitT, denote_mod, denote_input, denote_const, readBit,
    ProgLang.Prog.inputValue, List.getD_eq_getElem?_getD]
  cases w[position.denote w env]? with
  | none => rfl
  | some b => cases b <;> rfl

theorem StableAt.readBitT {position : Term} (hp : StableAt w position env) :
    StableAt w (readBitT position) env := hp.input.mod (stableAt_const _ _)

theorem tm_readBitT {position : Term} {d : ℕ} (hp : Tm w L d position env)
    (hL : 2 ≤ L) : Tm w L 1 (readBitT position) env :=
  tm_mod_left (t_input hp hL) (t_const (lit_lt_two_pow (by omega) hL))

/-- Read one field, using its low-to-high bits. The exponent is clamped even
outside the loop's range, so the accessor has an unrestricted `TmF` contract. -/
def readFieldT (width index : Term) : Term :=
  sumT width fun j => mul
    (readBitT (add (add (add width (const 1)) (mul index width)) j))
    (pow2 (mod j width))

theorem denote_readFieldT (width index : Term) (hw : StableAt w width env)
    (hi : StableAt w index env) :
    (readFieldT width index).denote w env =
      readField w (width.denote w env) (index.denote w env) := by
  unfold readFieldT readField
  rw [denote_sumT_lt _ _ env
    (fun j => readBit w (width.denote w env + 1 + index.denote w env * width.denote w env + j)
      * 2 ^ j)]
  intro acc j hj
  simp only [denote_mul, denote_readBitT, denote_add, denote_const,
    denote_pow2, denote_mod, hw.cons₂, hi.cons₂]
  have hl : (lvl env.length).denote w (acc :: j :: env) = j := by
    term_simp
  rw [hl, Nat.mod_eq_of_lt hj]

theorem StableAt.readFieldT {width index : Term} (hw : StableAt w width env)
    (hi : StableAt w index env) : StableAt w (readFieldT width index) env := by
  intro pre
  rw [denote_readFieldT _ _ (hw.extend pre) (hi.extend pre),
    denote_readFieldT _ _ hw hi, hw pre, hi pre]

private theorem field_acc_lt (width index : Term) (hw : StableAt w width env) :
    ∀ k ≤ width.denote w env,
      foldAcc w (fun acc j => add acc
        (mul (readBitT (add (add (add width (const 1)) (mul index width)) j))
          (pow2 (mod j width)))) env 0 k < 2 ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    have hk' : k < width.denote w env := by omega
    have ha := ih hk'.le
    rw [foldAcc_succ, denote_add, denote_mul, denote_readBitT,
      denote_pow2, denote_mod, hw.cons₂]
    have hi : (lvl env.length).denote w
        (foldAcc w (fun acc j => add acc
          (mul (readBitT (add (add (add width (const 1)) (mul index width)) j))
            (pow2 (mod j width)))) env 0 k :: k :: env) = k := by term_simp
    have hx : (lvl (env.length + 1)).denote w
        (foldAcc w (fun acc j => add acc
          (mul (readBitT (add (add (add width (const 1)) (mul index width)) j))
            (pow2 (mod j width)))) env 0 k :: k :: env) =
        foldAcc w (fun acc j => add acc
          (mul (readBitT (add (add (add width (const 1)) (mul index width)) j))
            (pow2 (mod j width)))) env 0 k := by simp [denote_lvl]
    rw [hi, hx, Nat.mod_eq_of_lt hk', pow_succ]
    calc
      _ ≤ _ + 1 * 2 ^ k := Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (readBit_le_one w _)) _
      _ < _ := by omega

/-- Field reading has tier one, even for an arbitrary tier-sixteen field index.
Only the field width, rather than the input length, bounds the accumulator. -/
theorem tm_readFieldT {width index : Term}
    (hL : 2 ≤ L) (hw : Tm w L 1 width env) (hws : StableAt w width env)
    (hwp : 0 < width.denote w env) (hwidth : width.denote w env ≤ L)
    (hi : Tm w L 16 index env) : Tm w L 1 (readFieldT width index) env := by
  have h1 : Tm w L 1 (const 1) env := t_const (lit_lt_two_pow (by omega) hL)
  unfold readFieldT sumT
  refine tm_foldT_inv hw (by omega) (tm_const (d := 1) (by positivity) (by omega))
    (db := 3) (fun env' he acc j ha hj => ?_) (by omega) ?_
  · have hwidth' := hw.ext he
    have hws' := hws.extend' he
    have hp : Pos w L width env' := Pos.of_stable hws' (by
      rw [hws.extend'_eq he]; exact hwp)
    have hm := tm_mod hj hwidth' hp
    have hext : ∀ pre, Small L pre → (mod j width).denote w (pre ++ env') < 1 * L := by
      intro pre _
      simp only [denote_mod, hws' pre, one_mul]
      have hv : width.denote w env' ≤ L := by rw [hws.extend'_eq he]; exact hwidth
      exact (Nat.mod_lt _ (by rw [hws.extend'_eq he]; exact hwp)).trans_le hv
    have hpow := t_pow2 hm (by omega) hext (by omega) hL
    have hoff := tm_add
      (tm_add (tm_add hwidth' (h1.ext he) (d := 2) (by omega) (by omega) (by omega) (by omega))
        (tm_mul (hi.ext he) hwidth' (d := 17) (by omega) (by omega))
        (d := 18) (by omega) (by omega) (by omega) (by omega))
      hj (d := 19) (by omega) (by omega) (by omega) (by omega)
    exact tm_add ha (tm_mul (tm_readBitT hoff hL) hpow (d := 2) (by omega) (by omega))
      (by omega) (by omega) (by omega) (by omega)
  · intro pre hp k hk
    simp only [denote_const]
    have hacc := field_acc_lt width index (hws.extend pre) k hk
    have hkL : k ≤ L := by rw [hws pre] at hk; omega
    exact hacc.trans_le (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hkL)

theorem implN_readFieldT {width : Term} (hw : StableAt w width env) :
    ImplN w env (readFieldT width) (readField w (width.denote w env)) := by
  intro pre index hi
  exact ⟨by rw [denote_readFieldT _ _ (hw.extend pre) hi, hw pre],
    (hw.extend pre).readFieldT hi⟩

/-- Scan to the first zero bit, bounded by the explicit input length. -/
def recordWidthT (length : Term) : Term :=
  foldT length (const 0) fun acc _ => add acc (readBitT acc)

private theorem width_acc_le (w : List Bool) (env : List ℕ) (k : ℕ) :
    foldAcc w (fun acc _ => add acc (readBitT acc)) env 0 k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [foldAcc_succ, denote_add, denote_readBitT]
    have hv : (lvl (env.length + 1)).denote w
        (foldAcc w (fun acc _ => add acc (readBitT acc)) env 0 k :: k :: env) =
        foldAcc w (fun acc _ => add acc (readBitT acc)) env 0 k := by term_simp
    rw [hv]
    have := readBit_le_one w (foldAcc w (fun acc _ => add acc (readBitT acc)) env 0 k)
    omega

private theorem width_acc_encode (r : Record) (env : List ℕ) (k : ℕ) :
    foldAcc (encode r) (fun acc _ => add acc (readBitT acc)) env 0 k = min k r.width := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [foldAcc_succ, denote_add, denote_readBitT]
    have hv : (lvl (env.length + 1)).denote (encode r)
        (foldAcc (encode r) (fun acc _ => add acc (readBitT acc)) env 0 k :: k :: env) =
        foldAcc (encode r) (fun acc _ => add acc (readBitT acc)) env 0 k := by term_simp
    rw [hv, ih, readBit_encode_header r _ (min_le_right _ _)]
    split_ifs <;> omega

theorem denote_recordWidthT (r : Record) (length : Term) (env : List ℕ)
    (hl : r.width ≤ length.denote (encode r) env) :
    (recordWidthT length).denote (encode r) env = r.width := by
  simp only [recordWidthT, denote_foldT, denote_const, width_acc_encode,
    min_eq_right hl]

theorem StableAt.recordWidthT {length : Term} (hl : StableAt w length env) :
    StableAt w (recordWidthT length) env := by
  intro pre
  change foldAcc w (fun acc _ => Term.add acc (ProgTerm.readBitT acc)) (pre ++ env) 0
      (length.denote w (pre ++ env)) =
    foldAcc w (fun acc _ => Term.add acc (ProgTerm.readBitT acc)) env 0 (length.denote w env)
  rw [hl pre]
  have hf (env' : List ℕ) (n : ℕ) :
      foldAcc w (fun acc _ => Term.add acc (ProgTerm.readBitT acc)) env' 0 n =
        (List.range n).foldl (fun acc _ => acc + readBit w acc) 0 := by
    apply foldAcc_eq
    intro acc k
    simp only [denote_add, denote_readBitT]
    term_simp
  rw [hf, hf]

theorem tm_recordWidthT {length : Term} (hL : 2 ≤ L)
    (hl : Tm w L 1 length env) : Tm w L 1 (recordWidthT length) env := by
  unfold recordWidthT
  refine tm_foldT_inv hl (by omega) (tm_const (d := 1) (by positivity) (by omega))
    (db := 2) (fun env' _ acc _ ha _ =>
      tm_add ha (tm_readBitT ha hL) (by omega) (by omega) (by omega) (by omega))
    (by omega) ?_
  intro pre hp k hk
  simp only [denote_const]
  exact (width_acc_le w (pre ++ env) k).trans_lt (hk.trans_lt ((hl pre hp).2))

/-- Address calculations use field offsets, never encoded table values. -/
def rowStartT (maxArity constraint : Term) : Term :=
  add (const 4) (mul constraint (add (add (const 1) maxArity) (pow2 maxArity)))

def explicitArityT (width count maxArity constraint : Term) : Term :=
  ite (lt constraint count) (readFieldT width (rowStartT maxArity constraint)) (const 0)

def explicitPortT (width count maxArity constraint port : Term) : Term :=
  ite (lt constraint count) (ite (lt port maxArity)
    (readFieldT width (add (add (rowStartT maxArity constraint) (const 1)) port))
    (const 0)) (const 0)

def explicitWeightT (width count maxArity constraint assignment : Term) : Term :=
  ite (lt constraint count)
    (readFieldT width (add (add (add (rowStartT maxArity constraint) (const 1)) maxArity)
      (mod assignment (pow2 maxArity)))) (const 0)

theorem denote_rowStartT {maxArity constraint : Term} :
    (rowStartT maxArity constraint).denote w env =
      rowStart (maxArity.denote w env) (constraint.denote w env) := by
  simp only [rowStartT, denote_add, denote_mul, denote_const, denote_pow2, rowStart, rowWidth]

theorem StableAt.rowStartT {maxArity constraint : Term}
    (ha : StableAt w maxArity env) (hc : StableAt w constraint env) :
    StableAt w (rowStartT maxArity constraint) env := by
  intro pre
  rw [denote_rowStartT, denote_rowStartT, ha pre, hc pre]

theorem denote_explicitArityT {width count maxArity constraint : Term}
    (hw : StableAt w width env) (ha : StableAt w maxArity env)
    (hc : StableAt w constraint env) :
    (explicitArityT width count maxArity constraint).denote w env =
      if constraint.denote w env < count.denote w env then
        readField w (width.denote w env)
          (arityIndex (maxArity.denote w env) (constraint.denote w env)) else 0 := by
  simp only [explicitArityT, denote_ite, denote_lt, denote_const,
    denote_readFieldT _ _ hw (ha.rowStartT hc), denote_rowStartT, arityIndex]
  split_ifs <;> simp_all

theorem denote_explicitPortT {width count maxArity constraint port : Term}
    (hw : StableAt w width env) (ha : StableAt w maxArity env)
    (hc : StableAt w constraint env) (hp : StableAt w port env) :
    (explicitPortT width count maxArity constraint port).denote w env =
      if constraint.denote w env < count.denote w env ∧ port.denote w env < maxArity.denote w env then
        readField w (width.denote w env)
          (portIndex (maxArity.denote w env) (constraint.denote w env) (port.denote w env)) else 0 := by
  simp only [explicitPortT, denote_ite, denote_lt, denote_const,
    denote_readFieldT _ _ hw (((ha.rowStartT hc).add (stableAt_const _ _)).add hp),
    denote_add, denote_rowStartT, portIndex]
  split_ifs <;> simp_all

theorem denote_explicitWeightT {width count maxArity constraint assignment : Term}
    (hw : StableAt w width env) (ha : StableAt w maxArity env)
    (hc : StableAt w constraint env) (hx : StableAt w assignment env) :
    (explicitWeightT width count maxArity constraint assignment).denote w env =
      if constraint.denote w env < count.denote w env then
        readField w (width.denote w env)
          (weightIndex (maxArity.denote w env) (constraint.denote w env)
            (assignment.denote w env % 2 ^ maxArity.denote w env)) else 0 := by
  have hpow : StableAt w (pow2 maxArity) env := fun pre => by
    rw [denote_pow2, denote_pow2, ha pre]
  simp only [explicitWeightT, denote_ite, denote_lt, denote_const, denote_pow2,
    denote_readFieldT _ _ hw ((((ha.rowStartT hc).add (stableAt_const _ _)).add ha).add (hx.mod hpow)),
    denote_add, denote_mod, denote_pow2, denote_rowStartT, weightIndex]
  split_ifs <;> simp_all

theorem StableAt.explicitArityT {width count maxArity constraint : Term}
    (hw : StableAt w width env) (hm : StableAt w count env)
    (ha : StableAt w maxArity env) (hc : StableAt w constraint env) :
    StableAt w (explicitArityT width count maxArity constraint) env :=
  (hc.lt hm).ite (hw.readFieldT (ha.rowStartT hc)) (stableAt_const _ _)

theorem StableAt.explicitPortT {width count maxArity constraint port : Term}
    (hw : StableAt w width env) (hm : StableAt w count env)
    (ha : StableAt w maxArity env) (hc : StableAt w constraint env)
    (hp : StableAt w port env) :
    StableAt w (explicitPortT width count maxArity constraint port) env :=
  (hc.lt hm).ite ((hp.lt ha).ite
    (hw.readFieldT (((ha.rowStartT hc).add (stableAt_const _ _)).add hp))
    (stableAt_const _ _)) (stableAt_const _ _)

theorem StableAt.explicitWeightT {width count maxArity constraint assignment : Term}
    (hw : StableAt w width env) (hm : StableAt w count env)
    (ha : StableAt w maxArity env) (hc : StableAt w constraint env)
    (hx : StableAt w assignment env) :
    StableAt w (explicitWeightT width count maxArity constraint assignment) env :=
  (hc.lt hm).ite
    (hw.readFieldT ((((ha.rowStartT hc).add (stableAt_const _ _)).add ha).add
      (hx.mod (fun pre => by rw [denote_pow2, denote_pow2, ha pre])))) (stableAt_const _ _)

theorem implN_explicitArityT (r : Record) {width count maxArity : Term}
    (hw : StableAt (encode r) width env) (hwv : width.denote (encode r) env = r.width)
    (hm : StableAt (encode r) count env) (ha : StableAt (encode r) maxArity env) :
    ImplN (encode r) env (explicitArityT width count maxArity)
      (fun e => if e < count.denote (encode r) env then
        r.fields.getD (arityIndex (maxArity.denote (encode r) env) e) 0 else 0) := by
  intro pre constraint hc
  refine ⟨?_, (hw.extend pre).explicitArityT (hm.extend pre) (ha.extend pre) hc⟩
  rw [denote_explicitArityT (hw.extend pre) (ha.extend pre) hc, hw pre, hm pre, ha pre,
    hwv, readField_encode]

theorem implN2_explicitPortT (r : Record) {width count maxArity : Term}
    (hw : StableAt (encode r) width env) (hwv : width.denote (encode r) env = r.width)
    (hm : StableAt (encode r) count env) (ha : StableAt (encode r) maxArity env) :
    ImplN2 (encode r) env (explicitPortT width count maxArity)
      (fun e i => if e < count.denote (encode r) env ∧ i < maxArity.denote (encode r) env then
        r.fields.getD (portIndex (maxArity.denote (encode r) env) e i) 0 else 0) := by
  intro pre constraint port hc hp
  refine ⟨?_, (hw.extend pre).explicitPortT (hm.extend pre) (ha.extend pre) hc hp⟩
  rw [denote_explicitPortT (hw.extend pre) (ha.extend pre) hc hp, hw pre, hm pre, ha pre,
    hwv, readField_encode]

theorem implZ2_explicitWeightT (r : Record) (P : ℕ) {width count maxArity : Term}
    (hw : StableAt (encode r) width env) (hwv : width.denote (encode r) env = r.width)
    (hm : StableAt (encode r) count env) (ha : StableAt (encode r) maxArity env) :
    ImplZ2 (encode r) env P (explicitWeightT width count maxArity)
      (fun e a => if e < count.denote (encode r) env then
        (r.fields.getD (weightIndex (maxArity.denote (encode r) env) e
          (a % 2 ^ maxArity.denote (encode r) env)) 0 : ZMod P) else 0) := by
  intro pre constraint assignment hc hx
  rw [denote_explicitWeightT (hw.extend pre) (ha.extend pre) hc hx, hw pre, hm pre, ha pre,
    hwv, readField_encode]
  split_ifs <;> simp_all

theorem tm_rowStartT {maxArity constraint : Term}
    (hL : 3 ≤ L) (ha : Tm w L 1 maxArity env) (hc : Tm w L 4 constraint env)
    (hp : Tm w L 1 (pow2 maxArity) env) : Tm w L 8 (rowStartT maxArity constraint) env := by
  have h4 : Tm w L 1 (const 4) env := t_const (by
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL)
  have h1 : Tm w L 1 (const 1) env := t_const (lit_lt_two_pow (by omega) (by omega))
  exact tm_add h4 (tm_mul hc
    (tm_add (tm_add h1 ha (d := 2) (by omega) (by omega) (by omega) (by omega)) hp
      (d := 3) (by omega) (by omega) (by omega) (by omega))
    (d := 7) (by omega) (by omega)) (by omega) (by omega) (by omega) (by omega)

/-- The three counter callbacks have tier one for arbitrary tier-four queries.
These bounds include every address calculation and input scan. -/
theorem tm_explicit_accessors {width count maxArity : Term}
    (hL : 3 ≤ L) (hw : Tm w L 1 width env) (hws : StableAt w width env)
    (hwp : 0 < width.denote w env) (hwidth : width.denote w env ≤ L)
    (hm : Tm w L 1 count env) (ha : Tm w L 1 maxArity env)
    (has : StableAt w maxArity env) (hav : maxArity.denote w env < L) :
    TmF w L (explicitArityT width count maxArity) 4 1 env ∧
    TmF2 w L (explicitPortT width count maxArity) 4 4 1 env ∧
    TmF2 w L (explicitWeightT width count maxArity) 4 4 1 env := by
  have hp : Tm w L 1 (pow2 maxArity) env :=
    t_pow2_stable ha (by omega) has (by simpa using hav) (by omega) (by omega)
  have h0 : Tm w L 1 (const 0) env := t_const (by positivity)
  have h1 : Tm w L 1 (const 1) env := t_const (lit_lt_two_pow (by omega) (by omega))
  have read {env' : List ℕ} (he : Ext L env' env) {index : Term}
      (hi : Tm w L 16 index env') : Tm w L 1 (readFieldT width index) env' :=
    tm_readFieldT (by omega) (hw.ext he) (hws.extend' he)
      (by rw [hws.extend'_eq he]; exact hwp)
      (by rw [hws.extend'_eq he]; exact hwidth) hi
  refine ⟨?_, ?_, ?_⟩
  · intro env' he constraint hc
    exact tm_ite (tm_lt (d := 1) hc (hm.ext he) (by omega) (by omega))
      (read he ((tm_rowStartT hL (ha.ext he) hc (hp.ext he)).mono (by omega))) (h0.ext he)
  · intro env' he constraint port hc hi
    have hs := tm_rowStartT hL (ha.ext he) hc (hp.ext he)
    have ha' := tm_add (tm_add hs (h1.ext he) (d := 9) (by omega) (by omega) (by omega) (by omega))
      hi (d := 10) (by omega) (by omega) (by omega) (by omega)
    exact tm_ite (tm_lt (d := 1) hc (hm.ext he) (by omega) (by omega))
      (tm_ite (tm_lt (d := 1) hi (ha.ext he) (by omega) (by omega))
        (read he (ha'.mono (by omega))) (h0.ext he)) (h0.ext he)
  · intro env' he constraint assignment hc hx
    have hs := tm_rowStartT hL (ha.ext he) hc (hp.ext he)
    have ha' := tm_add
      (tm_add (tm_add hs (h1.ext he) (d := 9) (by omega) (by omega) (by omega) (by omega))
        (ha.ext he) (d := 10) (by omega) (by omega) (by omega) (by omega))
      (tm_mod_left hx (hp.ext he)) (d := 11) (by omega) (by omega) (by omega) (by omega)
    exact tm_ite (tm_lt (d := 1) hc (hm.ext he) (by omega) (by omega))
      (read he (ha'.mono (by omega))) (h0.ext he)

end NtimeDspace.ProgTerm
