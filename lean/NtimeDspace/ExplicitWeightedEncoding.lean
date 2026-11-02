/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.NetSystemTerm

-- upstream: local-only (explicit input format of the weighted counting application)

/-!
# Fixed-width inputs for weighted constraint counting

An input consists of a unary word width and a list of binary fields. A field
is read directly from the input; the complete input is never packed into an
integer. Out-of-range bits and fields read as zero.

The weighted-system layout has four header fields (`N`, `m`, `p`, `Δ`), followed
by `m` records of `1 + Δ + 2^Δ` fields: arity, padded ports, and residues
indexed by `Δ` bits (unused coordinates repeat the actual truth table).
The encoding layer permits arbitrary fields. Its semantic interpretation and
the bounds on occurrences are separate from the binary representation.
-/

namespace NtimeDspace.ExplicitWeightedEncoding

/-- An explicit list of natural-number fields with a common positive width. -/
structure Record where
  width : ℕ
  fields : List ℕ
  positive_width : 0 < width
  fields_lt : ∀ x ∈ fields, x < 2 ^ width

/-- The payload is little-endian within each field. -/
def payload (r : Record) : List Bool :=
  List.ofFn fun i : Fin (r.fields.length * r.width) =>
    (r.fields.getD (i / r.width) 0).testBit (i % r.width)

def encode (r : Record) : List Bool :=
  List.replicate r.width true ++ false :: payload r

/-- Missing input bits read as zero, including beyond the complete record. -/
def readBit (w : List Bool) (i : ℕ) : ℕ := (w.getD i false).toNat

def readField (w : List Bool) (width index : ℕ) : ℕ :=
  ∑ j ∈ Finset.range width, readBit w (width + 1 + index * width + j) * 2 ^ j

theorem readBit_le_one (w : List Bool) (i : ℕ) : readBit w i ≤ 1 := by
  unfold readBit
  cases w.getD i false <;> decide

theorem readField_lt (w : List Bool) (width index : ℕ) :
    readField w width index < 2 ^ width := by
  unfold readField
  have bound : ∀ k, (∑ j ∈ Finset.range k,
      readBit w (width + 1 + index * width + j) * 2 ^ j) < 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hb := Nat.mul_le_mul_right (2 ^ k)
        (readBit_le_one w (width + 1 + index * width + k))
      omega
  exact bound width

@[simp] theorem payload_length (r : Record) :
    (payload r).length = r.fields.length * r.width := by simp [payload]

@[simp] theorem encode_length (r : Record) :
    (encode r).length = r.width + 1 + r.fields.length * r.width := by
  simp [encode, Nat.add_comm, Nat.add_left_comm]

theorem readBit_encode_header (r : Record) (i : ℕ) (hi : i ≤ r.width) :
    readBit (encode r) i = if i < r.width then 1 else 0 := by
  unfold readBit encode
  by_cases h : i < r.width
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, h]
  · have : i = r.width := by omega
    subst i
    simp [List.getD_eq_getElem?_getD]

theorem readBit_encode_payload (r : Record) (i : ℕ) :
    readBit (encode r) (r.width + 1 + i) =
      ((r.fields.getD (i / r.width) 0).testBit (i % r.width)).toNat := by
  unfold readBit encode
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right,
    List.length_replicate, show r.width ≤ r.width + 1 + i by omega,
    show r.width + 1 + i - r.width = i + 1 by omega,
    List.getElem?_cons_succ]
  by_cases hi : i < r.fields.length * r.width
  · simp [payload, hi]
  · have hdiv : r.fields.length ≤ i / r.width :=
      (Nat.le_div_iff_mul_le r.positive_width).2 (by omega)
    simp [payload, hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none hdiv]

theorem readField_encode (r : Record) (index : ℕ) :
    readField (encode r) r.width index = r.fields.getD index 0 := by
  unfold readField
  have hb : ∀ j < r.width,
      readBit (encode r) (r.width + 1 + index * r.width + j) =
        ((r.fields.getD index 0).testBit j).toNat := by
    intro j hj
    rw [Nat.add_assoc, readBit_encode_payload]
    have hd : (index * r.width + j) / r.width = index := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ r.positive_width,
        Nat.div_eq_of_lt hj, Nat.zero_add]
    simp [hd, Nat.add_mod, Nat.mod_eq_of_lt hj]
  simp_rw [Finset.sum_congr rfl (fun j hj =>
    congrArg (fun x => x * 2 ^ j) (hb j (Finset.mem_range.mp hj)))]
  rw [LocalSim.sum_testBit_eq_mod, Nat.mod_eq_of_lt]
  by_cases hi : index < r.fields.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact r.fields_lt _ (List.getElem_mem hi)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : r.fields.length ≤ index)]

theorem encode_injective : Function.Injective encode := by
  intro r s h
  have hw : r.width = s.width := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with hrs | hsr
    · have hb := congrArg (fun w => readBit w r.width) h
      rw [readBit_encode_header r _ le_rfl,
        readBit_encode_header s _ hrs.le] at hb
      simp [hrs] at hb
    · have hb := congrArg (fun w => readBit w s.width) h
      rw [readBit_encode_header r _ hsr.le,
        readBit_encode_header s _ le_rfl] at hb
      simp [hsr] at hb
  have hlen : r.fields.length = s.fields.length := by
    have hl := congrArg List.length h
    rw [encode_length, encode_length, ← hw] at hl
    exact Nat.eq_of_mul_eq_mul_right r.positive_width (by omega)
  have hf : r.fields = s.fields := by
    apply List.ext_getElem hlen
    intro i hi hj
    have hr := readField_encode r i
    have hs := readField_encode s i
    rw [← hw, ← h] at hs
    rw [List.getD_eq_getElem _ _ hi] at hr
    rw [List.getD_eq_getElem _ _ hj] at hs
    exact hr.symm.trans hs
  cases r
  cases s
  cases hw
  cases hf
  rfl

def embedding : Record ↪ List Bool := ⟨encode, encode_injective⟩

/-- Number of fields occupied by one padded constraint. -/
def rowWidth (maxArity : ℕ) : ℕ := 1 + maxArity + 2 ^ maxArity

def rowStart (maxArity constraint : ℕ) : ℕ := 4 + constraint * rowWidth maxArity

def arityIndex (maxArity constraint : ℕ) : ℕ := rowStart maxArity constraint
def portIndex (maxArity constraint port : ℕ) : ℕ := rowStart maxArity constraint + 1 + port
def weightIndex (maxArity constraint assignment : ℕ) : ℕ :=
  rowStart maxArity constraint + 1 + maxArity + assignment

/-- The precise input-size formula; no field's integer value is charged as unary. -/
theorem encode_length_layout (r : Record) (m maxArity : ℕ)
    (layout : r.fields.length = 4 + m * rowWidth maxArity) :
    (encode r).length = r.width + 1 + (4 + m * (1 + maxArity + 2 ^ maxArity)) * r.width := by
  rw [encode_length, layout, rowWidth]

/-- Polynomial length when the width, arity, truth-table size and constraint
count have a common polynomial bound. Logarithmic arity supplies the table bound. -/
theorem encode_length_le_polynomial (r : Record) (m maxArity N d : ℕ)
    (layout : r.fields.length = 4 + m * rowWidth maxArity)
    (width : r.width ≤ N ^ d) (arity : maxArity ≤ N ^ d)
    (table : 2 ^ maxArity ≤ N ^ d) (constraints : m ≤ N ^ d) :
    (encode r).length ≤ N ^ d + 1 + (4 + N ^ d * (1 + 2 * N ^ d)) * N ^ d := by
  rw [encode_length_layout r m maxArity layout]
  have hrow : 1 + maxArity + 2 ^ maxArity ≤ 1 + 2 * N ^ d := by omega
  have hm := Nat.mul_le_mul constraints hrow
  have hp := Nat.mul_le_mul (Nat.add_le_add_left hm 4) width
  omega

theorem tableSize_le_of_logarithmic_arity {N c maxArity : ℕ} (hN : 0 < N)
    (arity : maxArity ≤ c * N.log2) : 2 ^ maxArity ≤ N ^ c := by
  have hlog : 2 ^ N.log2 ≤ N := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  calc
    2 ^ maxArity ≤ 2 ^ (c * N.log2) := Nat.pow_le_pow_right (by norm_num) arity
    _ = (2 ^ N.log2) ^ c := by rw [Nat.mul_comm, pow_mul]
    _ ≤ N ^ c := Nat.pow_le_pow_left hlog c

/-- Logarithmic field width and arity, together with polynomially many
constraints, give an explicit polynomial bound on the bit input length. -/
theorem encode_length_le_of_logarithmic_arity (r : Record) (m maxArity N c d C : ℕ)
    (hN : 0 < N) (layout : r.fields.length = 4 + m * rowWidth maxArity)
    (width : r.width ≤ C * (N.log2 + 1)) (arity : maxArity ≤ c * N.log2)
    (constraints : m ≤ N ^ d) :
    (encode r).length ≤ C * (N + 1) + 1 +
      (4 + N ^ d * (1 + c * N + N ^ c)) * (C * (N + 1)) := by
  have htable := tableSize_le_of_logarithmic_arity hN arity
  have hwidth : r.width ≤ C * (N + 1) :=
    width.trans (Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.log2_le_self N) 1))
  have harity := arity.trans (Nat.mul_le_mul_left c (Nat.log2_le_self N))
  rw [encode_length_layout r m maxArity layout]
  have hrow : 1 + maxArity + 2 ^ maxArity ≤ 1 + c * N + N ^ c := by omega
  have hm := Nat.mul_le_mul constraints hrow
  have hp := Nat.mul_le_mul (Nat.add_le_add_left hm 4) hwidth
  omega

end NtimeDspace.ExplicitWeightedEncoding
