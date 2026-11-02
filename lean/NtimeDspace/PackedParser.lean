import NtimeDspace.ParserFold
import NtimeDspace.SupportEncoding

/-!
# Packed parser states

A loop accumulator is one natural number, so a parser state is packed into its
fields with a fixed radix `M`, larger than every register:
`tag + 4 · (cumulative + M · (rank + M · (found + M · (counter + M · acc))))`.
-/

namespace NtimeDspace.ParserFold

open BoundedSupportParser

variable {bound capacity : ℕ}

/-- A radix exceeding every register. -/
def radix (bound capacity : ℕ) : ℕ := bound + capacity + bound.log2 + 3

/-- Pack six fields. -/
def packFields (M t c r f z a : ℕ) : ℕ := t + 4 * (c + M * (r + M * (f + M * (z + M * a))))

/-- The packed form of a state. -/
def pack : State bound capacity → ℕ
  | .fail => 0
  | .ready regs => packFields (radix bound capacity) 1 regs.cumulative regs.rank
      regs.found.toNat 0 0
  | .prefixZ regs zeros => packFields (radix bound capacity) 2 regs.cumulative regs.rank
      regs.found.toNat zeros 0
  | .payload regs remaining acc => packFields (radix bound capacity) 3 regs.cumulative regs.rank
      regs.found.toNat remaining acc

section Extraction

variable {M t c r f z a : ℕ}

theorem packFields_tag (ht : t < 4) : packFields M t c r f z a % 4 = t := by
  unfold packFields; omega

theorem packFields_div4 (ht : t < 4) :
    packFields M t c r f z a / 4 = c + M * (r + M * (f + M * (z + M * a))) := by
  unfold packFields; omega

theorem field_mod (hc : c < M) (rest : ℕ) : (c + M * rest) % M = c := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

theorem field_div (hc : c < M) (rest : ℕ) : (c + M * rest) / M = rest := by
  have hM : 0 < M := by omega
  rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hc, Nat.zero_add]

end Extraction

theorem radix_pos : 0 < radix bound capacity := by unfold radix; omega

theorem cumulative_lt (regs : Registers bound capacity) :
    (regs.cumulative : ℕ) < radix bound capacity := by
  have := regs.cumulative.isLt; unfold radix; omega

theorem rank_lt (regs : Registers bound capacity) : (regs.rank : ℕ) < radix bound capacity := by
  have := regs.rank.isLt; unfold radix; omega

theorem found_lt (regs : Registers bound capacity) : regs.found.toNat < radix bound capacity := by
  have := Bool.toNat_le regs.found; unfold radix; omega

theorem counter_lt (z : Fin (bound.log2 + 1)) : (z : ℕ) < radix bound capacity := by
  have := z.isLt; unfold radix; omega

/-- Accept a completed gap, on fields. -/
def finishNat (B Cap q M c r f gap : ℕ) : ℕ :=
  if 0 < gap ∧ gap ≤ B - c ∧ r < Cap then
    packFields M 1 (c + gap) (r + 1) (if f = 1 ∨ c + gap = q then 1 else 0) 0 0
  else 0

/-- One prefix bit, on fields. -/
def prefixNat (B Cap Lb q M c r f z b : ℕ) : ℕ :=
  if b = 0 then (if z < Lb then packFields M 2 c r f (z + 1) 0 else 0)
  else if 0 < B then (if z = 0 then finishNat B Cap q M c r f 1 else packFields M 3 c r f z 1)
  else 0

/-- One payload bit, on fields. -/
def payloadNat (B Cap q M c r f z a b : ℕ) : ℕ :=
  if b ≤ B ∧ a ≤ (B - b) / 2 then
    (if z - 1 = 0 then finishNat B Cap q M c r f (2 * a + b)
      else packFields M 3 c r f (z - 1) (2 * a + b))
  else 0

/-- The transition on packed states. -/
def stepNat (B Cap Lb q M x b : ℕ) : ℕ :=
  let y := x / 4
  let c := y % M
  let r := y / M % M
  let f := y / M / M % M
  let z := y / M / M / M % M
  let a := y / M / M / M / M
  if x % 4 = 1 then (if r < Cap then prefixNat B Cap Lb q M c r f 0 b else 0)
  else if x % 4 = 2 then prefixNat B Cap Lb q M c r f z b
  else if x % 4 = 3 then payloadNat B Cap q M c r f z a b
  else 0

theorem finishNat_pack (query : Fin (bound + 1)) (regs : Registers bound capacity)
    (gap : Fin (bound + 1)) :
    finishNat bound capacity query (radix bound capacity) regs.cumulative regs.rank
      regs.found.toNat gap = pack (finish query regs gap) := by
  unfold finishNat finish
  by_cases h1 : 0 < gap.val
  · by_cases h2 : gap.val ≤ bound - regs.cumulative.val
    · by_cases h3 : regs.rank.val < capacity
      · rw [if_pos ⟨h1, h2, h3⟩, dif_pos h1, dif_pos h2, dif_pos h3]
        simp only [pack]
        congr 1
        cases regs.found <;> by_cases h4 : regs.cumulative.val + gap.val = query.val <;> simp [h4]
      · rw [if_neg (fun h => h3 h.2.2), dif_pos h1, dif_pos h2, dif_neg h3]; rfl
    · rw [if_neg (fun h => h2 h.2.1), dif_pos h1, dif_neg h2]; rfl
  · rw [if_neg (fun h => h1 h.1), dif_neg h1]; rfl

theorem prefixNat_pack (query : Fin (bound + 1)) (regs : Registers bound capacity)
    (zeros : Fin (bound.log2 + 1)) (bit : Bool) :
    prefixNat bound capacity bound.log2 query (radix bound capacity) regs.cumulative regs.rank
      regs.found.toNat zeros (bitValue bit) = pack (prefixStep query regs zeros bit) := by
  unfold prefixNat
  cases bit with
  | false =>
    simp only [bitValue, Bool.false_eq_true, if_false, if_true, prefixStep]
    by_cases h : zeros.val < bound.log2
    · rw [if_pos h, dif_pos h]; rfl
    · rw [if_neg h, dif_neg h]; rfl
  | true =>
    simp only [bitValue, if_true, one_ne_zero, if_false, prefixStep]
    by_cases hb : 0 < bound
    · rw [if_pos hb, dif_pos hb]
      by_cases hz : zeros.val = 0
      · rw [if_pos hz, dif_pos hz, ← finishNat_pack]
      · rw [if_neg hz, dif_neg hz]; rfl
    · rw [if_neg hb, dif_neg hb]; rfl

theorem payloadNat_pack (query : Fin (bound + 1)) (regs : Registers bound capacity)
    (remaining : Fin (bound.log2 + 1)) (acc : Fin (bound + 1)) (bit : Bool) :
    payloadNat bound capacity query (radix bound capacity) regs.cumulative regs.rank
      regs.found.toNat remaining acc (bitValue bit) =
      pack (payloadStep query regs remaining acc bit) := by
  unfold payloadNat payloadStep appendBit
  by_cases h1 : bitValue bit ≤ bound
  · by_cases h2 : acc.val ≤ (bound - bitValue bit) / 2
    · rw [if_pos ⟨h1, h2⟩, dif_pos h1, dif_pos h2]
      simp only
      by_cases h3 : remaining.val - 1 = 0
      · rw [if_pos h3, dif_pos h3]
        exact finishNat_pack query regs ⟨2 * acc.val + bitValue bit, _⟩
      · rw [if_neg h3, dif_neg h3]; rfl
    · rw [if_neg (fun h => h2 h.2), dif_pos h1, dif_neg h2]; rfl
  · rw [if_neg (fun h => h1 h.1), dif_neg h1]; rfl

/-- **The packed transition is the transition.** -/
theorem stepNat_pack (query : Fin (bound + 1)) (s : State bound capacity) (bit : Bool) :
    stepNat bound capacity bound.log2 query (radix bound capacity) (pack s) (bitValue bit) =
      pack (step query s bit) := by
  rcases s with _ | regs | ⟨regs, zeros⟩ | ⟨regs, remaining, acc⟩
  · simp [stepNat, pack, step]
  · have hc := cumulative_lt regs
    have hr := rank_lt regs
    have hf := found_lt regs
    simp only [stepNat, pack, packFields_tag (by norm_num : 1 < 4), packFields_div4 (by norm_num : 1 < 4),
      field_mod hc, field_div hc, field_mod hr, field_div hr, field_mod hf, field_div hf,
      field_mod (show 0 < radix bound capacity from radix_pos), if_true, step]
    by_cases hroom : regs.rank.val < capacity
    · rw [if_pos hroom, if_pos hroom]
      exact prefixNat_pack query regs ⟨0, by omega⟩ bit
    · rw [if_neg hroom, if_neg hroom]
  · have hc := cumulative_lt regs
    have hr := rank_lt regs
    have hf := found_lt regs
    have hz := counter_lt (capacity := capacity) zeros
    simp only [stepNat, pack, packFields_tag (by norm_num : 2 < 4), packFields_div4 (by norm_num : 2 < 4),
      field_mod hc, field_div hc, field_mod hr, field_div hr, field_mod hf, field_div hf,
      field_mod hz, field_div hz, step]
    simp only [show (2 : ℕ) ≠ 1 by norm_num, if_false, if_true, prefixNat_pack]
    rfl
  · have hc := cumulative_lt regs
    have hr := rank_lt regs
    have hf := found_lt regs
    have hz := counter_lt (capacity := capacity) remaining
    simp only [stepNat, pack, packFields_tag (by norm_num : 3 < 4), packFields_div4 (by norm_num : 3 < 4),
      field_mod hc, field_div hc, field_mod hr, field_div hr, field_mod hf, field_div hf,
      field_mod hz, field_div hz, step]
    simp only [show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true,
      payloadNat_pack]
    rfl

/-- The word of a candidate is the list of its bits below the leading one. -/
theorem binaryTail_eq_map (c : ℕ) :
    SupportEncoding.binaryTail c = (List.range c.log2).map c.testBit := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [SupportEncoding.binaryTail]
    by_cases h : 2 ≤ c
    · rw [dif_pos h, ih (c / 2) (Nat.div_lt_self (by omega) (by omega)),
        show c.log2 = (c / 2).log2 + 1 from by
          rw [Nat.log2_def]; simp [show c ≠ 0 by omega, show ¬ c < 2 by omega]]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1 <;> first
        | (refine List.map_congr_left fun j _ => ?_; simp [Function.comp, Nat.testBit_succ])
        | (rw [Nat.testBit_zero]; cases hb : c.bodd <;> simp [Nat.bodd] at hb ⊢ <;> omega)
        | rfl
    · rw [dif_neg h]
      have : c.log2 = 0 := by rw [Nat.log2_def]; simp [show c < 2 by omega]
      simp [this]

/-- The packed fold over bit positions is the packed parser fold. -/
theorem fold_stepNat (query : Fin (bound + 1)) (c L : ℕ) (s : State bound capacity) :
    (List.range L).foldl (fun x j => stepNat bound capacity bound.log2 query (radix bound capacity)
      x (bitValue (c.testBit j))) (pack s) =
      pack (((List.range L).map c.testBit).foldl (step query) s) := by
  rw [List.foldl_map]
  induction List.range L generalizing s with
  | nil => rfl
  | cons j js ih => rw [List.foldl_cons, List.foldl_cons, stepNat_pack, ih]

/-- Reading the result off a packed final state. -/
theorem pack_tag_one (s : State bound capacity) :
    pack s % 4 = 1 ↔ ∃ regs, s = .ready regs := by
  rcases s with _ | regs | ⟨regs, zeros⟩ | ⟨regs, remaining, acc⟩ <;>
    simp [pack, packFields_tag]

theorem pack_ready_found (regs : Registers bound capacity) :
    pack (State.ready regs) / 4 / radix bound capacity / radix bound capacity %
      radix bound capacity = regs.found.toNat := by
  simp only [pack, packFields_div4 (by norm_num : 1 < 4), field_div (cumulative_lt regs),
    field_div (rank_lt regs), field_mod (found_lt regs)]

theorem pack_ready_rank (regs : Registers bound capacity) :
    pack (State.ready regs) / 4 / radix bound capacity % radix bound capacity = regs.rank := by
  simp only [pack, packFields_div4 (by norm_num : 1 < 4), field_div (cumulative_lt regs),
    field_mod (rank_lt regs)]

end NtimeDspace.ParserFold
