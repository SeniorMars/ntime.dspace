import NtimeDspace.SupportEncoding

/-!
# Bounded streaming parsing of gamma-coded supports

The parser retains only bounded natural-number registers and an immutable input
suffix. It never constructs decoded payload, gap, or support lists. Overflow
guards precede multiplication, increment, and cumulative-index addition.

These are executable arithmetic transition functions, with bounds for invalid
inputs as well as valid encodings. A refinement to a concrete tape machine and
a work-space analysis are still separate obligations.
-/

namespace NtimeDspace.BoundedSupportParser

open SupportEncoding

def bitValue (bit : Bool) : ℕ := if bit then 1 else 0

/-- The comparison is performed before the enlarged accumulator is formed. -/
def appendBit (bound : ℕ) (accumulator : Fin (bound + 1)) (bit : Bool) :
    Option (Fin (bound + 1)) :=
  if low : bitValue bit ≤ bound then
    if room : accumulator.val ≤ (bound - bitValue bit) / 2 then
      some ⟨2 * accumulator.val + bitValue bit, by
        have h := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp room
        omega⟩
    else none
  else none

theorem appendBit_of_fits (bound : ℕ) (accumulator : Fin (bound + 1)) (bit : Bool)
    (fits : 2 * accumulator.val + bitValue bit ≤ bound) :
    appendBit bound accumulator bit =
      some ⟨2 * accumulator.val + bitValue bit, by omega⟩ := by
  have low : bitValue bit ≤ bound := by omega
  have room : accumulator.val ≤ (bound - bitValue bit) / 2 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by omega)
  simp only [appendBit, dite_eq_left low, dite_eq_left room]

theorem appendBit_of_overflow (bound : ℕ) (accumulator : Fin (bound + 1)) (bit : Bool)
    (overflow : bound < 2 * accumulator.val + bitValue bit) :
    appendBit bound accumulator bit = none := by
  unfold appendBit
  split_ifs with low room
  · have h := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp room
    omega
  all_goals rfl

/-- A specification fold only; the parser does not build its bit list. -/
def foldBits : ℕ → List Bool → ℕ
  | accumulator, [] => accumulator
  | accumulator, bit :: bits => foldBits (2 * accumulator + bitValue bit) bits

theorem foldBits_ge (accumulator : ℕ) (bits : List Bool) :
    accumulator ≤ foldBits accumulator bits := by
  induction bits generalizing accumulator with
  | nil => rfl
  | cons bit bits ih =>
    exact (by omega : accumulator ≤ 2 * accumulator + bitValue bit).trans (ih _)

theorem foldBits_append (accumulator : ℕ) (first second : List Bool) :
    foldBits accumulator (first ++ second) = foldBits (foldBits accumulator first) second := by
  induction first generalizing accumulator with
  | nil => rfl
  | cons bit bits ih => exact ih _

theorem foldBits_reverse (bits : List Bool) :
    foldBits 1 bits.reverse = binaryValue bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    rw [List.reverse_cons, foldBits_append, ih]
    cases bit <;> simp [foldBits, binaryValue, Nat.bit_val, bitValue]

/-- Read a bounded payload, returning its integer and the untouched suffix.
The payload counter and accumulator remain in finite bounded types throughout. -/
def readPayload (bound : ℕ) (remaining : Fin (bound.log2 + 1))
    (accumulator : Fin (bound + 1)) (input : List Bool) :
    Option (Fin (bound + 1) × List Bool) :=
  if finished : remaining.val = 0 then some (accumulator, input)
  else match input with
    | [] => none
    | bit :: rest =>
      match appendBit bound accumulator bit with
      | none => none
      | some next => readPayload bound ⟨remaining.val - 1, by omega⟩ next rest
termination_by input.length

theorem readPayload_append (bound : ℕ) (payload rest : List Bool)
    (length_bound : payload.length ≤ bound.log2) (accumulator : Fin (bound + 1))
    (value_bound : foldBits accumulator.val payload ≤ bound) :
    readPayload bound ⟨payload.length, by omega⟩ accumulator (payload ++ rest) =
      some (⟨foldBits accumulator.val payload, by omega⟩, rest) := by
  induction payload generalizing accumulator with
  | nil =>
    rw [readPayload.eq_def]
    simp [foldBits]
  | cons bit bits ih =>
    have fits : 2 * accumulator.val + bitValue bit ≤ bound :=
      (foldBits_ge _ bits).trans value_bound
    have step := appendBit_of_fits bound accumulator bit fits
    simp only [List.length_cons, List.cons_append, readPayload, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceDIte, step, Nat.add_sub_cancel]
    exact ih (by simp only [List.length_cons] at length_bound; omega)
      ⟨2 * accumulator.val + bitValue bit, by omega⟩ value_bound

/-- Count initial zeros, bounded by `log₂ bound`, before reading the payload. -/
def readPrefix (bound : ℕ) (zeros : Fin (bound.log2 + 1)) (input : List Bool) :
    Option (Fin (bound + 1) × List Bool) :=
  match input with
  | [] => none
  | false :: rest =>
    if room : zeros.val < bound.log2 then
      readPrefix bound ⟨zeros.val + 1, by omega⟩ rest
    else none
  | true :: rest =>
    if positive : 0 < bound then readPayload bound zeros ⟨1, by omega⟩ rest else none

theorem readPrefix_replicate (bound count : ℕ) (zeros : Fin (bound.log2 + 1))
    (positive : 0 < bound) (fits : zeros.val + count ≤ bound.log2) (input : List Bool) :
    readPrefix bound zeros (List.replicate count false ++ true :: input) =
      readPayload bound ⟨zeros.val + count, by omega⟩ ⟨1, by omega⟩ input := by
  induction count generalizing zeros with
  | zero => simp [readPrefix, positive]
  | succ count ih =>
    have room : zeros.val < bound.log2 := by omega
    simp only [List.replicate_succ, List.cons_append, readPrefix, dite_eq_left room]
    rw [ih _ (by dsimp; omega)]
    congr 1
    apply Fin.ext
    simp
    omega

def gamma (bound : ℕ) (input : List Bool) : Option (Fin (bound + 1) × List Bool) :=
  readPrefix bound ⟨0, by omega⟩ input

/-- The bounded parser agrees with the existing gamma codec on every positive
integer within its declared limit, preserving arbitrary trailing bits. -/
theorem gamma_encode_append (bound value : ℕ) (positive : 0 < value)
    (fits : value ≤ bound) (rest : List Bool) :
    gamma bound (gammaEncode value ++ rest) = some (⟨value, by omega⟩, rest) := by
  have bound_positive : 0 < bound := positive.trans_le fits
  have logs : value.log2 ≤ bound.log2 :=
    (Nat.le_log2 bound_positive.ne').mpr ((Nat.log2_self_le positive.ne').trans fits)
  unfold gamma gammaEncode
  rw [List.append_assoc, List.cons_append,
    readPrefix_replicate bound (binaryTail value).length _ bound_positive
      (by simpa only [Fin.val_zero, Nat.zero_add, binaryTail_length] using logs)]
  have length_bound : (binaryTail value).reverse.length ≤ bound.log2 := by
    simpa only [List.length_reverse, binaryTail_length] using logs
  have val : foldBits 1 (binaryTail value).reverse = value :=
    (foldBits_reverse _).trans (binaryValue_binaryTail value positive)
  have h := readPayload_append bound (binaryTail value).reverse rest length_bound
    ⟨1, by omega⟩ (by simpa only [Fin.val_mk, val] using fits)
  simpa only [Fin.val_zero, Nat.zero_add, List.length_reverse, val] using h

/-- Every payload call, including calls on malformed candidates, has bounded
registers by construction. The input is an immutable suffix, not a decoded list. -/
theorem payload_register_bounds (bound : ℕ) (remaining : Fin (bound.log2 + 1))
    (accumulator : Fin (bound + 1)) :
    remaining.val ≤ bound.log2 ∧ accumulator.val ≤ bound := by
  exact ⟨Nat.le_of_lt_succ remaining.isLt, Nat.le_of_lt_succ accumulator.isLt⟩

theorem gamma_output_bound (bound : ℕ) (input rest : List Bool) (value : Fin (bound + 1))
    (_accepted : gamma bound input = some (value, rest)) : value.val ≤ bound :=
  Nat.le_of_lt_succ value.isLt

theorem appendBit_value (bound : ℕ) (accumulator next : Fin (bound + 1)) (bit : Bool)
    (accepted : appendBit bound accumulator bit = some next) :
    next.val = 2 * accumulator.val + bitValue bit := by
  unfold appendBit at accepted
  split_ifs at accepted with low room
  · exact (congrArg Fin.val (Option.some.inj accepted)).symm

/-- Every accepted payload is exactly a prefix of the original input of the
requested length; the existential list occurs only in this specification. -/
theorem readPayload_sound (bound : ℕ) (remaining : Fin (bound.log2 + 1))
    (accumulator value : Fin (bound + 1)) (input rest : List Bool)
    (accepted : readPayload bound remaining accumulator input = some (value, rest)) :
    ∃ payload, input = payload ++ rest ∧ payload.length = remaining.val ∧
      value.val = foldBits accumulator.val payload := by
  induction input generalizing remaining accumulator with
  | nil =>
    rw [readPayload.eq_def] at accepted
    split_ifs at accepted with finished
    · have pair := Option.some.inj accepted
      have values := congrArg Prod.fst pair
      have suffix := congrArg Prod.snd pair
      refine ⟨[], ?_, ?_, ?_⟩
      · simpa only [List.nil_append] using suffix
      · exact finished.symm
      · simpa only [foldBits] using (congrArg Fin.val values).symm
  | cons bit input ih =>
    rw [readPayload.eq_def] at accepted
    split_ifs at accepted with finished
    · have pair := Option.some.inj accepted
      have values := congrArg Prod.fst pair
      have suffix := congrArg Prod.snd pair
      refine ⟨[], ?_, ?_, ?_⟩
      · simpa only [List.nil_append] using suffix
      · exact finished.symm
      · simpa only [foldBits] using (congrArg Fin.val values).symm
    · cases step : appendBit bound accumulator bit with
      | none => simp only [step] at accepted; contradiction
      | some next =>
        simp only [step] at accepted
        obtain ⟨payload, suffix, length, result⟩ := ih _ next accepted
        refine ⟨bit :: payload, by simp only [List.cons_append, suffix], ?_, ?_⟩
        · simp only [List.length_cons]
          dsimp at length
          omega
        · rw [foldBits, ← appendBit_value bound accumulator next bit step]
          exact result

theorem binaryValue_positive (bits : List Bool) : 0 < binaryValue bits := by
  induction bits with
  | nil => decide
  | cons bit bits ih =>
    cases bit <;> simp only [binaryValue, Nat.bit_val, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem binaryTail_binaryValue (bits : List Bool) : binaryTail (binaryValue bits) = bits := by
  induction bits with
  | nil => simp [binaryValue, binaryTail]
  | cons bit bits ih =>
    have positive := binaryValue_positive bits
    have two : 2 ≤ Nat.bit bit (binaryValue bits) := by
      cases bit <;> simp only [Nat.bit_val, Bool.toNat_false, Bool.toNat_true] <;> omega
    rw [binaryValue, binaryTail, dite_eq_left two, Nat.bodd_bit, Nat.bit_div_two, ih]

theorem gammaEncode_foldBits (payload : List Bool) :
    gammaEncode (foldBits 1 payload) =
      List.replicate payload.length false ++ true :: payload := by
  have value := foldBits_reverse payload.reverse
  simp only [List.reverse_reverse] at value
  rw [value, gammaEncode, binaryTail_binaryValue, List.length_reverse, List.reverse_reverse]

theorem readPrefix_sound (bound : ℕ) (zeros : Fin (bound.log2 + 1))
    (input rest : List Bool) (value : Fin (bound + 1))
    (accepted : readPrefix bound zeros input = some (value, rest)) :
    ∃ count payload, input = List.replicate count false ++ true :: (payload ++ rest) ∧
      payload.length = zeros.val + count ∧ value.val = foldBits 1 payload := by
  induction input generalizing zeros with
  | nil => simp only [readPrefix] at accepted; contradiction
  | cons bit input ih =>
    cases bit with
    | false =>
      rw [readPrefix] at accepted
      split_ifs at accepted with room
      · obtain ⟨count, payload, suffix, length, result⟩ := ih _ accepted
        refine ⟨count + 1, payload, ?_, ?_, result⟩
        · simp only [List.replicate_succ, List.cons_append, suffix]
        · dsimp at length
          omega
    | true =>
      rw [readPrefix] at accepted
      split_ifs at accepted with positive
      · obtain ⟨payload, suffix, length, result⟩ := readPayload_sound bound zeros _ value input rest accepted
        exact ⟨0, payload, by simpa only [List.replicate_zero, List.nil_append] using congrArg (true :: ·) suffix,
          by simpa only [Nat.add_zero] using length, result⟩

/-- Accepted gamma input is a canonical positive codeword followed by exactly
the reported suffix, even when the original candidate was arbitrary. -/
theorem gamma_sound (bound : ℕ) (input rest : List Bool) (value : Fin (bound + 1))
    (accepted : gamma bound input = some (value, rest)) :
    0 < value.val ∧ value.val ≤ bound ∧ input = gammaEncode value.val ++ rest := by
  obtain ⟨count, payload, suffix, length, result⟩ := readPrefix_sound bound _ input rest value accepted
  have positive : 0 < value.val := by
    have h := foldBits_ge 1 payload
    omega
  refine ⟨positive, Nat.le_of_lt_succ value.isLt, ?_⟩
  rw [suffix, result, gammaEncode_foldBits, List.append_assoc, List.cons_append]
  congr 2
  simpa only [Fin.val_mk, Nat.zero_add] using length.symm

/-- Registers retained between successive codewords. -/
@[ext]
structure Registers (bound capacity : ℕ) where
  cumulative : Fin (bound + 1)
  rank : Fin (capacity + 1)
  found : Bool
  deriving DecidableEq

/-- Scan to the end while retaining only the cumulative index, number of
entries, and query-membership bit. Both rank and index guards precede addition. -/
def scan (bound capacity : ℕ) (query : Fin (bound + 1)) (state : Registers bound capacity)
    (input : List Bool) : Option (Registers bound capacity) :=
  if finished : input = [] then some state
  else if room : state.rank.val < capacity then
    match gamma bound input with
    | none => none
    | some (gap, rest) =>
      if positive : 0 < gap.val then
        if fits : gap.val ≤ bound - state.cumulative.val then
          scan bound capacity query
            { cumulative := ⟨state.cumulative.val + gap.val, by
                have h := state.cumulative.isLt
                omega⟩
              rank := ⟨state.rank.val + 1, by omega⟩
              found := state.found || decide (state.cumulative.val + gap.val = query.val) } rest
        else none
      else none
  else none
termination_by capacity - state.rank.val
decreasing_by
  omega

theorem scan_encode (bound capacity : ℕ) (query : Fin (bound + 1))
    (gaps : List ℕ) (positive : ∀ gap ∈ gaps, 0 < gap)
    (state : Registers bound capacity)
    (total_bound : state.cumulative.val + gaps.sum ≤ bound)
    (rank_bound : state.rank.val + gaps.length ≤ capacity) :
    scan bound capacity query state (encodeGaps gaps) = some
      { cumulative := ⟨state.cumulative.val + gaps.sum, by omega⟩
        rank := ⟨state.rank.val + gaps.length, by omega⟩
        found := state.found || decide (query.val ∈ supportFromGaps state.cumulative.val gaps) } := by
  induction gaps generalizing state with
  | nil =>
    rw [encodeGaps, scan]
    simp [supportFromGaps]
  | cons gap gaps ih =>
    have gap_positive : 0 < gap := positive gap (by simp)
    have tail_positive : ∀ g ∈ gaps, 0 < g := fun g hg => positive g (by simp [hg])
    have room : state.rank.val < capacity := by
      simp only [List.length_cons] at rank_bound
      omega
    have gap_bound : gap ≤ bound := by
      simp only [List.sum_cons] at total_bound
      omega
    have fits : gap ≤ bound - state.cumulative.val := by
      simp only [List.sum_cons] at total_bound
      omega
    have nonempty : gammaEncode gap ++ encodeGaps gaps ≠ [] := by
      intro empty
      exact gammaEncode_nonempty gap (List.append_eq_nil_iff.mp empty).1
    rw [encodeGaps, scan, dite_eq_right nonempty, dite_eq_left room,
      gamma_encode_append bound gap gap_positive gap_bound]
    simp only [dite_eq_left gap_positive, dite_eq_left fits]
    rw [ih tail_positive _ (by simp only [List.sum_cons] at total_bound; dsimp; omega)
      (by simp only [List.length_cons] at rank_bound; dsimp; omega)]
    apply congrArg some
    apply Registers.ext
    · apply Fin.ext
      simp only [List.sum_cons]
      omega
    · apply Fin.ext
      simp only [List.length_cons]
      omega
    · simp [supportFromGaps, Bool.or_assoc, eq_comm]

def lookup (bound capacity : ℕ) (query : Fin (bound + 1)) (input : List Bool) :
    Option Bool :=
  (scan bound capacity query
    { cumulative := ⟨0, by omega⟩, rank := ⟨0, by omega⟩, found := false } input).map
      Registers.found

/-- Membership in the cumulative support is computed directly from its gap
code, without constructing the decoded support. -/
theorem lookup_encodeGaps (bound capacity : ℕ) (query : Fin (bound + 1))
    (gaps : List ℕ) (positive : ∀ gap ∈ gaps, 0 < gap)
    (total_bound : gaps.sum ≤ bound) (rank_bound : gaps.length ≤ capacity) :
    lookup bound capacity query (encodeGaps gaps) =
      some (decide (query.val ∈ supportFromGaps 0 gaps)) := by
  unfold lookup
  rw [scan_encode bound capacity query gaps positive _
    (by simpa only [Fin.val_mk, Nat.zero_add] using total_bound)
    (by simpa only [Fin.val_mk, Nat.zero_add] using rank_bound)]
  rfl

theorem gapsFromSupport_length (indices : List ℕ) (start : ℕ) :
    (gapsFromSupport start indices).length = indices.length := by
  induction indices generalizing start with
  | nil => rfl
  | cons index indices ih => simp only [gapsFromSupport, List.length_cons, ih]

/-- The telescoping gap sum stays within the largest permitted support index. -/
theorem gapsFromSupport_sum_le (bound : ℕ) (indices : List ℕ)
    (sorted : indices.Pairwise (· < ·)) (start : ℕ) (start_bound : start ≤ bound)
    (above : ∀ index ∈ indices, start < index)
    (bounded : ∀ index ∈ indices, index ≤ bound) :
    start + (gapsFromSupport start indices).sum ≤ bound := by
  induction indices generalizing start with
  | nil => simpa only [gapsFromSupport, List.sum_nil, Nat.add_zero] using start_bound
  | cons index indices ih =>
    have ordered := List.pairwise_cons.mp sorted
    have index_bound := bounded index (by simp)
    have index_above := above index (by simp)
    have tail_bound : ∀ i ∈ indices, i ≤ bound := fun i hi => bounded i (by simp [hi])
    have tail := ih ordered.2 index index_bound ordered.1 tail_bound
    simp only [gapsFromSupport, List.sum_cons]
    omega

/-- Direct membership lookup for the manuscript's sorted-support codec. -/
theorem lookup_encodeSupport (bound capacity : ℕ) (query : Fin (bound + 1))
    (indices : List ℕ) (sorted : indices.Pairwise (· < ·))
    (positive : ∀ index ∈ indices, 0 < index)
    (bounded : ∀ index ∈ indices, index ≤ bound) (count : indices.length ≤ capacity) :
    lookup bound capacity query (encodeSupport indices) = some (decide (query.val ∈ indices)) := by
  unfold encodeSupport
  rw [lookup_encodeGaps bound capacity query (gapsFromSupport 0 indices)
    (gapsFromSupport_pos indices sorted 0 positive)
    (by simpa only [Nat.zero_add] using
      gapsFromSupport_sum_le bound indices sorted 0 (Nat.zero_le _) positive bounded)
    (by simpa only [gapsFromSupport_length] using count)]
  rw [supportFromGaps_gapsFromSupport indices sorted 0 positive]

/-- Bounds on every register in every scan call, regardless of whether its
candidate bit string is valid. All recursive calls retain these same types. -/
theorem scan_register_bounds (bound capacity : ℕ) (query : Fin (bound + 1))
    (state : Registers bound capacity) :
    query.val ≤ bound ∧ state.cumulative.val ≤ bound ∧ state.rank.val ≤ capacity := by
  exact ⟨Nat.le_of_lt_succ query.isLt,
    Nat.le_of_lt_succ state.cumulative.isLt, Nat.le_of_lt_succ state.rank.isLt⟩

theorem scan_output_bounds (bound capacity : ℕ) (query : Fin (bound + 1))
    (state result : Registers bound capacity) (input : List Bool)
    (_accepted : scan bound capacity query state input = some result) :
    result.cumulative.val ≤ bound ∧ result.rank.val ≤ capacity := by
  exact ⟨Nat.le_of_lt_succ result.cumulative.isLt, Nat.le_of_lt_succ result.rank.isLt⟩

/-- Every successful scan of an arbitrary candidate is a full canonical
positive-gap encoding, with the exact index, entry count, and membership bit. -/
theorem scan_sound (bound capacity : ℕ) (query : Fin (bound + 1))
    (state result : Registers bound capacity) (input : List Bool)
    (accepted : scan bound capacity query state input = some result) :
    ∃ gaps : List ℕ, (∀ gap ∈ gaps, 0 < gap) ∧ input = encodeGaps gaps ∧
      result.cumulative.val = state.cumulative.val + gaps.sum ∧
      result.rank.val = state.rank.val + gaps.length ∧
      result.found = (state.found || decide (query.val ∈ supportFromGaps state.cumulative.val gaps)) := by
  rw [scan] at accepted
  split_ifs at accepted with finished room
  · have same := Option.some.inj accepted
    subst result
    exact ⟨[], by simp, finished, by simp, by simp, by simp [supportFromGaps]⟩
  · cases decoded : gamma bound input with
    | none => simp only [decoded] at accepted; contradiction
    | some pair =>
      rcases pair with ⟨gap, rest⟩
      simp only [decoded] at accepted
      split_ifs at accepted with positive fits
      obtain ⟨gaps, gaps_positive, encoded, total, count, member⟩ :=
        scan_sound bound capacity query _ result rest accepted
      obtain ⟨_, _, codePrefix⟩ := gamma_sound bound input rest gap decoded
      refine ⟨gap.val :: gaps, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact positive
        · exact gaps_positive g hg
      · rw [encodeGaps, ← encoded]
        exact codePrefix
      · simpa only [List.sum_cons, Nat.add_assoc] using total
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using count
      · simpa [supportFromGaps, Bool.or_assoc, eq_comm] using member
termination_by capacity - state.rank.val
decreasing_by omega

theorem supportFromGaps_length (start : ℕ) (gaps : List ℕ) :
    (supportFromGaps start gaps).length = gaps.length := by
  induction gaps generalizing start with
  | nil => rfl
  | cons gap gaps ih => simp only [supportFromGaps, List.length_cons, ih]

theorem supportFromGaps_le_sum (start : ℕ) (gaps : List ℕ) (index : ℕ)
    (member : index ∈ supportFromGaps start gaps) : index ≤ start + gaps.sum := by
  induction gaps generalizing start with
  | nil => simp only [supportFromGaps, List.not_mem_nil] at member
  | cons gap gaps ih =>
    simp only [supportFromGaps, List.mem_cons] at member
    simp only [List.sum_cons]
    rcases member with same | member
    · omega
    · have tail := ih (start + gap) member
      omega

/-- The bounded canonical supports accepted by the external lookup interface. -/
def ValidSupport (bound capacity : ℕ) (indices : List ℕ) : Prop :=
  indices.Pairwise (· < ·) ∧ (∀ index ∈ indices, 0 < index) ∧
    (∀ index ∈ indices, index ≤ bound) ∧ indices.length ≤ capacity

/-- Successful membership lookup implies a valid canonical bounded support.
Thus malformed candidates cannot silently contribute an unrelated answer. -/
theorem lookup_sound (bound capacity : ℕ) (query : Fin (bound + 1))
    (input : List Bool) (found : Bool) (accepted : lookup bound capacity query input = some found) :
    ∃ indices : List ℕ, ValidSupport bound capacity indices ∧ input = encodeSupport indices ∧
      found = decide (query.val ∈ indices) := by
  let initial : Registers bound capacity :=
    { cumulative := ⟨0, by omega⟩, rank := ⟨0, by omega⟩, found := false }
  change (scan bound capacity query initial input).map Registers.found = some found at accepted
  cases scanned : scan bound capacity query initial input with
  | none => simp only [scanned, Option.map_none] at accepted; contradiction
  | some result =>
    simp only [scanned, Option.map_some, Option.some.injEq] at accepted
    obtain ⟨gaps, positive, encoded, total, count, member⟩ :=
      scan_sound bound capacity query initial result input scanned
    refine ⟨supportFromGaps 0 gaps, ?_, ?_, ?_⟩
    · refine ⟨supportFromGaps_strict gaps positive 0,
        fun index hi => supportFromGaps_gt gaps positive 0 index hi, ?_, ?_⟩
      · intro index hi
        have le_sum := supportFromGaps_le_sum 0 gaps index hi
        have bounded := result.cumulative.isLt
        dsimp [initial] at total
        omega
      · rw [supportFromGaps_length]
        have bounded := result.rank.isLt
        dsimp [initial] at count
        omega
    · rw [encodeSupport, gapsFromSupport_supportFromGaps]
      exact encoded
    · simpa only [initial, Bool.false_or] using accepted.symm.trans member

theorem lookup_some_iff (bound capacity : ℕ) (query : Fin (bound + 1))
    (input : List Bool) (found : Bool) :
    lookup bound capacity query input = some found ↔
      ∃ indices : List ℕ, ValidSupport bound capacity indices ∧ input = encodeSupport indices ∧
        found = decide (query.val ∈ indices) := by
  constructor
  · exact lookup_sound bound capacity query input found
  · rintro ⟨indices, ⟨sorted, positive, bounded, count⟩, rfl, rfl⟩
    exact lookup_encodeSupport bound capacity query indices sorted positive bounded count

/-- Each successful candidate has exactly one valid support interpretation. -/
theorem lookup_sound_unique (bound capacity : ℕ) (query : Fin (bound + 1))
    (input : List Bool) (found : Bool) (accepted : lookup bound capacity query input = some found) :
    ∃! indices : List ℕ, ValidSupport bound capacity indices ∧ input = encodeSupport indices ∧
      found = decide (query.val ∈ indices) := by
  obtain ⟨indices, valid, encoded, answer⟩ := lookup_sound bound capacity query input found accepted
  refine ⟨indices, ⟨valid, encoded, answer⟩, ?_⟩
  intro other other_valid
  exact encodeSupport_injective other_valid.1.1 valid.1 other_valid.1.2.1 valid.2.1
    (other_valid.2.1.symm.trans encoded)

/-- A second bounded pass finds the query's one-based ordinal. Zero means the
query is absent. This helper may stop early; `lookupOrdinal` validates first. -/
def seekOrdinal (bound capacity : ℕ) (query cumulative : Fin (bound + 1))
    (rank : Fin (capacity + 1)) (input : List Bool) : Option (Fin (capacity + 1)) :=
  if finished : input = [] then some ⟨0, by omega⟩
  else if room : rank.val < capacity then
    match gamma bound input with
    | none => none
    | some (gap, rest) =>
      if positive : 0 < gap.val then
        if fits : gap.val ≤ bound - cumulative.val then
          if cumulative.val + gap.val = query.val then some ⟨rank.val + 1, by omega⟩
          else seekOrdinal bound capacity query
            ⟨cumulative.val + gap.val, by have h := cumulative.isLt; omega⟩
            ⟨rank.val + 1, by omega⟩ rest
        else none
      else none
  else none
termination_by capacity - rank.val
decreasing_by omega

theorem seekOrdinal_encode (bound capacity : ℕ) (query cumulative : Fin (bound + 1))
    (rank : Fin (capacity + 1)) (gaps : List ℕ)
    (positive : ∀ gap ∈ gaps, 0 < gap)
    (total_bound : cumulative.val + gaps.sum ≤ bound)
    (rank_bound : rank.val + gaps.length ≤ capacity) :
    ∃ ordinal : Fin (capacity + 1),
      seekOrdinal bound capacity query cumulative rank (encodeGaps gaps) = some ordinal ∧
      ordinal.val = if query.val ∈ supportFromGaps cumulative.val gaps then
        rank.val + (supportFromGaps cumulative.val gaps).idxOf query.val + 1 else 0 := by
  induction gaps generalizing cumulative rank with
  | nil =>
    refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · rw [encodeGaps, seekOrdinal, dite_eq_left rfl]
    · simp only [supportFromGaps, List.not_mem_nil, ↓reduceIte]
  | cons gap gaps ih =>
    have gap_positive : 0 < gap := positive gap (by simp)
    have tail_positive : ∀ g ∈ gaps, 0 < g := fun g hg => positive g (by simp [hg])
    have room : rank.val < capacity := by
      simp only [List.length_cons] at rank_bound
      omega
    have gap_bound : gap ≤ bound := by
      simp only [List.sum_cons] at total_bound
      omega
    have fits : gap ≤ bound - cumulative.val := by
      simp only [List.sum_cons] at total_bound
      omega
    have nonempty : gammaEncode gap ++ encodeGaps gaps ≠ [] := by
      intro empty
      exact gammaEncode_nonempty gap (List.append_eq_nil_iff.mp empty).1
    rw [encodeGaps, seekOrdinal, dite_eq_right nonempty, dite_eq_left room,
      gamma_encode_append bound gap gap_positive gap_bound]
    simp only [dite_eq_left gap_positive, dite_eq_left fits]
    by_cases hit : cumulative.val + gap = query.val
    · rw [ite_eq_left hit]
      refine ⟨⟨rank.val + 1, by omega⟩, rfl, ?_⟩
      simp [supportFromGaps, hit]
    · rw [ite_eq_right hit]
      obtain ⟨ordinal, parsed, result⟩ := ih
        ⟨cumulative.val + gap, by have h := cumulative.isLt; omega⟩
        ⟨rank.val + 1, by omega⟩ tail_positive
        (by simp only [List.sum_cons] at total_bound; dsimp; omega)
        (by simp only [List.length_cons] at rank_bound; dsimp; omega)
      refine ⟨ordinal, parsed, ?_⟩
      simpa only [supportFromGaps, List.mem_cons, Ne.symm hit, false_or,
        List.idxOf_cons_ne _ hit, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1] using result

/-- Validate the complete candidate, then return its query ordinal in a second
pass. `none` means invalid; `some 0` means a valid support without the query. -/
def lookupOrdinal (bound capacity : ℕ) (query : Fin (bound + 1)) (input : List Bool) :
    Option (Fin (capacity + 1)) :=
  match lookup bound capacity query input with
  | none => none
  | some _ => seekOrdinal bound capacity query ⟨0, by omega⟩ ⟨0, by omega⟩ input

theorem lookupOrdinal_encodeSupport (bound capacity : ℕ) (query : Fin (bound + 1))
    (indices : List ℕ) (valid : ValidSupport bound capacity indices) :
    ∃ ordinal : Fin (capacity + 1),
      lookupOrdinal bound capacity query (encodeSupport indices) = some ordinal ∧
      ordinal.val = if query.val ∈ indices then indices.idxOf query.val + 1 else 0 := by
  unfold lookupOrdinal
  rw [lookup_encodeSupport bound capacity query indices valid.1 valid.2.1 valid.2.2.1 valid.2.2.2]
  obtain ⟨ordinal, parsed, answer⟩ := seekOrdinal_encode bound capacity query ⟨0, by omega⟩ ⟨0, by omega⟩
    (gapsFromSupport 0 indices) (gapsFromSupport_pos indices valid.1 0 valid.2.1)
    (gapsFromSupport_sum_le bound indices valid.1 0 (Nat.zero_le _) valid.2.1 valid.2.2.1)
    (by simpa only [Fin.val_mk, Nat.zero_add, gapsFromSupport_length] using valid.2.2.2)
  refine ⟨ordinal, parsed, ?_⟩
  simpa only [Fin.val_mk, Nat.zero_add,
    supportFromGaps_gapsFromSupport indices valid.1 0 valid.2.1] using answer

/-- Arbitrary accepted ordinal queries have a unique valid support, and the
reported positive ordinal is exactly its zero-based list index plus one. -/
theorem lookupOrdinal_sound_unique (bound capacity : ℕ) (query : Fin (bound + 1))
    (input : List Bool) (ordinal : Fin (capacity + 1))
    (accepted : lookupOrdinal bound capacity query input = some ordinal) :
    ∃! indices : List ℕ, ValidSupport bound capacity indices ∧ input = encodeSupport indices ∧
      ordinal.val = if query.val ∈ indices then indices.idxOf query.val + 1 else 0 := by
  have validated : ∃ found, lookup bound capacity query input = some found := by
    unfold lookupOrdinal at accepted
    cases h : lookup bound capacity query input with
    | none => simp only [h] at accepted; contradiction
    | some found => exact ⟨found, rfl⟩
  obtain ⟨found, validated⟩ := validated
  obtain ⟨indices, valid, encoded, _⟩ := lookup_sound bound capacity query input found validated
  obtain ⟨expected, parsed, answer⟩ := lookupOrdinal_encodeSupport bound capacity query indices valid
  have same : ordinal = expected := Option.some.inj (accepted.symm.trans (encoded ▸ parsed))
  refine ⟨indices, ⟨valid, encoded, same ▸ answer⟩, ?_⟩
  intro other other_valid
  exact encodeSupport_injective other_valid.1.1 valid.1 other_valid.1.2.1 valid.2.1
    (other_valid.2.1.symm.trans encoded)

/-- Convert the one-based ordinal to the bounded zero-based mask position. -/
def ordinalIndex {capacity : ℕ} (ordinal : Fin (capacity + 1)) : Option (Fin capacity) :=
  if positive : 0 < ordinal.val then
    some ⟨ordinal.val - 1, by have h := ordinal.isLt; omega⟩
  else none

end NtimeDspace.BoundedSupportParser
