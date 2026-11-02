import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
An executable Elias gamma codec for the positive gaps in paper.tex, Section 4.
The code has exactly `2 * Nat.log2 n + 1` bits for positive `n`. The decoder
consumes only the next codeword and preserves arbitrary trailing bits.

These theorems concern representation and parsing, not a Turing-machine space
bound or the aggregate AM-GM bound for a bounded-size subset of `[N]`.
-/

namespace NtimeDspace.SupportEncoding

/-- The bits below the leading one, least-significant bit first. -/
def binaryTail (n : ℕ) : List Bool :=
  if h : 2 ≤ n then n.bodd :: binaryTail (n / 2) else []
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Interpret the low bits followed by a final leading one. -/
def binaryValue : List Bool → ℕ
  | [] => 1
  | b :: bs => Nat.bit b (binaryValue bs)

theorem binaryValue_binaryTail (n : ℕ) (hn : 0 < n) :
  binaryValue (binaryTail n) = n := by
  induction n using Nat.strong_induction_on
  rename_i n ih
  by_cases htwo : 2 ≤ n
  · rw [binaryTail, dif_pos htwo, binaryValue]
    rw [ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) (by omega)]
    rw [Nat.bit_val]
    simpa [Nat.div2_val, Nat.add_comm] using Nat.bodd_add_div2 n
  · have : n = 1 := by omega
    subst n
    simp [binaryTail, binaryValue]

theorem binaryTail_length (n : ℕ) : (binaryTail n).length = Nat.log2 n := by
  induction n using Nat.strong_induction_on
  rename_i n ih
  by_cases htwo : 2 ≤ n
  · have recursion : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
      simpa only [Nat.log2_eq_log_two] using
        (Nat.log_of_one_lt_of_le (b := 2) (n := n) (by decide) htwo)
    rw [binaryTail, dif_pos htwo, List.length_cons, recursion]
    rw [ih (n / 2) (Nat.div_lt_self (by omega) (by omega))]
  · rw [binaryTail, dif_neg htwo, List.length_nil, Nat.log2_eq_log_two,
      Nat.log_of_lt (by omega : n < 2)]

/-- Read exactly k bits; reject a truncated payload. -/
def takeBits : ℕ → List Bool → Option (List Bool × List Bool)
  | 0, input => some ([], input)
  | _ + 1, [] => none
  | k + 1, b :: input =>
    match takeBits k input with
    | none => none
    | some (payload, rest) => some (b :: payload, rest)

theorem takeBits_append (payload rest : List Bool) :
    takeBits payload.length (payload ++ rest) = some (payload, rest) := by
  induction payload with
  | nil => rfl
  | cons b bs ih => simp [takeBits, ih]

/-- Count initial zero bits; after the leading one read that many payload bits.
The recursive call consumes a bit, so this parser terminates on every input. -/
def scanZeros : ℕ → List Bool → Option (List Bool × List Bool)
  | _, [] => none
  | k, false :: input => scanZeros (k + 1) input
  | k, true :: input => takeBits k input

theorem scanZeros_replicate (m k : ℕ) (input : List Bool) :
    scanZeros k (List.replicate m false ++ true :: input) = takeBits (k + m) input := by
  induction m generalizing k with
  | zero => simp [scanZeros]
  | succ m ih =>
    simp only [List.replicate_succ, List.cons_append, scanZeros]
    rw [ih]
    congr 1
    omega

/-- Elias gamma encoding of n. The roundtrip theorems require `0 < n`. -/
def gammaEncode (n : ℕ) : List Bool :=
  List.replicate (binaryTail n).length false ++ true :: (binaryTail n).reverse

/-- Parse one positive integer and return the unconsumed input. -/
def gammaDecode (input : List Bool) : Option (ℕ × List Bool) :=
  (scanZeros 0 input).map fun (payload, rest) => (binaryValue payload.reverse, rest)

theorem gammaDecode_encode_append (n : ℕ) (hn : 0 < n) (rest : List Bool) :
    gammaDecode (gammaEncode n ++ rest) = some (n, rest) := by
  unfold gammaEncode gammaDecode
  rw [List.append_assoc, List.cons_append, scanZeros_replicate]
  simp only [Nat.zero_add]
  have ht := takeBits_append (binaryTail n).reverse rest
  simp only [List.length_reverse] at ht
  rw [ht]
  simp [binaryValue_binaryTail n hn]

theorem gammaDecode_encode (n : ℕ) (hn : 0 < n) :
    gammaDecode (gammaEncode n) = some (n, []) := by
  simpa using gammaDecode_encode_append n hn []

theorem gammaEncode_length (n : ℕ) :
    (gammaEncode n).length = 2 * Nat.log2 n + 1 := by
  simp [gammaEncode, binaryTail_length]
  omega

theorem gammaEncode_injective_positive {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (h : gammaEncode m = gammaEncode n) : m = n := by
  have hd := congrArg gammaDecode h
  rw [gammaDecode_encode m hm, gammaDecode_encode n hn] at hd
  exact congrArg Prod.fst (Option.some.inj hd)

/-- A full word plus any continuation determines both its integer and suffix. -/
theorem gammaEncode_unique_prefix {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {left right : List Bool} (h : gammaEncode m ++ left = gammaEncode n ++ right) :
    m = n ∧ left = right := by
  have hd := congrArg gammaDecode h
  rw [gammaDecode_encode_append m hm, gammaDecode_encode_append n hn] at hd
  exact Prod.mk.inj (Option.some.inj hd)

/-- Concatenate the codewords for the successive positive gaps of a support. -/
def encodeGaps : List ℕ → List Bool
  | [] => []
  | gap :: gaps => gammaEncode gap ++ encodeGaps gaps

/-- Parse to end of input, with an explicit upper bound on the codeword count.
The public decoder uses the input bit length as fuel. No partial recursion is used. -/
def decodeGapsFuel : ℕ → List Bool → Option (List ℕ)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b :: bits =>
    match gammaDecode (b :: bits) with
    | none => none
    | some (gap, rest) => (decodeGapsFuel fuel rest).map (gap :: ·)

def decodeGaps (input : List Bool) : Option (List ℕ) :=
  decodeGapsFuel input.length input

theorem gammaEncode_nonempty (n : ℕ) : gammaEncode n ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [gammaEncode_length] at this
  simp only [List.length_nil] at this
  omega

theorem decodeGapsFuel_encode (gaps : List ℕ)
    (hpos : ∀ gap ∈ gaps, 0 < gap) (fuel : ℕ) (hfuel : gaps.length ≤ fuel) :
    decodeGapsFuel fuel (encodeGaps gaps) = some gaps := by
  induction gaps generalizing fuel with
  | nil => simp [encodeGaps, decodeGapsFuel]
  | cons gap gaps ih =>
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := by
      cases fuel with
      | zero => simp at hfuel
      | succ fuel => exact ⟨fuel, rfl⟩
    have hg : 0 < gap := hpos gap (by simp)
    have hgs : ∀ g ∈ gaps, 0 < g := by
      intro g h
      exact hpos g (by simp [h])
    have hdecode := gammaDecode_encode_append gap hg (encodeGaps gaps)
    have hnonempty : gammaEncode gap ++ encodeGaps gaps ≠ [] := by
      simp [List.append_eq_nil_iff, gammaEncode_nonempty]
    unfold encodeGaps
    generalize hbits : gammaEncode gap ++ encodeGaps gaps = bits at *
    cases bits with
    | nil => exact False.elim (hnonempty rfl)
    | cons b bs =>
      simp only [decodeGapsFuel, hdecode]
      rw [ih hgs fuel (by simpa using hfuel)]
      rfl

theorem encodeGaps_length_ge (gaps : List ℕ) : gaps.length ≤ (encodeGaps gaps).length := by
  induction gaps with
  | nil => simp [encodeGaps]
  | cons gap gaps ih =>
    simp only [encodeGaps, List.length_cons, List.length_append, gammaEncode_length]
    omega

theorem decodeGaps_encode (gaps : List ℕ) (hpos : ∀ gap ∈ gaps, 0 < gap) :
    decodeGaps (encodeGaps gaps) = some gaps :=
  decodeGapsFuel_encode gaps hpos _ (encodeGaps_length_ge gaps)

theorem encodeGaps_injective_positive {left right : List ℕ}
    (hleft : ∀ gap ∈ left, 0 < gap) (hright : ∀ gap ∈ right, 0 < gap)
    (h : encodeGaps left = encodeGaps right) : left = right := by
  have hd := congrArg decodeGaps h
  rw [decodeGaps_encode left hleft, decodeGaps_encode right hright] at hd
  exact Option.some.inj hd

theorem encodeGaps_length (gaps : List ℕ) :
    (encodeGaps gaps).length = (gaps.map fun n => 2 * Nat.log2 n + 1).sum := by
  induction gaps with
  | nil => simp [encodeGaps]
  | cons gap gaps ih => simp [encodeGaps, gammaEncode_length, ih]

/-- Cumulative sums turn positive gaps into a strictly increasing support. -/
def supportFromGaps (start : ℕ) : List ℕ → List ℕ
  | [] => []
  | gap :: gaps => (start + gap) :: supportFromGaps (start + gap) gaps

/-- Differences of consecutive support indices, beginning with `first-start`. -/
def gapsFromSupport (start : ℕ) : List ℕ → List ℕ
  | [] => []
  | index :: indices => (index - start) :: gapsFromSupport index indices

theorem supportFromGaps_gt (gaps : List ℕ) (hpos : ∀ gap ∈ gaps, 0 < gap)
    (start index : ℕ) (hmem : index ∈ supportFromGaps start gaps) : start < index := by
  induction gaps generalizing start with
  | nil => simp [supportFromGaps] at hmem
  | cons gap gaps ih =>
    have hg : 0 < gap := hpos gap (by simp)
    have hgs : ∀ g ∈ gaps, 0 < g := by
      intro g h
      exact hpos g (by simp [h])
    simp only [supportFromGaps, List.mem_cons] at hmem
    rcases hmem with h | h
    · omega
    · have := ih hgs (start + gap) h
      omega

theorem supportFromGaps_strict (gaps : List ℕ) (hpos : ∀ gap ∈ gaps, 0 < gap)
    (start : ℕ) : (supportFromGaps start gaps).Pairwise (· < ·) := by
  induction gaps generalizing start with
  | nil => simp [supportFromGaps]
  | cons gap gaps ih =>
    have hgs : ∀ g ∈ gaps, 0 < g := by
      intro g h
      exact hpos g (by simp [h])
    simp only [supportFromGaps, List.pairwise_cons]
    exact ⟨fun index hmem => supportFromGaps_gt gaps hgs (start + gap) index hmem,
      ih hgs (start + gap)⟩

theorem gapsFromSupport_supportFromGaps (gaps : List ℕ) (start : ℕ) :
    gapsFromSupport start (supportFromGaps start gaps) = gaps := by
  induction gaps generalizing start with
  | nil => rfl
  | cons gap gaps ih => simp [supportFromGaps, gapsFromSupport, ih]

theorem gapsFromSupport_pos (indices : List ℕ)
    (hsorted : indices.Pairwise (· < ·)) (start : ℕ)
    (habove : ∀ index ∈ indices, start < index) :
    ∀ gap ∈ gapsFromSupport start indices, 0 < gap := by
  induction indices generalizing start with
  | nil => simp [gapsFromSupport]
  | cons index indices ih =>
    have hs := List.pairwise_cons.mp hsorted
    intro gap hmem
    simp only [gapsFromSupport, List.mem_cons] at hmem
    rcases hmem with h | h
    · have := habove index (by simp)
      omega
    · exact ih hs.2 index hs.1 gap h

theorem supportFromGaps_gapsFromSupport (indices : List ℕ)
    (hsorted : indices.Pairwise (· < ·)) (start : ℕ)
    (habove : ∀ index ∈ indices, start < index) :
    supportFromGaps start (gapsFromSupport start indices) = indices := by
  induction indices generalizing start with
  | nil => rfl
  | cons index indices ih =>
    have hs := List.pairwise_cons.mp hsorted
    have hindex := habove index (by simp)
    have hadd : start + (index - start) = index := by omega
    simp only [gapsFromSupport, supportFromGaps, hadd]
    rw [ih hs.2 index hs.1]

/-- The manuscript's gap encoding for a sorted support in the positive integers. -/
def encodeSupport (indices : List ℕ) : List Bool :=
  encodeGaps (gapsFromSupport 0 indices)

def decodeSupport (input : List Bool) : Option (List ℕ) :=
  (decodeGaps input).map (supportFromGaps 0)

theorem decodeSupport_encode (indices : List ℕ)
    (hsorted : indices.Pairwise (· < ·))
    (hpos : ∀ index ∈ indices, 0 < index) :
    decodeSupport (encodeSupport indices) = some indices := by
  unfold encodeSupport decodeSupport
  rw [decodeGaps_encode _ (gapsFromSupport_pos indices hsorted 0 hpos)]
  simp only [Option.map_some]
  rw [supportFromGaps_gapsFromSupport indices hsorted 0 hpos]

theorem encodeSupport_injective {left right : List ℕ}
    (hleft : left.Pairwise (· < ·)) (hright : right.Pairwise (· < ·))
    (hleftpos : ∀ index ∈ left, 0 < index) (hrightpos : ∀ index ∈ right, 0 < index)
    (h : encodeSupport left = encodeSupport right) : left = right := by
  have hd := congrArg decodeSupport h
  rw [decodeSupport_encode left hleft hleftpos,
    decodeSupport_encode right hright hrightpos] at hd
  exact Option.some.inj hd

end NtimeDspace.SupportEncoding
