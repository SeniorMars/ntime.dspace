import NtimeDspace.SupportOrdinalScan
import NtimeDspace.SupportSubsetLoop

/-!
The ordinal scan agrees with the existing validated ordinal lookup on every
payload. Formula vs use positive code indices `v.val + 1`; the returned
ordinal is zero for absence and otherwise the zero-based mask index plus one.
The scalar bit accessor below uses the actual accepted width. These are
semantic bridges, not a compilation or work-tape bound for bit access.
-/

namespace NtimeDspace.SupportOrdinalMeaning

open SupportAssignment

variable {bound capacity : ℕ}

private theorem lookupOrdinal_map_encode (query : Fin (bound + 1))
    (support : List (Fin bound)) (valid : Valid capacity support) :
    (BoundedSupportParser.lookupOrdinal bound capacity query (encode support)).map Fin.val =
      some (if query.val ∈ positiveSupport support then
        (positiveSupport support).idxOf query.val + 1 else 0) := by
  obtain ⟨ordinal, parsed, position⟩ :=
    BoundedSupportParser.lookupOrdinal_encodeSupport bound capacity query
      (positiveSupport support) ((positiveSupport_valid_iff support).mpr valid)
  change (BoundedSupportParser.lookupOrdinal bound capacity query
    (SupportEncoding.encodeSupport (positiveSupport support))).map Fin.val = _
  rw [parsed, Option.map_some, position]

/-- Equality includes rejection: a valid prefix never turns an invalid suffix
into an accepted ordinal. The two procedures may use different passes. -/
theorem read_ordinal_eq_lookupOrdinal (query : Fin (bound + 1)) (input : List Bool) :
    (SupportOrdinalScan.read bound capacity query.val input).map Prod.snd =
      (BoundedSupportParser.lookupOrdinal bound capacity query input).map Fin.val := by
  cases parsed : SupportOrdinalScan.read bound capacity query.val input with
  | none =>
    cases looked : BoundedSupportParser.lookupOrdinal bound capacity query input with
    | none => rfl
    | some ordinal =>
      obtain ⟨indices, ⟨valid, encoded, _⟩, _⟩ :=
        BoundedSupportParser.lookupOrdinal_sound_unique bound capacity query input ordinal looked
      obtain ⟨support, supportValid, same⟩ := exists_variableSupport indices valid
      have code : input = encode support := by
        rw [encode, same]
        exact encoded
      have accepted := SupportOrdinalScan.read_encode bound capacity query.val support supportValid
      rw [← code, parsed] at accepted
      contradiction
  | some pair =>
    rcases pair with ⟨width, ordinal⟩
    obtain ⟨support, valid, code, _, position⟩ :=
      (SupportOrdinalScan.read_some_iff bound capacity query.val input width ordinal).mp parsed
    rw [code, lookupOrdinal_map_encode query support valid, Option.map_some, position]

/-- A formula variable is queried at its positive support-code index. -/
theorem read_encode_variable (support : List (Fin bound)) (valid : Valid capacity support)
    (v : Fin bound) :
    SupportOrdinalScan.read bound capacity (positiveIndex v) (encode support) =
      some (support.length, if v ∈ support then support.idxOf v + 1 else 0) := by
  simpa only [positiveSupport_mem, positiveSupport_idxOf] using
    SupportOrdinalScan.read_encode bound capacity (positiveIndex v) support valid

theorem read_some_variable_iff (v : Fin bound) (input : List Bool) (width ordinal : ℕ) :
    SupportOrdinalScan.read bound capacity (positiveIndex v) input = some (width, ordinal) ↔
      ∃ support : List (Fin bound), ∃ _valid : Valid capacity support,
        input = encode support ∧ width = support.length ∧
          ordinal = if v ∈ support then support.idxOf v + 1 else 0 := by
  simpa only [positiveSupport_mem, positiveSupport_idxOf] using
    SupportOrdinalScan.read_some_iff bound capacity (positiveIndex v) input width ordinal

/-- A scalar ordinal lookup. The absence sentinel never requests a mask bit. -/
def bitAtOrdinal (bits : ℕ → Bool) (ordinal : ℕ) : Bool :=
  if 0 < ordinal then bits (ordinal - 1) else false

/-- Totalize an accessor for exactly `width` bits, without allocating a list. -/
def maskBits {width : ℕ} (mask : Fin width → Bool) (index : ℕ) : Bool :=
  if inside : index < width then mask ⟨index, inside⟩ else false

theorem bitAtOrdinal_eq_bounded (mask : Fin capacity → Bool) (ordinal : Fin (capacity + 1)) :
    bitAtOrdinal (maskBits mask) ordinal.val = SupportAssignment.bitAtOrdinal mask ordinal := by
  by_cases positive : 0 < ordinal.val
  · have inside : ordinal.val - 1 < capacity := by have := ordinal.isLt; omega
    simp only [bitAtOrdinal, positive, ↓reduceIte, maskBits, inside, ↓reduceDIte,
      SupportAssignment.bitAtOrdinal, BoundedSupportParser.ordinalIndex]
  · simp only [bitAtOrdinal, positive, ↓reduceIte, SupportAssignment.bitAtOrdinal,
      BoundedSupportParser.ordinalIndex, ↓reduceDIte]

/-- Exactly-width mask interpretation of the one-based ordinal. No extra
positions are supplied when the parser capacity exceeds the support length. -/
theorem bitAtOrdinal_exactMask (support : List (Fin bound)) (mask : Fin support.length → Bool)
    (v : Fin bound) (ordinal : ℕ)
    (position : ordinal = if v ∈ support then support.idxOf v + 1 else 0) :
    bitAtOrdinal (maskBits mask) ordinal =
      decide (v ∈ SparseCorrection.maskSubset support (Nat.le_refl _) mask) := by
  rw [← SparseCorrection.maskSubset_membership support (Nat.le_refl _) mask v]
  by_cases member : v ∈ support
  · have inside := List.idxOf_lt_length_of_mem member
    rw [position, ite_eq_left member]
    simp only [bitAtOrdinal, Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel,
      maskBits, inside, ↓reduceDIte, assignmentBit, member]
  · rw [position, ite_eq_right member]
    simp [bitAtOrdinal, assignmentBit, member]

theorem read_bit_exactMask (support : List (Fin bound)) (valid : Valid capacity support)
    (mask : Fin support.length → Bool) (v : Fin bound) :
    (SupportOrdinalScan.read bound capacity (positiveIndex v) (encode support)).map
      (fun result => bitAtOrdinal (maskBits mask) result.2) =
      some (decide (v ∈ SparseCorrection.maskSubset support (Nat.le_refl _) mask)) := by
  rw [read_encode_variable support valid v, Option.map_some]
  exact congrArg some (bitAtOrdinal_exactMask support mask v _ rfl)

/-- Arbitrary accepted candidates provide their exact mask width. The equality
of widths transports only bounded indices; no decoded support is executed. -/
theorem accepted_bit_exactMask (v : Fin bound) (input : List Bool) (width ordinal : ℕ)
    (accepted : SupportOrdinalScan.read bound capacity (positiveIndex v) input =
      some (width, ordinal)) (mask : Fin width → Bool) :
    ∃ support : List (Fin bound), ∃ _valid : Valid capacity support,
      ∃ widthEq : width = support.length, input = encode support ∧
        bitAtOrdinal (maskBits mask) ordinal =
          decide (v ∈ SparseCorrection.maskSubset support (Nat.le_refl _)
            (fun index => mask (Fin.cast widthEq.symm index))) := by
  obtain ⟨support, valid, code, rfl, position⟩ :=
    (read_some_variable_iff v input width ordinal).mp accepted
  exact ⟨support, valid, rfl, code, bitAtOrdinal_exactMask support mask v ordinal position⟩

end NtimeDspace.SupportOrdinalMeaning
