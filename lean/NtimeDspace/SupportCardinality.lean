import NtimeDspace.SupportEnumeration

/-!
# Runtime cardinality of a compressed support

The bounded parser already retains the number of complete support entries.
`count` exposes that final register after full-input validation. It returns the
actual mask width, bounded by parser capacity, without decoding a support list.
The canonical support witnesses below occur only in correctness statements.

This is a bounded-register arithmetic interface, not yet a work-tape-space
refinement of the parser or its input representation.
-/

namespace NtimeDspace.SupportCardinality

open SupportEncoding BoundedSupportParser

variable {n capacity : ℕ}

/-- A full support scan beginning before the first positive index. -/
def initial (n capacity : ℕ) : Registers n capacity :=
  { cumulative := ⟨0, by omega⟩, rank := ⟨0, by omega⟩, found := false }

/-- Executing exact-width query. No support, gap, or payload list is decoded. -/
def count (n capacity : ℕ) (input : List Bool) : Option (Fin (capacity + 1)) :=
  (scan n capacity ⟨0, by omega⟩ (initial n capacity) input).map Registers.rank

theorem count_encode (support : List (Fin n))
    (valid : SupportAssignment.Valid capacity support) :
    count n capacity (SupportAssignment.encode support) =
      some ⟨support.length, Nat.lt_succ_of_le valid.2⟩ := by
  have positive := (SupportAssignment.positiveSupport_valid_iff support).mpr valid
  unfold count SupportAssignment.encode encodeSupport
  rw [scan_encode n capacity ⟨0, by omega⟩ _
    (gapsFromSupport_pos _ positive.1 0 positive.2.1) (initial n capacity)
    (by simpa only [initial] using (gapsFromSupport_sum_le n _ positive.1 0
      (Nat.zero_le _) positive.2.1 positive.2.2.1))
    (by simpa only [initial, Nat.zero_add, gapsFromSupport_length] using positive.2.2.2)]
  apply congrArg some
  apply Fin.ext
  simp only [initial, Nat.zero_add, gapsFromSupport_length,
    SupportAssignment.positiveSupport, List.length_map]

/-- Cardinality and membership validation inspect exactly the same complete
scan, differing only in the final bounded register they project. -/
theorem count_eq_none_iff_validate (input : List Bool) :
    count n capacity input = none ↔ SupportEnumeration.validate n capacity input = none := by
  unfold count initial SupportEnumeration.validate lookup
  cases scan n capacity ⟨0, by omega⟩
    { cumulative := ⟨0, by omega⟩, rank := ⟨0, by omega⟩, found := false } input <;> simp

theorem count_isSome_eq_validate (input : List Bool) :
    (count n capacity input).isSome = (SupportEnumeration.validate n capacity input).isSome := by
  unfold count initial SupportEnumeration.validate lookup
  cases scan n capacity ⟨0, by omega⟩
    { cumulative := ⟨0, by omega⟩, rank := ⟨0, by omega⟩, found := false } input <;> rfl

/-- An arbitrary accepted input has a unique valid variable support, and the
returned width is its actual length rather than the parser's capacity. -/
theorem count_sound_unique (input : List Bool) (width : Fin (capacity + 1))
    (accepted : count n capacity input = some width) :
    ∃! support : List (Fin n), ∃ _valid : SupportAssignment.Valid capacity support,
      input = SupportAssignment.encode support ∧ width.val = support.length := by
  have parsed : SupportEnumeration.validate n capacity input ≠ none := by
    intro rejected
    have empty := (count_eq_none_iff_validate input).mpr rejected
    rw [accepted] at empty
    exact Option.some_ne_none width empty
  obtain ⟨support, valid, encoded⟩ :=
    (SupportEnumeration.validate_ne_none_iff input).mp parsed
  have expected := count_encode support valid
  have same : width = ⟨support.length, Nat.lt_succ_of_le valid.2⟩ :=
    Option.some.inj (accepted.symm.trans (encoded ▸ expected))
  refine ⟨support, ⟨valid, encoded, congrArg Fin.val same⟩, ?_⟩
  rintro other ⟨other_valid, other_code, _⟩
  exact SupportAssignment.encode_injective other_valid valid (other_code.symm.trans encoded)

theorem count_some_iff (input : List Bool) (width : Fin (capacity + 1)) :
    count n capacity input = some width ↔
      ∃ support : List (Fin n), ∃ _valid : SupportAssignment.Valid capacity support,
        input = SupportAssignment.encode support ∧ width.val = support.length := by
  constructor
  · intro accepted
    obtain ⟨support, semantics, _⟩ := count_sound_unique input width accepted
    exact ⟨support, semantics⟩
  · rintro ⟨support, valid, rfl, length⟩
    have same : width = ⟨support.length, Nat.lt_succ_of_le valid.2⟩ := Fin.ext length
    rw [same]
    exact count_encode support valid

/-- Every returned scalar width is bounded, including on arbitrary malformed
candidates; malformed codes can only return a width after full validation. -/
theorem count_output_bound (input : List Bool) (width : Fin (capacity + 1))
    (_accepted : count n capacity input = some width) : width.val ≤ capacity :=
  Nat.le_of_lt_succ width.isLt

theorem count_empty (n capacity : ℕ) : count n capacity [] = some ⟨0, by omega⟩ := by
  simp [count, scan, initial]

end NtimeDspace.SupportCardinality
