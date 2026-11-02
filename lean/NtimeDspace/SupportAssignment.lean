import NtimeDspace.BoundedSupportParser

/-!
# Streaming support-mask assignment queries

Formula variables use `Fin N`, whereas the gamma support codec uses the positive
indices `1, …, N`. The query for variable `v` is therefore `v.val + 1`. A validated
streaming ordinal lookup selects the corresponding zero-based mask position;
variables outside the support receive `false`.

Only the input bit string and a mask-bit accessor are used by `lookupBit`.
Decoded support lists occur in specifications and proofs, never in its
execution. Tape-machine refinement and workspace bounds remain separate.
The parser capacity is only an upper bound: assignment-mask enumeration must
use the actual support length. `extendMask` embeds such an exact-width mask
into the parser's capacity without assigning bits to unused mask positions.
-/

namespace NtimeDspace.SupportAssignment

open SupportEncoding

variable {n capacity : ℕ}

def positiveIndex (v : Fin n) : ℕ := v.val + 1

def query (v : Fin n) : Fin (n + 1) :=
  ⟨positiveIndex v, by have := v.isLt; dsimp [positiveIndex]; omega⟩

theorem positiveIndex_injective : Function.Injective (positiveIndex (n := n)) := by
  intro first second same
  apply Fin.ext
  unfold positiveIndex at same
  omega

/-- Specification-side conversion to the positive support-code convention. -/
def positiveSupport (support : List (Fin n)) : List ℕ := support.map positiveIndex

def Valid (capacity : ℕ) (support : List (Fin n)) : Prop :=
  support.Pairwise (· < ·) ∧ support.length ≤ capacity

theorem positiveSupport_valid_iff (support : List (Fin n)) :
    BoundedSupportParser.ValidSupport n capacity (positiveSupport support) ↔ Valid capacity support := by
  have sorted : (positiveSupport support).Pairwise (· < ·) ↔ support.Pairwise (· < ·) := by
    simp only [positiveSupport, List.pairwise_map, positiveIndex, Nat.add_lt_add_iff_right, Fin.lt_def]
  constructor
  · rintro ⟨ordered, _, _, count⟩
    exact ⟨sorted.mp ordered, by simpa only [positiveSupport, List.length_map] using count⟩
  · rintro ⟨ordered, count⟩
    refine ⟨sorted.mpr ordered, ?_, ?_, ?_⟩
    · intro index member
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp member
      exact Nat.succ_pos _
    · intro index member
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp member
      exact Nat.succ_le_of_lt v.isLt
    · simpa only [positiveSupport, List.length_map] using count

theorem positiveSupport_mem (support : List (Fin n)) (v : Fin n) :
    positiveIndex v ∈ positiveSupport support ↔ v ∈ support := by
  simp only [positiveSupport, List.mem_map, positiveIndex_injective.eq_iff,
    exists_eq_right]

theorem positiveSupport_idxOf (support : List (Fin n)) (v : Fin n) :
    (positiveSupport support).idxOf (positiveIndex v) = support.idxOf v := by
  induction support with
  | nil => rfl
  | cons first support ih =>
    by_cases same : first = v
    · subst first
      simp [positiveSupport]
    · have distinct : positiveIndex first ≠ positiveIndex v :=
        fun equal => same (positiveIndex_injective equal)
      change (positiveIndex first :: positiveSupport support).idxOf (positiveIndex v) =
        (first :: support).idxOf v
      rw [List.idxOf_cons_ne _ distinct, List.idxOf_cons_ne _ same, ih]

def encode (support : List (Fin n)) : List Bool := encodeSupport (positiveSupport support)

theorem encode_injective {first second : List (Fin n)}
    (first_valid : Valid capacity first) (second_valid : Valid capacity second)
    (same : encode first = encode second) : first = second := by
  have first_code := (positiveSupport_valid_iff first).mpr first_valid
  have second_code := (positiveSupport_valid_iff second).mpr second_valid
  have equal := encodeSupport_injective first_code.1 second_code.1
    first_code.2.1 second_code.2.1 same
  exact positiveIndex_injective.list_map equal

/-- Mathematical assignment associated to a sorted support and its mask bits. -/
def assignmentBit (support : List (Fin n)) (count : support.length ≤ capacity)
    (mask : Fin capacity → Bool) (v : Fin n) : Bool :=
  if member : v ∈ support then
    mask ⟨support.idxOf v, (List.idxOf_lt_length_of_mem member).trans_le count⟩
  else false

/-- A successful ordinal zero denotes an absent variable. A positive ordinal
selects the preceding zero-based mask position. -/
def bitAtOrdinal (mask : Fin capacity → Bool) (ordinal : Fin (capacity + 1)) : Bool :=
  match BoundedSupportParser.ordinalIndex ordinal with
  | none => false
  | some index => mask index

/-- Executing assignment lookup: validate and scan the code, then read one
mask bit. No support list is decoded or retained. -/
def lookupBit (mask : Fin capacity → Bool) (v : Fin n) (input : List Bool) : Option Bool :=
  (BoundedSupportParser.lookupOrdinal n capacity (query v) input).map (bitAtOrdinal mask)

theorem bitAtOrdinal_correct (support : List (Fin n)) (count : support.length ≤ capacity)
    (mask : Fin capacity → Bool) (v : Fin n) (ordinal : Fin (capacity + 1))
    (position : ordinal.val = if v ∈ support then support.idxOf v + 1 else 0) :
    bitAtOrdinal mask ordinal = assignmentBit support count mask v := by
  by_cases member : v ∈ support
  · rw [ite_eq_left member] at position
    have positive : 0 < ordinal.val := by omega
    simp only [bitAtOrdinal, BoundedSupportParser.ordinalIndex, dite_eq_left positive,
      assignmentBit, dite_eq_left member]
    apply congrArg mask
    apply Fin.ext
    dsimp
    omega
  · rw [ite_eq_right member] at position
    have zero : ¬0 < ordinal.val := by omega
    simp only [bitAtOrdinal, BoundedSupportParser.ordinalIndex, dite_eq_right zero,
      assignmentBit, dite_eq_right member]

/-- Correctness of the positive-index and zero-based-mask convention together. -/
theorem lookupBit_encode (support : List (Fin n)) (valid : Valid capacity support)
    (mask : Fin capacity → Bool) (v : Fin n) :
    lookupBit mask v (encode support) = some (assignmentBit support valid.2 mask v) := by
  obtain ⟨ordinal, parsed, position⟩ := BoundedSupportParser.lookupOrdinal_encodeSupport n capacity
    (query v) (positiveSupport support) ((positiveSupport_valid_iff support).mpr valid)
  have position' : ordinal.val = if v ∈ support then support.idxOf v + 1 else 0 := by
    simpa only [query, Fin.val_mk, positiveSupport_mem, positiveSupport_idxOf] using position
  unfold lookupBit encode
  rw [parsed, Option.map_some, bitAtOrdinal_correct support valid.2 mask v ordinal position']

/-- Every valid positive support is the shifted code of a unique list of
formula variables. This existential conversion is used only in proofs. -/
theorem exists_variableSupport (indices : List ℕ)
    (valid : BoundedSupportParser.ValidSupport n capacity indices) :
    ∃ support : List (Fin n), Valid capacity support ∧ positiveSupport support = indices := by
  induction indices with
  | nil => exact ⟨[], by simp [Valid], rfl⟩
  | cons index indices ih =>
    have ordered := List.pairwise_cons.mp valid.1
    have positive : 0 < index := valid.2.1 index (by simp)
    have bounded : index ≤ n := valid.2.2.1 index (by simp)
    have tail_valid : BoundedSupportParser.ValidSupport n capacity indices :=
      ⟨ordered.2, fun i hi => valid.2.1 i (by simp [hi]),
        fun i hi => valid.2.2.1 i (by simp [hi]), by
          have h := valid.2.2.2
          simp only [List.length_cons] at h
          omega⟩
    obtain ⟨tail, _, encoded⟩ := ih tail_valid
    let first : Fin n := ⟨index - 1, by omega⟩
    have first_code : positiveIndex first = index := by dsimp [positiveIndex, first]; omega
    have same : positiveSupport (first :: tail) = index :: indices := by
      change positiveIndex first :: positiveSupport tail = _
      rw [first_code, encoded]
    exact ⟨first :: tail, (positiveSupport_valid_iff _).mp (same ▸ valid), same⟩

/-- A bit returned for an arbitrary candidate comes from exactly one valid
support; the bit value alone is never used to infer which support was encoded. -/
theorem lookupBit_sound_unique (mask : Fin capacity → Bool) (v : Fin n)
    (input : List Bool) (answer : Bool) (accepted : lookupBit mask v input = some answer) :
    ∃! support : List (Fin n), ∃ valid : Valid capacity support,
      input = encode support ∧ answer = assignmentBit support valid.2 mask v := by
  unfold lookupBit at accepted
  cases parsed : BoundedSupportParser.lookupOrdinal n capacity (query v) input with
  | none => simp only [parsed, Option.map_none] at accepted; contradiction
  | some ordinal =>
    obtain ⟨indices, ⟨valid, encoded, _⟩, _⟩ :=
      BoundedSupportParser.lookupOrdinal_sound_unique n capacity (query v) input ordinal parsed
    obtain ⟨support, support_valid, support_code⟩ := exists_variableSupport indices valid
    have code : input = encode support := by rw [encode, support_code]; exact encoded
    have computed := lookupBit_encode support support_valid mask v
    have returned : answer = assignmentBit support support_valid.2 mask v := by
      apply Option.some.inj
      exact accepted.symm.trans (code ▸ computed)
    refine ⟨support, ⟨support_valid, code, returned⟩, ?_⟩
    rintro other ⟨other_valid, other_code, _⟩
    exact encode_injective other_valid support_valid (other_code.symm.trans code)

theorem lookupBit_some_iff (mask : Fin capacity → Bool) (v : Fin n)
    (input : List Bool) (answer : Bool) :
    lookupBit mask v input = some answer ↔
      ∃ support : List (Fin n), ∃ valid : Valid capacity support,
        input = encode support ∧ answer = assignmentBit support valid.2 mask v := by
  constructor
  · intro accepted
    obtain ⟨support, semantics, _⟩ := lookupBit_sound_unique mask v input answer accepted
    exact ⟨support, semantics⟩
  · rintro ⟨support, valid, rfl, rfl⟩
    exact lookupBit_encode support valid mask v

/-- Extend an exact-width mask accessor by false bits. The width is a scalar;
the executing accessor never receives or reconstructs a support list. -/
def extendMask {width : ℕ} (_fits : width ≤ capacity) (mask : Fin width → Bool) :
    Fin capacity → Bool :=
  fun index => if inside : index.val < width then mask ⟨index.val, inside⟩ else false

theorem assignmentBit_extendMask (support : List (Fin n)) (count : support.length ≤ capacity)
    (mask : Fin support.length → Bool) (v : Fin n) :
    assignmentBit support count (extendMask count mask) v =
      assignmentBit support (Nat.le_refl _) mask v := by
  by_cases member : v ∈ support
  · have inside := List.idxOf_lt_length_of_mem member
    simp only [assignmentBit, dite_eq_left member, extendMask, dite_eq_left inside]
  · simp only [assignmentBit, dite_eq_right member]

/-- Exact support-size masks give the intended assignment even when the parser
allows larger supports. This does not identify capacity with mask width. -/
theorem lookupBit_exactMask (support : List (Fin n)) (valid : Valid capacity support)
    (mask : Fin support.length → Bool) (v : Fin n) :
    lookupBit (extendMask valid.2 mask) v (encode support) =
      some (assignmentBit support (Nat.le_refl _) mask v) := by
  rw [lookupBit_encode support valid, assignmentBit_extendMask]

end NtimeDspace.SupportAssignment
