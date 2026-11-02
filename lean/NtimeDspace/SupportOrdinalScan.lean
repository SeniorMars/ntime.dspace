import NtimeDspace.SupportCardinality

/-!
A proof-side full support scan recording cardinality and one-based query
ordinal. Zero denotes absence. The scan continues validating after a hit.
This list-suffix specification will be refined by a scalar cursor machine;
it is not itself a machine-workspace theorem.
-/

namespace NtimeDspace.SupportOrdinalScan

open SupportEncoding BoundedSupportParser

def scan (bound capacity target : ℕ) (state : Registers bound capacity)
    (ordinal : ℕ) (input : List Bool) : Option (ℕ × ℕ) :=
  if finished : input = [] then some (state.rank.val, ordinal)
  else if room : state.rank.val < capacity then
    match gamma bound input with
    | none => none
    | some (gap, rest) =>
      if positive : 0 < gap.val then
        if fits : gap.val ≤ bound - state.cumulative.val then
          scan bound capacity target
            { cumulative := ⟨state.cumulative.val + gap.val, by
                have := state.cumulative.isLt
                omega⟩
              rank := ⟨state.rank.val + 1, by omega⟩
              found := false }
            (if state.cumulative.val + gap.val = target then state.rank.val + 1 else ordinal)
            rest
        else none
      else none
  else none
termination_by capacity - state.rank.val
decreasing_by omega

def read (bound capacity target : ℕ) (input : List Bool) : Option (ℕ × ℕ) :=
  scan bound capacity target (SupportCardinality.initial bound capacity) 0 input

theorem scan_count (bound capacity target : ℕ) (state : Registers bound capacity)
    (ordinal : ℕ) (flag : Bool) (query : Fin (bound + 1)) (input : List Bool) :
    (scan bound capacity target state ordinal input).map Prod.fst =
      (BoundedSupportParser.scan bound capacity query { state with found := flag } input).map
        (fun result => result.rank.val) := by
  conv_lhs => rw [scan]
  conv_rhs => rw [BoundedSupportParser.scan]
  dsimp only
  split_ifs with finished room
  · rfl
  · cases parsed : gamma bound input with
    | none => rfl
    | some pair =>
      rcases pair with ⟨gap, rest⟩
      simp only
      by_cases positive : 0 < gap.val
      · by_cases fits : gap.val ≤ bound - state.cumulative.val
        · simp only [dite_eq_left positive, dite_eq_left fits]
          exact scan_count bound capacity target
            { cumulative := ⟨state.cumulative.val + gap.val, by
                have := state.cumulative.isLt
                omega⟩
              rank := ⟨state.rank.val + 1, by omega⟩, found := false }
            (if state.cumulative.val + gap.val = target then state.rank.val + 1 else ordinal)
            (flag || decide (state.cumulative.val + gap.val = query.val)) query rest
        · simp [positive, fits]
      · simp [positive]
  · rfl
termination_by capacity - state.rank.val
decreasing_by omega

theorem read_count (bound capacity target : ℕ) (input : List Bool) :
    (read bound capacity target input).map Prod.fst =
      (SupportCardinality.count bound capacity input).map Fin.val := by
  simpa only [read, SupportCardinality.count, SupportCardinality.initial,
    Option.map_map, Function.comp_def] using
      scan_count bound capacity target (SupportCardinality.initial bound capacity)
        0 false ⟨0, by omega⟩ input

theorem scan_encode (bound capacity target : ℕ) (state : Registers bound capacity)
    (ordinal : ℕ) (gaps : List ℕ) (positive : ∀ gap ∈ gaps, 0 < gap)
    (totalBound : state.cumulative.val + gaps.sum ≤ bound)
    (rankBound : state.rank.val + gaps.length ≤ capacity) :
    scan bound capacity target state ordinal (encodeGaps gaps) =
      some (state.rank.val + gaps.length,
        if target ∈ supportFromGaps state.cumulative.val gaps then
          state.rank.val + (supportFromGaps state.cumulative.val gaps).idxOf target + 1
        else ordinal) := by
  induction gaps generalizing state ordinal with
  | nil => simp [encodeGaps, scan, supportFromGaps]
  | cons gap gaps ih =>
    have gapPositive : 0 < gap := positive gap (by simp)
    have tailPositive : ∀ g ∈ gaps, 0 < g := fun g hg => positive g (by simp [hg])
    have room : state.rank.val < capacity := by
      simp only [List.length_cons] at rankBound
      omega
    have gapBound : gap ≤ bound := by
      simp only [List.sum_cons] at totalBound
      omega
    have fits : gap ≤ bound - state.cumulative.val := by
      simp only [List.sum_cons] at totalBound
      omega
    have nonempty : gammaEncode gap ++ encodeGaps gaps ≠ [] := by
      intro empty
      exact gammaEncode_nonempty gap (List.append_eq_nil_iff.mp empty).1
    rw [encodeGaps, scan, dite_eq_right nonempty, dite_eq_left room,
      gamma_encode_append bound gap gapPositive gapBound]
    simp only [dite_eq_left gapPositive, dite_eq_left fits]
    rw [ih _ _ tailPositive
      (by simp only [List.sum_cons] at totalBound; dsimp; omega)
      (by simp only [List.length_cons] at rankBound; dsimp; omega)]
    by_cases hit : state.cumulative.val + gap = target
    · have absent : target ∉ supportFromGaps (state.cumulative.val + gap) gaps := by
        intro member
        have later := supportFromGaps_gt gaps tailPositive _ _ member
        omega
      have absent' : target ∉ supportFromGaps target gaps := by simpa only [hit] using absent
      simp [supportFromGaps, hit, absent']; omega
    · simp only [supportFromGaps, List.mem_cons, Ne.symm hit, false_or,
        List.idxOf_cons_ne _ hit, hit, ↓reduceIte, List.length_cons]
      congr 2 <;> (try split_ifs) <;> omega

theorem read_encode (bound capacity target : ℕ) (support : List (Fin bound))
    (valid : SupportAssignment.Valid capacity support) :
    read bound capacity target (SupportAssignment.encode support) =
      some (support.length,
        if target ∈ SupportAssignment.positiveSupport support then
          (SupportAssignment.positiveSupport support).idxOf target + 1 else 0) := by
  have positive := (SupportAssignment.positiveSupport_valid_iff support).mpr valid
  unfold read SupportAssignment.encode encodeSupport
  rw [scan_encode bound capacity target _ 0 _
    (gapsFromSupport_pos _ positive.1 0 positive.2.1)
    (by simpa only [SupportCardinality.initial, Fin.val_mk, Nat.zero_add] using
      gapsFromSupport_sum_le bound _ positive.1 0 (Nat.zero_le _) positive.2.1 positive.2.2.1)
    (by simpa only [SupportCardinality.initial, Fin.val_mk, Nat.zero_add,
      gapsFromSupport_length] using positive.2.2.2)]
  simp only [SupportCardinality.initial, Fin.val_mk, Nat.zero_add, gapsFromSupport_length]
  rw [supportFromGaps_gapsFromSupport _ positive.1 0 positive.2.1]
  simp only [SupportAssignment.positiveSupport, List.length_map]

theorem read_sound_unique (bound capacity target : ℕ) (input : List Bool)
    (width ordinal : ℕ) (accepted : read bound capacity target input = some (width, ordinal)) :
    ∃! support : List (Fin bound), ∃ _valid : SupportAssignment.Valid capacity support,
      input = SupportAssignment.encode support ∧ width = support.length ∧
        ordinal = if target ∈ SupportAssignment.positiveSupport support then
          (SupportAssignment.positiveSupport support).idxOf target + 1 else 0 := by
  have count := read_count bound capacity target input
  rw [accepted] at count
  cases parsed : SupportCardinality.count bound capacity input with
  | none => simp [parsed] at count
  | some result =>
    have widthEq : width = result.val := by simpa [parsed] using count
    obtain ⟨support, valid, encoded, length⟩ :=
      (SupportCardinality.count_some_iff input result).mp parsed
    have returned := read_encode bound capacity target support valid
    rw [← encoded, accepted] at returned
    have pair := Option.some.inj returned
    refine ⟨support, ⟨valid, encoded, widthEq.trans length, congrArg Prod.snd pair⟩, ?_⟩
    rintro other ⟨otherValid, otherEncoded, _, _⟩
    exact SupportAssignment.encode_injective otherValid valid (otherEncoded.symm.trans encoded)

theorem read_some_iff (bound capacity target : ℕ) (input : List Bool) (width ordinal : ℕ) :
    read bound capacity target input = some (width, ordinal) ↔
      ∃ support : List (Fin bound), ∃ _valid : SupportAssignment.Valid capacity support,
        input = SupportAssignment.encode support ∧ width = support.length ∧
          ordinal = if target ∈ SupportAssignment.positiveSupport support then
            (SupportAssignment.positiveSupport support).idxOf target + 1 else 0 := by
  constructor
  · intro accepted
    obtain ⟨support, semantics, _⟩ := read_sound_unique _ _ _ _ _ _ accepted
    exact ⟨support, semantics⟩
  · rintro ⟨support, valid, rfl, rfl, rfl⟩
    exact read_encode _ _ _ support valid

theorem read_output_bounds (bound capacity target : ℕ) (input : List Bool) (width ordinal : ℕ)
    (accepted : read bound capacity target input = some (width, ordinal)) :
    ordinal ≤ width ∧ width ≤ capacity := by
  obtain ⟨support, valid, _, length, position⟩ := (read_some_iff _ _ _ _ _ _).mp accepted
  refine ⟨?_, length ▸ valid.2⟩
  rw [position, length]
  split_ifs with member
  · have index := List.idxOf_lt_length_of_mem member
    simpa only [SupportAssignment.positiveSupport, List.length_map] using
      Nat.succ_le_of_lt index
  · exact Nat.zero_le _

end NtimeDspace.SupportOrdinalScan
