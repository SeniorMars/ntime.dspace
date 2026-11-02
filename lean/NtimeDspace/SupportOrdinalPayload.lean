import NtimeDspace.BoundedSupportPayload
import NtimeDspace.SupportOrdinalScan

/-!
# Cursor-only support cardinality and ordinal lookup

The complete support scanner is observed at each committed positive gap. A
matching query records its one-based position, with zero denoting absence.
Scanning continues after a match, so an invalid suffix still rejects the input.
The executing state retains scalar registers only; decoded supports occur in
specifications and proofs.
-/

namespace NtimeDspace.SupportOrdinalPayload

@[ext]
structure State where
  core : BoundedSupportPayload.State
  ordinal : ℕ
  deriving DecidableEq

def initial (bound : ℕ) : State := ⟨BoundedSupportPayload.initial bound, 0⟩

def next (bound capacity target : ℕ) (argument : State × Option Bool) : State :=
  let advanced := BoundedSupportPayload.next bound capacity (argument.1.core, argument.2)
  ⟨advanced, if argument.1.core.rank < advanced.rank ∧ advanced.cumulative = target
    then advanced.rank else argument.1.ordinal⟩

def query (state : State) : ℕ := BoundedSupportPayload.query state.core

def halted (state : State) : Bool := BoundedSupportPayload.halted state.core

def output (state : State) : Option (ℕ × ℕ) :=
  (BoundedSupportPayload.output state.core).map (fun width => (width, state.ordinal))

def step (bound capacity target : ℕ) (input : List Bool) (state : State) : State :=
  if halted state then state else next bound capacity target (state, input[query state]?)

def run (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ) : State :=
  (step bound capacity target input)^[fuel] (initial bound)

def read (bound capacity target : ℕ) (input : List Bool) : Option (ℕ × ℕ) :=
  output (run bound capacity target input (input.length + 1))

@[simp] theorem initial_core (bound : ℕ) :
    (initial bound).core = BoundedSupportPayload.initial bound := rfl

@[simp] theorem next_core (bound capacity target : ℕ) (state : State) (bit : Option Bool) :
    (next bound capacity target (state, bit)).core =
      BoundedSupportPayload.next bound capacity (state.core, bit) := rfl

@[simp] theorem run_zero (bound capacity target : ℕ) (input : List Bool) :
    run bound capacity target input 0 = initial bound := rfl

theorem run_succ (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ) :
    run bound capacity target input (fuel + 1) =
      step bound capacity target input (run bound capacity target input fuel) :=
  Function.iterate_succ_apply' _ _ _

theorem step_core (bound capacity target : ℕ) (input : List Bool) (state : State) :
    (step bound capacity target input state).core =
      BoundedSupportPayload.step bound capacity input state.core := by
  by_cases done : BoundedSupportPayload.halted state.core = true
  · simp [step, halted, BoundedSupportPayload.step, done]
  · simp [step, halted, query, BoundedSupportPayload.step, done]

theorem run_core (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ) :
    (run bound capacity target input fuel).core = BoundedSupportPayload.run bound capacity input fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [run_succ, step_core, ih, BoundedSupportPayload.run_succ]

private theorem commit_rank_mono (bound capacity : ℕ) (state : BoundedSupportPayload.State)
    (parsed : BoundedGammaPayload.State) :
    state.rank ≤ (BoundedSupportPayload.commit bound capacity state parsed).rank := by
  unfold BoundedSupportPayload.commit
  split_ifs <;> simp

private theorem next_rank_mono (bound capacity : ℕ) (state : BoundedSupportPayload.State)
    (bit : Option Bool) : state.rank ≤ (BoundedSupportPayload.next bound capacity (state, bit)).rank := by
  by_cases boundary : state.phase = 0
  · cases bit with
    | none => simp [BoundedSupportPayload.next, boundary]
    | some bit =>
      by_cases room : state.rank < capacity
      · simpa only [BoundedSupportPayload.next, boundary, room, ↓reduceIte] using
          commit_rank_mono bound capacity state _
      · simp [BoundedSupportPayload.next, boundary, room]
  · by_cases inside : state.phase = 1
    · simpa only [BoundedSupportPayload.next, boundary, inside, Fin.reduceEq, ↓reduceIte] using
        commit_rank_mono bound capacity state _
    · simp [BoundedSupportPayload.next, boundary, inside]

theorem next_ordinal_le_rank (bound capacity target : ℕ) (state : State) (bit : Option Bool)
    (prior : state.ordinal ≤ state.core.rank) :
    (next bound capacity target (state, bit)).ordinal ≤ (next bound capacity target (state, bit)).core.rank := by
  have monotone := next_rank_mono bound capacity state.core bit
  unfold next
  dsimp
  split_ifs
  · exact Nat.le_refl _
  · exact prior.trans monotone

theorem run_ordinal_le_rank (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ) :
    (run bound capacity target input fuel).ordinal ≤ (run bound capacity target input fuel).core.rank := by
  induction fuel with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
    rw [run_succ]
    unfold step
    split_ifs
    · exact ih
    · exact next_ordinal_le_rank _ _ _ _ _ ih

theorem run_ordinal_le_capacity (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ) :
    (run bound capacity target input fuel).ordinal ≤ capacity := by
  have upper := (BoundedSupportPayload.run_wellFormed bound capacity input fuel).rank_le
  have rank := run_ordinal_le_rank bound capacity target input fuel
  rw [run_core] at rank
  exact rank.trans upper

theorem run_cursor_bound (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ) :
    (run bound capacity target input fuel).core.parser.cursor ≤ input.length := by
  rw [run_core]
  exact BoundedSupportPayload.run_cursor_bound _ _ _ _

theorem halts_by_length (bound capacity target : ℕ) (input : List Bool) :
    halted (run bound capacity target input (input.length + 1)) = true := by
  unfold halted
  rw [run_core]
  exact BoundedSupportPayload.halts_by_length _ _ _

/-- The observer does not change validation or cardinality. A matching prefix
followed by an invalid suffix still yields `none`. -/
theorem read_width (bound capacity target : ℕ) (input : List Bool) :
    (read bound capacity target input).map Prod.fst =
      (SupportCardinality.count bound capacity input).map Fin.val := by
  unfold read output
  rw [Option.map_map]
  simp only [Function.comp_def, run_core]
  simpa using BoundedSupportPayload.halted_output bound capacity input (input.length + 1)
    (BoundedSupportPayload.halts_by_length _ _ _)

theorem read_output_bounds (bound capacity target : ℕ) (input : List Bool)
    (width ordinal : ℕ) (success : read bound capacity target input = some (width, ordinal)) :
    ordinal ≤ width ∧ width ≤ capacity := by
  have ordinalBound := run_ordinal_le_rank bound capacity target input (input.length + 1)
  have widthBound := (BoundedSupportPayload.run_wellFormed bound capacity input
    (input.length + 1)).rank_le
  rw [← run_core bound capacity target input (input.length + 1)] at widthBound
  simp only [read, output, BoundedSupportPayload.output] at success
  split_ifs at success
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
    omega
  · simp at success

theorem run_register_bounds (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ) :
    let state := run bound capacity target input fuel
    state.core.cumulative ≤ bound ∧ state.core.rank ≤ capacity ∧
      state.ordinal ≤ state.core.rank ∧ state.core.parser.cursor ≤ input.length ∧
      state.core.parser.zeros ≤ bound.log2 ∧ state.core.parser.remaining ≤ bound.log2 ∧
      state.core.parser.accumulator ≤ bound ∧ state.core.parser.room ≤ bound := by
  have bounds := BoundedSupportPayload.run_register_bounds bound capacity input fuel
  rw [← run_core bound capacity target input fuel] at bounds
  exact ⟨bounds.1, bounds.2.1, run_ordinal_le_rank _ _ _ _ _, bounds.2.2⟩

private def attached (target : ℕ) (state : State) (advanced : BoundedSupportPayload.State) : State :=
  ⟨advanced, if state.core.rank < advanced.rank ∧ advanced.cumulative = target then
    advanced.rank else state.ordinal⟩

private def afterGap (bound capacity target cumulative rank ordinal : ℕ)
    (pair : Fin (bound + 1) × List Bool) : Option (ℕ × ℕ) :=
  if positive : 0 < pair.1.val then
    if fits : pair.1.val ≤ bound - cumulative then
      if room : rank < capacity then
        SupportOrdinalScan.scan bound capacity target
          { cumulative := ⟨cumulative + pair.1.val, by omega⟩,
            rank := ⟨rank + 1, by omega⟩, found := false }
          (if cumulative + pair.1.val = target then rank + 1 else ordinal) pair.2
      else none
    else none
  else none

/-- The remaining list scan is proof-only; the executing state stores no suffix. -/
private def residual (bound capacity target : ℕ) (state : State)
    (wf : BoundedSupportPayload.WellFormed bound capacity state.core)
    (input : List Bool) : Option (ℕ × ℕ) :=
  if state.core.phase = 0 then
    SupportOrdinalScan.scan bound capacity target
      { cumulative := ⟨state.core.cumulative, by have := wf.cumulative_le; omega⟩,
        rank := ⟨state.core.rank, by have := wf.rank_le; omega⟩, found := false }
      state.ordinal (input.drop state.core.parser.cursor)
  else if state.core.phase = 1 then
    (BoundedGammaPayload.residual bound state.core.parser wf.parser_wellFormed
      (input.drop state.core.parser.cursor)).bind
        (afterGap bound capacity target state.core.cumulative state.core.rank state.ordinal)
  else output state

private theorem commit_residual (bound capacity target : ℕ) (state : State)
    (parsed : BoundedGammaPayload.State)
    (wf : BoundedSupportPayload.WellFormed bound capacity state.core)
    (parserWF : BoundedGammaPayload.WellFormed bound parsed) (input : List Bool) :
    residual bound capacity target
      (attached target state (BoundedSupportPayload.commit bound capacity state.core parsed))
      (BoundedSupportPayload.commit_wellFormed _ _ _ _ wf parserWF) input =
      (BoundedGammaPayload.residual bound parsed parserWF (input.drop parsed.cursor)).bind
        (afterGap bound capacity target state.core.cumulative state.core.rank state.ordinal) := by
  by_cases accepted : parsed.phase = 2
  · simp only [BoundedSupportPayload.commit, accepted, ↓reduceIte]
    split_ifs with positive fits room <;>
      simp_all [residual, attached, BoundedGammaPayload.residual, afterGap, output,
        BoundedSupportPayload.output]
  · by_cases rejected : parsed.phase = 3
    · simp [BoundedSupportPayload.commit, rejected, residual, attached, output,
        BoundedSupportPayload.output, BoundedGammaPayload.residual]
    · have phaseSmall (phase : Fin 4) (noTwo : phase ≠ 2) (noThree : phase ≠ 3) :
          phase = 0 ∨ phase = 1 := by
        fin_cases phase <;> simp_all
      have small := phaseSmall parsed.phase accepted rejected
      rcases small with pref | payload
      · simp [BoundedSupportPayload.commit, residual, attached, BoundedGammaPayload.residual, pref]
      · simp [BoundedSupportPayload.commit, residual, attached, BoundedGammaPayload.residual, payload]

private theorem scan_nonempty (bound capacity target : ℕ)
    (state : BoundedSupportParser.Registers bound capacity) (ordinal : ℕ)
    (input : List Bool) (nonempty : input ≠ []) (room : state.rank.val < capacity) :
    SupportOrdinalScan.scan bound capacity target state ordinal input =
      (BoundedSupportParser.gamma bound input).bind
        (afterGap bound capacity target state.cumulative.val state.rank.val ordinal) := by
  rw [SupportOrdinalScan.scan, dite_eq_right nonempty, dite_eq_left room]
  cases parsed : BoundedSupportParser.gamma bound input with
  | none => rfl
  | some pair =>
    rcases pair with ⟨gap, rest⟩
    by_cases positive : 0 < gap.val
    · by_cases fits : gap.val ≤ bound - state.cumulative.val
      · simp [positive, fits, afterGap, room]
      · simp [positive, fits, afterGap]
    · simp [positive, afterGap]

private theorem drop_of_none (input : List Bool) (cursor : ℕ)
    (absent : input[cursor]? = none) : input.drop cursor = [] := by
  induction input generalizing cursor with
  | nil => simp
  | cons bit rest ih =>
    cases cursor with
    | zero => simp at absent
    | succ cursor => exact ih cursor (by simpa using absent)

private theorem drop_of_some (input : List Bool) (cursor : ℕ) (bit : Bool)
    (present : input[cursor]? = some bit) : input.drop cursor = bit :: input.drop (cursor + 1) := by
  induction input generalizing cursor with
  | nil => simp at present
  | cons first rest ih =>
    cases cursor with
    | zero => simpa using present
    | succ cursor => simpa using ih cursor (by simpa using present)

private theorem residual_next (bound capacity target : ℕ) (state : State)
    (wf : BoundedSupportPayload.WellFormed bound capacity state.core) (input : List Bool) :
    residual bound capacity target (next bound capacity target (state, input[query state]?))
      (BoundedSupportPayload.next_wellFormed _ _ _ _ wf) input =
      residual bound capacity target state wf input := by
  change residual bound capacity target
    (attached target state (BoundedSupportPayload.next bound capacity
      (state.core, input[state.core.parser.cursor]?))) _ input = _
  by_cases boundary : state.core.phase = 0
  · by_cases absent : input[state.core.parser.cursor]? = none
    · simp [BoundedSupportPayload.next, absent, boundary, residual, attached, output,
        BoundedSupportPayload.output, drop_of_none input state.core.parser.cursor absent,
        SupportOrdinalScan.scan]
    · obtain ⟨bitValue, bit⟩ : ∃ bitValue, input[state.core.parser.cursor]? = some bitValue := by
        cases result : input[state.core.parser.cursor]? with
        | none => exact False.elim (absent result)
        | some bitValue => exact ⟨bitValue, rfl⟩
      have nonempty : input.drop state.core.parser.cursor ≠ [] := by
        rw [drop_of_some input state.core.parser.cursor bitValue bit]
        exact List.cons_ne_nil _ _
      by_cases room : state.core.rank < capacity
      · simp only [BoundedSupportPayload.next, boundary, bit, room, ↓reduceIte]
        rw [commit_residual bound capacity target state _ wf
          (BoundedGammaPayload.next_wellFormed _ _ _ (BoundedGammaPayload.initial_wellFormed _ _))]
        have gamma := BoundedGammaPayload.residual_next bound input
          (BoundedGammaPayload.initial bound state.core.parser.cursor)
          (BoundedGammaPayload.initial_wellFormed _ _)
          (by simp [BoundedGammaPayload.halted, BoundedGammaPayload.initial])
        simp only [BoundedGammaPayload.initial, bit] at gamma
        simp only [BoundedGammaPayload.initial]
        rw [gamma]
        change (BoundedSupportParser.gamma bound (input.drop state.core.parser.cursor)).bind
          (afterGap bound capacity target state.core.cumulative state.core.rank state.ordinal) = _
        simp only [residual, boundary, ↓reduceIte]
        exact (scan_nonempty bound capacity target
          { cumulative := ⟨state.core.cumulative, by have := wf.cumulative_le; omega⟩,
            rank := ⟨state.core.rank, by have := wf.rank_le; omega⟩, found := false }
          state.ordinal _ nonempty room).symm
      · simp [BoundedSupportPayload.next, bit, boundary, room, residual, attached, output,
          BoundedSupportPayload.output, SupportOrdinalScan.scan, nonempty]
  · by_cases inside : state.core.phase = 1
    · have running : BoundedGammaPayload.halted state.core.parser = false := by
        rcases wf.inside inside with pref | payload
        · simp [BoundedGammaPayload.halted, pref]
        · simp [BoundedGammaPayload.halted, payload]
      simp only [BoundedSupportPayload.next, inside, Fin.reduceEq, ↓reduceIte]
      rw [commit_residual bound capacity target state _ wf
        (BoundedGammaPayload.next_wellFormed _ _ _ wf.parser_wellFormed)]
      rw [BoundedGammaPayload.residual_next bound input state.core.parser wf.parser_wellFormed running]
      simp [residual, inside]
    · simp only [BoundedSupportPayload.next, boundary, inside, ↓reduceIte]
      simp [attached]

private theorem run_residual (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ) :
    residual bound capacity target (run bound capacity target input fuel)
      (run_core bound capacity target input fuel ▸ BoundedSupportPayload.run_wellFormed _ _ _ _) input =
      SupportOrdinalScan.read bound capacity target input := by
  induction fuel with
  | zero =>
    simp [residual, initial, BoundedSupportPayload.initial, BoundedGammaPayload.initial,
      SupportOrdinalScan.read, SupportCardinality.initial]
  | succ fuel ih =>
    simp only [run_succ]
    unfold step
    split_ifs
    · exact ih
    · exact (residual_next _ _ _ _ _ input).trans ih

private theorem residual_halted (bound capacity target : ℕ) (state : State)
    (wf : BoundedSupportPayload.WellFormed bound capacity state.core) (input : List Bool)
    (done : halted state = true) : residual bound capacity target state wf input = output state := by
  have phases : state.core.phase ≠ 0 ∧ state.core.phase ≠ 1 := by
    simp only [halted, BoundedSupportPayload.halted, decide_eq_true_eq] at done
    constructor <;> intro same <;> rw [same] at done <;> norm_num at done
  simp [residual, phases.1, phases.2]

theorem halted_output (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ)
    (done : halted (run bound capacity target input fuel) = true) :
    output (run bound capacity target input fuel) = SupportOrdinalScan.read bound capacity target input := by
  rw [← residual_halted bound capacity target _
    (run_core bound capacity target input fuel ▸ BoundedSupportPayload.run_wellFormed _ _ _ _) input done]
  exact run_residual _ _ _ _ _

theorem read_correct (bound capacity target : ℕ) (input : List Bool) :
    read bound capacity target input = SupportOrdinalScan.read bound capacity target input :=
  halted_output _ _ _ _ _ (halts_by_length _ _ _ _)

theorem halted_output_eq_read (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ)
    (done : halted (run bound capacity target input fuel) = true) :
    output (run bound capacity target input fuel) = read bound capacity target input := by
  rw [read_correct]
  exact halted_output _ _ _ _ _ done

/-- Every valid support returns its actual width and the matching one-based
position, for arbitrary natural-number queries (including zero and out-of-range). -/
theorem read_encode (bound capacity target : ℕ) (support : List (Fin bound))
    (valid : SupportAssignment.Valid capacity support) :
    read bound capacity target (SupportAssignment.encode support) =
      some (support.length,
        if target ∈ SupportAssignment.positiveSupport support then
          (SupportAssignment.positiveSupport support).idxOf target + 1 else 0) := by
  rw [read_correct]
  exact SupportOrdinalScan.read_encode _ _ _ support valid

/-- Acceptance validates the entire candidate and identifies a unique canonical
support. The retained ordinal cannot conceal a malformed suffix after a hit. -/
theorem read_sound_unique (bound capacity target : ℕ) (input : List Bool)
    (width ordinal : ℕ) (accepted : read bound capacity target input = some (width, ordinal)) :
    ∃! support : List (Fin bound), ∃ _valid : SupportAssignment.Valid capacity support,
      input = SupportAssignment.encode support ∧ width = support.length ∧
        ordinal = if target ∈ SupportAssignment.positiveSupport support then
          (SupportAssignment.positiveSupport support).idxOf target + 1 else 0 := by
  rw [read_correct] at accepted
  exact SupportOrdinalScan.read_sound_unique _ _ _ _ _ _ accepted

theorem read_some_iff (bound capacity target : ℕ) (input : List Bool) (width ordinal : ℕ) :
    read bound capacity target input = some (width, ordinal) ↔
      ∃ support : List (Fin bound), ∃ _valid : SupportAssignment.Valid capacity support,
        input = SupportAssignment.encode support ∧ width = support.length ∧
          ordinal = if target ∈ SupportAssignment.positiveSupport support then
            (SupportAssignment.positiveSupport support).idxOf target + 1 else 0 := by
  rw [read_correct]
  exact SupportOrdinalScan.read_some_iff _ _ _ _ _ _

end NtimeDspace.SupportOrdinalPayload
