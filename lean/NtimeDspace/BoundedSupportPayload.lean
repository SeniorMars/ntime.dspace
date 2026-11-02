import NtimeDspace.BoundedGammaPayload
import NtimeDspace.SupportCardinality
import NtimeDspace.SupportScanSemantics
import NtimeDspace.GammaCursorProgress

/-!
# Cursor-only validation and cardinality of a complete support code

One gamma-parser state is reused for successive positive gaps. The original
input is accessed by cursor; no suffix, gap list, or decoded support is stored.
Outer phases are codeword boundary, inside gamma, accepted, and rejected.
Acceptance occurs only at a codeword boundary at EOF, including the empty code.
This module proves scalar semantics; callback and machine compilation are separate.
-/

namespace NtimeDspace.BoundedSupportPayload

@[ext]
structure State where
  phase : Fin 4
  cumulative : ℕ
  rank : ℕ
  parser : BoundedGammaPayload.State
  deriving DecidableEq

def initial (bound : ℕ) : State :=
  ⟨0, 0, 0, BoundedGammaPayload.initial bound 0⟩

/-- Commit a completed positive gap only after both overflow guards. Failed
and incomplete gamma states retain their current scalar parser registers. -/
def commit (bound capacity : ℕ) (state : State) (parsed : BoundedGammaPayload.State) : State :=
  if parsed.phase = 2 then
    if 0 < parsed.accumulator then
      if parsed.accumulator ≤ bound - state.cumulative then
        if state.rank < capacity then
          ⟨0, state.cumulative + parsed.accumulator, state.rank + 1, parsed⟩
        else { state with phase := 3, parser := parsed }
      else { state with phase := 3, parser := parsed }
    else { state with phase := 3, parser := parsed }
  else if parsed.phase = 3 then { state with phase := 3, parser := parsed }
  else { state with phase := 1, parser := parsed }

def next (bound capacity : ℕ) (argument : State × Option Bool) : State :=
  let state := argument.1
  if state.phase = 0 then
    match argument.2 with
    | none => { state with phase := 2 }
    | some bit =>
      if state.rank < capacity then
        commit bound capacity state
          (BoundedGammaPayload.next bound
            (BoundedGammaPayload.initial bound state.parser.cursor, some bit))
      else { state with phase := 3 }
  else if state.phase = 1 then
    commit bound capacity state (BoundedGammaPayload.next bound (state.parser, argument.2))
  else state

def query (state : State) : ℕ := state.parser.cursor

def halted (state : State) : Bool := decide (2 ≤ state.phase.val)

def output (state : State) : Option ℕ := if state.phase = 2 then some state.rank else none

def step (bound capacity : ℕ) (input : List Bool) (state : State) : State :=
  if halted state then state else next bound capacity (state, input[query state]?)

def run (bound capacity : ℕ) (input : List Bool) (fuel : ℕ) : State :=
  (step bound capacity input)^[fuel] (initial bound)

def read (bound capacity : ℕ) (input : List Bool) : Option ℕ :=
  output (run bound capacity input (input.length + 1))

@[simp] theorem run_zero (bound capacity : ℕ) (input : List Bool) :
    run bound capacity input 0 = initial bound := rfl

theorem run_succ (bound capacity : ℕ) (input : List Bool) (fuel : ℕ) :
    run bound capacity input (fuel + 1) = step bound capacity input (run bound capacity input fuel) :=
  Function.iterate_succ_apply' _ _ _

structure WellFormed (bound capacity : ℕ) (state : State) : Prop where
  cumulative_le : state.cumulative ≤ bound
  rank_le : state.rank ≤ capacity
  parser_wellFormed : BoundedGammaPayload.WellFormed bound state.parser
  inside : state.phase = 1 → state.parser.phase = 0 ∨ state.parser.phase = 1

theorem initial_wellFormed (bound capacity : ℕ) : WellFormed bound capacity (initial bound) := by
  exact ⟨Nat.zero_le _, Nat.zero_le _, BoundedGammaPayload.initial_wellFormed _ _, by simp [initial]⟩

private theorem phase_small (phase : Fin 4) (notAccepted : phase ≠ 2) (notRejected : phase ≠ 3) :
    phase = 0 ∨ phase = 1 := by
  fin_cases phase <;> simp_all

theorem commit_wellFormed (bound capacity : ℕ) (state : State)
    (parsed : BoundedGammaPayload.State) (wf : WellFormed bound capacity state)
    (parserWF : BoundedGammaPayload.WellFormed bound parsed) :
    WellFormed bound capacity (commit bound capacity state parsed) := by
  unfold commit
  split_ifs with accepted positive fits room rejected
  · refine ⟨?_, ?_, parserWF, ?_⟩
    · dsimp
      have := wf.cumulative_le
      omega
    · dsimp
      omega
    · simp
  · exact ⟨wf.cumulative_le, wf.rank_le, parserWF, by simp⟩
  · exact ⟨wf.cumulative_le, wf.rank_le, parserWF, by simp⟩
  · exact ⟨wf.cumulative_le, wf.rank_le, parserWF, by simp⟩
  · exact ⟨wf.cumulative_le, wf.rank_le, parserWF, by simp⟩
  · exact ⟨wf.cumulative_le, wf.rank_le, parserWF, fun _ => phase_small _ accepted rejected⟩

theorem next_wellFormed (bound capacity : ℕ) (state : State) (bit : Option Bool)
    (wf : WellFormed bound capacity state) : WellFormed bound capacity (next bound capacity (state, bit)) := by
  by_cases boundary : state.phase = 0
  · cases bit with
    | none => simpa [next, boundary] using
        (show WellFormed bound capacity { state with phase := 2 } from
          ⟨wf.cumulative_le, wf.rank_le, wf.parser_wellFormed, by simp⟩)
    | some bit =>
      by_cases room : state.rank < capacity
      · simpa only [next, boundary, room, ↓reduceIte] using
          commit_wellFormed bound capacity state _ wf
            (BoundedGammaPayload.next_wellFormed _ _ _ (BoundedGammaPayload.initial_wellFormed _ _))
      · simpa only [next, boundary, room, ↓reduceIte] using
          (show WellFormed bound capacity { state with phase := 3 } from
            ⟨wf.cumulative_le, wf.rank_le, wf.parser_wellFormed, by simp⟩)
  · by_cases inside : state.phase = 1
    · simpa [next, inside] using
        commit_wellFormed bound capacity state _ wf
          (BoundedGammaPayload.next_wellFormed _ _ _ wf.parser_wellFormed)
    · simpa only [next, boundary, inside, ↓reduceIte] using wf

theorem run_wellFormed (bound capacity : ℕ) (input : List Bool) (fuel : ℕ) :
    WellFormed bound capacity (run bound capacity input fuel) := by
  induction fuel with
  | zero => exact initial_wellFormed _ _
  | succ fuel ih =>
    rw [run_succ]
    unfold step
    split_ifs
    · exact ih
    · exact next_wellFormed _ _ _ _ ih

theorem commit_parser (bound capacity : ℕ) (state : State) (parsed : BoundedGammaPayload.State) :
    (commit bound capacity state parsed).parser = parsed := by
  unfold commit
  split_ifs <;> rfl

theorem next_cursor_bounds (bound capacity : ℕ) (state : State) (bit : Option Bool) :
    state.parser.cursor ≤ (next bound capacity (state, bit)).parser.cursor ∧
      (next bound capacity (state, bit)).parser.cursor ≤ state.parser.cursor + 1 ∧
      (bit = none → (next bound capacity (state, bit)).parser.cursor = state.parser.cursor) := by
  have parser := GammaCursorProgress.next_cursor_bounds bound state.parser bit
  have reset := GammaCursorProgress.next_cursor_bounds bound
    (BoundedGammaPayload.initial bound state.parser.cursor) bit
  by_cases boundary : state.phase = 0
  · cases bit with
    | none => simp [next, boundary]
    | some bit =>
      by_cases room : state.rank < capacity
      · simpa [next, boundary, room, commit_parser, BoundedGammaPayload.initial] using reset
      · simp [next, boundary, room]
  · by_cases inside : state.phase = 1
    · simpa only [next, boundary, inside, Fin.reduceEq, ↓reduceIte, commit_parser] using parser
    · simp [next, boundary, inside]

theorem step_cursor_bound (bound capacity : ℕ) (input : List Bool) (state : State)
    (prior : state.parser.cursor ≤ input.length) :
    (BoundedSupportPayload.step bound capacity input state).parser.cursor ≤ input.length := by
  unfold BoundedSupportPayload.step
  split_ifs with done
  · exact prior
  · have movement := next_cursor_bounds bound capacity state input[query state]?
    by_cases within : state.parser.cursor < input.length
    · omega
    · have absent : input[query state]? = none := by
        apply List.getElem?_eq_none
        simpa only [BoundedSupportPayload.query] using Nat.le_of_not_gt within
      have stationary := movement.2.2 absent
      omega

theorem run_cursor_bound (bound capacity : ℕ) (input : List Bool) (fuel : ℕ) :
    (run bound capacity input fuel).parser.cursor ≤ input.length := by
  induction fuel with
  | zero => exact Nat.zero_le _
  | succ fuel ih => rw [run_succ]; exact step_cursor_bound _ _ _ _ ih


/-- No register grows with a decoded support list: every prefix, including malformed
candidates, retains only bounded counters and the gamma parser registers. -/
theorem run_register_bounds (bound capacity : ℕ) (input : List Bool) (fuel : ℕ) :
    let state := run bound capacity input fuel
    state.cumulative ≤ bound ∧ state.rank ≤ capacity ∧
      state.parser.cursor ≤ input.length ∧ state.parser.zeros ≤ bound.log2 ∧
      state.parser.remaining ≤ bound.log2 ∧ state.parser.accumulator ≤ bound ∧
      state.parser.room ≤ bound := by
  have wf := run_wellFormed bound capacity input fuel
  exact ⟨wf.cumulative_le, wf.rank_le, run_cursor_bound _ _ _ _,
    wf.parser_wellFormed.zeros_le,
    wf.parser_wellFormed.remaining_le.trans wf.parser_wellFormed.zeros_le,
    wf.parser_wellFormed.accumulator_le, wf.parser_wellFormed.room_le⟩

private theorem commit_notRejected (bound capacity : ℕ) (state : State)
    (parsed : BoundedGammaPayload.State)
    (running : halted (commit bound capacity state parsed) = false) : parsed.phase ≠ 3 := by
  intro rejected
  simp [commit, rejected, halted] at running

private theorem next_running_cursor (bound capacity : ℕ) (state : State) (bit : Option Bool)
    (before : halted state = false)
    (inside : state.phase = 1 → BoundedGammaPayload.halted state.parser = false)
    (after : halted (next bound capacity (state, bit)) = false) :
    (next bound capacity (state, bit)).parser.cursor = state.parser.cursor + 1 := by
  by_cases boundary : state.phase = 0
  · cases bit with
    | none => simp [next, boundary, halted] at after
    | some bit =>
      by_cases room : state.rank < capacity
      · simp only [next, boundary, room, ↓reduceIte] at after ⊢
        rw [commit_parser]
        exact GammaCursorProgress.next_notRejected_cursor bound
          (BoundedGammaPayload.initial bound state.parser.cursor) (some bit)
          (by simp [BoundedGammaPayload.halted, BoundedGammaPayload.initial])
          (commit_notRejected _ _ _ _ after)
      · simp [next, boundary, room, halted] at after
  · have reading : state.phase = 1 := by
      have value : state.phase.val ≠ 0 := fun same => boundary (Fin.ext same)
      simp only [halted, decide_eq_false_iff_not] at before
      apply Fin.ext
      omega
    simp only [next, reading, Fin.reduceEq, ↓reduceIte] at after ⊢
    rw [commit_parser]
    exact GammaCursorProgress.next_notRejected_cursor bound state.parser bit (inside reading)
      (commit_notRejected _ _ _ _ after)

theorem running_cursor (bound capacity : ℕ) (input : List Bool) (fuel : ℕ)
    (running : halted (run bound capacity input fuel) = false) :
    (run bound capacity input fuel).parser.cursor = fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [run_succ] at running ⊢
    unfold step at running ⊢
    split_ifs with done
    · simp [done] at running
    · have before : halted (run bound capacity input fuel) = false := by simpa using done
      have inside : (run bound capacity input fuel).phase = 1 →
          BoundedGammaPayload.halted (run bound capacity input fuel).parser = false := by
        intro reading
        rcases (run_wellFormed bound capacity input fuel).inside reading with pref | payload
        · simp [BoundedGammaPayload.halted, pref]
        · simp [BoundedGammaPayload.halted, payload]
      simp only [ite_eq_right done] at running
      rw [next_running_cursor _ _ _ _ before inside running, ih before]

/-- Every nonhalting transition consumes one original input bit. One further EOF
query suffices to accept a boundary or reject an incomplete codeword. -/
theorem halts_by_length (bound capacity : ℕ) (input : List Bool) :
    halted (run bound capacity input (input.length + 1)) = true := by
  by_contra notDone
  have running : halted (run bound capacity input (input.length + 1)) = false :=
    Bool.eq_false_iff.mpr notDone
  have cursor := running_cursor bound capacity input _ running
  have bounded := run_cursor_bound bound capacity input (input.length + 1)
  omega

private def scanValue (bound capacity cumulative rank : ℕ)
    (cumulativeBound : cumulative ≤ bound) (rankBound : rank ≤ capacity) (input : List Bool) : Option ℕ :=
  (BoundedSupportParser.scan bound capacity ⟨0, by omega⟩
    { cumulative := ⟨cumulative, by omega⟩, rank := ⟨rank, by omega⟩, found := false } input).map
      (fun state => state.rank.val)

private def afterGap (bound capacity cumulative rank : ℕ)
    (pair : Fin (bound + 1) × List Bool) : Option ℕ :=
  if positive : 0 < pair.1.val then
    if fits : pair.1.val ≤ bound - cumulative then
      if room : rank < capacity then
        scanValue bound capacity (cumulative + pair.1.val) (rank + 1)
          (by omega) (by omega) pair.2
      else none
    else none
  else none

/-- A proof-side continuation of the complete support scan. The suffix and
bounded proof objects occur only here, never in the executing state. -/
private def residual (bound capacity : ℕ) (state : State)
    (wf : WellFormed bound capacity state) (input : List Bool) : Option ℕ :=
  if state.phase = 0 then
    scanValue bound capacity state.cumulative state.rank wf.cumulative_le wf.rank_le
      (input.drop state.parser.cursor)
  else if state.phase = 1 then
    (BoundedGammaPayload.residual bound state.parser wf.parser_wellFormed
      (input.drop state.parser.cursor)).bind (afterGap bound capacity state.cumulative state.rank)
  else output state

private theorem commit_residual (bound capacity : ℕ) (state : State)
    (parsed : BoundedGammaPayload.State) (wf : WellFormed bound capacity state)
    (parserWF : BoundedGammaPayload.WellFormed bound parsed) (input : List Bool) :
    residual bound capacity (commit bound capacity state parsed)
      (commit_wellFormed _ _ _ _ wf parserWF) input =
      (BoundedGammaPayload.residual bound parsed parserWF (input.drop parsed.cursor)).bind
        (afterGap bound capacity state.cumulative state.rank) := by
  by_cases accepted : parsed.phase = 2
  · simp only [commit, accepted, ↓reduceIte]
    split_ifs with positive fits room <;>
      simp_all [residual, BoundedGammaPayload.residual, afterGap, output]
  · by_cases rejected : parsed.phase = 3
    · simp [commit, rejected, residual, output, BoundedGammaPayload.residual]
    · rcases phase_small parsed.phase accepted rejected with pref | payload
      · simp [commit, residual, BoundedGammaPayload.residual, pref]
      · simp [commit, residual, BoundedGammaPayload.residual, payload]

private theorem scanValue_nonempty (bound capacity cumulative rank : ℕ)
    (cumulativeBound : cumulative ≤ bound) (rankBound : rank ≤ capacity)
    (input : List Bool) (nonempty : input ≠ []) (room : rank < capacity) :
    scanValue bound capacity cumulative rank cumulativeBound rankBound input =
      (BoundedSupportParser.gamma bound input).bind (afterGap bound capacity cumulative rank) := by
  unfold scanValue
  rw [BoundedSupportParser.scan, dite_eq_right nonempty, dite_eq_left room]
  cases parsed : BoundedSupportParser.gamma bound input with
  | none => rfl
  | some pair =>
    rcases pair with ⟨gap, rest⟩
    by_cases positive : 0 < gap.val
    · by_cases fits : gap.val ≤ bound - cumulative
      · simp only [positive, fits, ↓reduceDIte, Option.bind_some, afterGap, room]
        unfold scanValue
        exact SupportScanSemantics.scan_rank_found bound capacity ⟨0, by omega⟩
          { cumulative := ⟨cumulative + gap.val, by omega⟩,
            rank := ⟨rank + 1, by omega⟩, found := false }
          (false || decide (cumulative + gap.val = 0)) rest
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

private theorem residual_next (bound capacity : ℕ) (state : State)
    (wf : WellFormed bound capacity state) (input : List Bool) :
    residual bound capacity (next bound capacity (state, input[query state]?))
      (next_wellFormed _ _ _ _ wf) input = residual bound capacity state wf input := by
  by_cases boundary : state.phase = 0
  · cases bit : input[state.parser.cursor]? with
    | none =>
      simp [next, query, bit, boundary, residual, scanValue, output,
        drop_of_none input state.parser.cursor bit, BoundedSupportParser.scan]
    | some bitValue =>
      have nonempty : input.drop state.parser.cursor ≠ [] := by
        rw [drop_of_some input state.parser.cursor bitValue bit]
        exact List.cons_ne_nil _ _
      by_cases room : state.rank < capacity
      · simp only [next, query, boundary, bit, room, ↓reduceIte]
        rw [commit_residual bound capacity state _ wf
          (BoundedGammaPayload.next_wellFormed _ _ _ (BoundedGammaPayload.initial_wellFormed _ _))]
        have gamma := BoundedGammaPayload.residual_next bound input
          (BoundedGammaPayload.initial bound state.parser.cursor)
          (BoundedGammaPayload.initial_wellFormed _ _)
          (by simp [BoundedGammaPayload.halted, BoundedGammaPayload.initial])
        simp only [BoundedGammaPayload.initial, bit] at gamma
        simp only [BoundedGammaPayload.initial]
        rw [gamma]
        change (BoundedSupportParser.gamma bound (input.drop state.parser.cursor)).bind
          (afterGap bound capacity state.cumulative state.rank) = _
        simpa only [residual, boundary, ↓reduceIte] using
          (scanValue_nonempty bound capacity state.cumulative state.rank
            wf.cumulative_le wf.rank_le _ nonempty room).symm
      · simp [next, query, bit, boundary, room, residual, output, scanValue,
          BoundedSupportParser.scan, nonempty]
  · by_cases inside : state.phase = 1
    · have running : BoundedGammaPayload.halted state.parser = false := by
        rcases wf.inside inside with pref | payload
        · simp [BoundedGammaPayload.halted, pref]
        · simp [BoundedGammaPayload.halted, payload]
      simp only [next, query, inside, Fin.reduceEq, ↓reduceIte]
      rw [commit_residual bound capacity state _ wf
        (BoundedGammaPayload.next_wellFormed _ _ _ wf.parser_wellFormed)]
      rw [BoundedGammaPayload.residual_next bound input state.parser wf.parser_wellFormed running]
      simp [residual, inside]
    · simp only [next, boundary, inside, ↓reduceIte]

private theorem run_residual (bound capacity : ℕ) (input : List Bool) (fuel : ℕ) :
    residual bound capacity (run bound capacity input fuel) (run_wellFormed _ _ _ _) input =
      (SupportCardinality.count bound capacity input).map Fin.val := by
  induction fuel with
  | zero =>
    simp [residual, initial, BoundedGammaPayload.initial, scanValue,
      SupportCardinality.count, SupportCardinality.initial, Option.map_map, Function.comp_def]
  | succ fuel ih =>
    simp only [run_succ]
    unfold step
    split_ifs
    · exact ih
    · exact (residual_next _ _ _ (run_wellFormed _ _ _ _) input).trans ih

private theorem residual_halted (bound capacity : ℕ) (state : State)
    (wf : WellFormed bound capacity state) (input : List Bool) (done : halted state = true) :
    residual bound capacity state wf input = output state := by
  have phases : state.phase ≠ 0 ∧ state.phase ≠ 1 := by
    simp only [halted, decide_eq_true_eq] at done
    constructor <;> intro same <;> rw [same] at done <;> norm_num at done
  simp [residual, phases.1, phases.2]

theorem halted_output (bound capacity : ℕ) (input : List Bool) (fuel : ℕ)
    (done : halted (run bound capacity input fuel) = true) :
    output (run bound capacity input fuel) =
      (SupportCardinality.count bound capacity input).map Fin.val := by
  rw [← residual_halted bound capacity _ (run_wellFormed _ _ _ _) input done]
  exact run_residual _ _ _ _

/-- The cursor-only scalar scanner agrees on every input, including malformed
candidates, with the independently verified complete support-code parser. -/
theorem read_correct (bound capacity : ℕ) (input : List Bool) :
    read bound capacity input = (SupportCardinality.count bound capacity input).map Fin.val := by
  exact halted_output bound capacity input (input.length + 1) (halts_by_length _ _ _)

theorem halted_output_eq_read (bound capacity : ℕ) (input : List Bool) (fuel : ℕ)
    (done : halted (run bound capacity input fuel) = true) :
    output (run bound capacity input fuel) = read bound capacity input := by
  rw [read_correct]
  exact halted_output _ _ _ _ done

end NtimeDspace.BoundedSupportPayload
