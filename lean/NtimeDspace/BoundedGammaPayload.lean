import NtimeDspace.BoundedSupportParser

/-!
A bounded gamma reader using indexed input queries and scalar registers only.
The bound and starting cursor are explicit inputs to initialization and stepping.
The prefix guard halves `room`; no logarithm or power is evaluated by the reader.
No input suffix or decoded list is retained in the state; `drop` is specification-only.
This module does not compile input-dependent initialization to a tape machine.
-/

namespace NtimeDspace.BoundedGammaPayload

open SupportEncoding BoundedSupportParser

/-- Prefix, payload, accepted, rejected, respectively. -/
@[ext]
structure State where
  phase : Fin 4
  cursor : ℕ
  zeros : ℕ
  remaining : ℕ
  accumulator : ℕ
  room : ℕ
  deriving DecidableEq

def initial (bound start : ℕ) : State := ⟨0, start, 0, 0, 0, bound⟩

/-- The same pre-arithmetic guard as the bounded list parser, on raw registers. -/
def appendValue (bound accumulator : ℕ) (bit : Bool) : Option ℕ :=
  if bitValue bit ≤ bound then
    if accumulator ≤ (bound - bitValue bit) / 2 then
      some (2 * accumulator + bitValue bit)
    else none
  else none

def next (bound : ℕ) (argument : State × Option Bool) : State :=
  let s := argument.1
  if s.phase = 0 then
    match argument.2 with
    | none => { s with phase := 3 }
    | some false =>
      if 2 ≤ s.room then
        { s with cursor := s.cursor + 1, zeros := s.zeros + 1, room := s.room / 2 }
      else { s with phase := 3 }
    | some true =>
      if 0 < bound then
        ⟨if s.zeros = 0 then 2 else 1, s.cursor + 1, s.zeros, s.zeros, 1, s.room⟩
      else { s with phase := 3 }
  else if s.phase = 1 then
    match argument.2 with
    | none => { s with phase := 3 }
    | some bit =>
      match appendValue bound s.accumulator bit with
      | none => { s with phase := 3 }
      | some value =>
        ⟨if s.remaining ≤ 1 then 2 else 1, s.cursor + 1, s.zeros,
          s.remaining - 1, value, s.room⟩
  else s

def halted (state : State) : Bool := decide (2 ≤ state.phase.val)

def output (state : State) : Option (ℕ × ℕ) :=
  if state.phase = 2 then some (state.accumulator, state.cursor) else none

def step (bound : ℕ) (input : List Bool) (state : State) : State :=
  if halted state then state else next bound (state, input[state.cursor]?)

def run (bound : ℕ) (input : List Bool) (start fuel : ℕ) : State :=
  (step bound input)^[fuel] (initial bound start)

@[simp] theorem run_zero (bound : ℕ) (input : List Bool) (start : ℕ) :
    run bound input start 0 = initial bound start := rfl

theorem run_succ (bound : ℕ) (input : List Bool) (start fuel : ℕ) :
    run bound input start (fuel + 1) = step bound input (run bound input start fuel) :=
  Function.iterate_succ_apply' _ _ _

structure WellFormed (bound : ℕ) (state : State) : Prop where
  zeros_le : state.zeros ≤ bound.log2
  remaining_le : state.remaining ≤ state.zeros
  accumulator_le : state.accumulator ≤ bound
  room_le : state.room ≤ bound
  room_log : state.zeros + state.room.log2 = bound.log2
  payload_positive : state.phase = 1 → 0 < state.remaining

theorem initial_wellFormed (bound start : ℕ) : WellFormed bound (initial bound start) := by
  constructor <;> simp [initial]

theorem appendValue_bounds (bound accumulator value : ℕ) (bit : Bool)
    (success : appendValue bound accumulator bit = some value) :
    value = 2 * accumulator + bitValue bit ∧ value ≤ bound := by
  unfold appendValue at success
  split_ifs at success with low room
  have eq := Option.some.inj success
  have fits := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp room
  constructor <;> omega

theorem appendValue_eq_appendBit (bound : ℕ) (accumulator : Fin (bound + 1)) (bit : Bool) :
    appendValue bound accumulator.val bit = (appendBit bound accumulator bit).map Fin.val := by
  unfold appendValue appendBit
  split_ifs <;> rfl

private theorem room_iff (bound : ℕ) (state : State) (wf : WellFormed bound state) :
    2 ≤ state.room ↔ state.zeros < bound.log2 := by
  have log := Nat.log2_def state.room
  split_ifs at log with room <;> constructor <;> intro h <;>
    have := wf.room_log <;> omega

theorem next_wellFormed (bound : ℕ) (state : State) (bit : Option Bool)
    (wf : WellFormed bound state) : WellFormed bound (next bound (state, bit)) := by
  rcases wf with ⟨zeros, remaining, accumulator, room, roomLog, positive⟩
  by_cases pref : state.phase = 0
  · cases bit with
    | none => simpa [next, pref, WellFormed] using
        (show WellFormed bound { state with phase := 3 } from
          ⟨zeros, remaining, accumulator, room, roomLog, by simp⟩)
    | some bit =>
      cases bit with
      | false =>
        by_cases fits : 2 ≤ state.room
        · have log : state.room.log2 = (state.room / 2).log2 + 1 := by
            simpa [fits] using Nat.log2_def state.room
          simp only [next, pref, ↓reduceIte, fits]
          refine ⟨by dsimp; omega, by dsimp; omega, accumulator,
            (Nat.div_le_self _ _).trans room, by dsimp; omega, by simp⟩
        · simp only [next, pref, ↓reduceIte, fits]
          exact ⟨zeros, remaining, accumulator, room, roomLog, by simp⟩
      | true =>
        by_cases nonzero : 0 < bound
        · simp only [next, pref, ↓reduceIte, nonzero]
          refine ⟨zeros, le_rfl, nonzero, room, roomLog, ?_⟩
          dsimp
          split_ifs with empty <;> simp_all
          omega
        · simp only [next, pref, ↓reduceIte, nonzero]
          exact ⟨zeros, remaining, accumulator, room, roomLog, by simp⟩
  · by_cases payload : state.phase = 1
    · cases bit with
      | none =>
        simp only [next, payload, ↓reduceIte]
        exact ⟨zeros, remaining, accumulator, room, roomLog, by simp⟩
      | some bit =>
        cases result : appendValue bound state.accumulator bit with
        | none =>
          simp only [next, payload, ↓reduceIte, result]
          exact ⟨zeros, remaining, accumulator, room, roomLog, by simp⟩
        | some value =>
          have fits := (appendValue_bounds _ _ _ _ result).2
          simp only [next, payload, ↓reduceIte, result]
          refine ⟨zeros, by dsimp; omega, fits, room, roomLog, ?_⟩
          dsimp
          split_ifs with last <;> simp_all
    · simpa [next, pref, payload] using
        (show WellFormed bound state from ⟨zeros, remaining, accumulator, room, roomLog, positive⟩)

theorem run_wellFormed (bound : ℕ) (input : List Bool) (start fuel : ℕ) :
    WellFormed bound (run bound input start fuel) := by
  induction fuel with
  | zero => exact initial_wellFormed _ _
  | succ fuel ih =>
    rw [run_succ]
    unfold step
    split_ifs
    · exact ih
    · exact next_wellFormed _ _ _ ih

/-- This residual is a proof-side list specification; it is never retained. -/
def residual (bound : ℕ) (state : State) (wf : WellFormed bound state) (suffix : List Bool) :
    Option (Fin (bound + 1) × List Bool) :=
  if state.phase = 0 then readPrefix bound ⟨state.zeros, by have := wf.zeros_le; omega⟩ suffix
  else if state.phase = 1 then
    readPayload bound ⟨state.remaining, by have := wf.remaining_le; have := wf.zeros_le; omega⟩
      ⟨state.accumulator, by have := wf.accumulator_le; omega⟩ suffix
  else if state.phase = 2 then
    some (⟨state.accumulator, by have := wf.accumulator_le; omega⟩, suffix)
  else none

private theorem drop_of_none (input : List Bool) (cursor : ℕ)
    (h : input[cursor]? = none) : input.drop cursor = [] := by
  induction input generalizing cursor with
  | nil => simp
  | cons bit rest ih =>
    cases cursor with
    | zero => simp at h
    | succ cursor => exact ih cursor (by simpa using h)

private theorem drop_of_some (input : List Bool) (cursor : ℕ) (bit : Bool)
    (h : input[cursor]? = some bit) : input.drop cursor = bit :: input.drop (cursor + 1) := by
  induction input generalizing cursor with
  | nil => simp at h
  | cons b rest ih =>
    cases cursor with
    | zero => simpa using h
    | succ cursor => simpa using ih cursor (by simpa using h)

private theorem running_phase (state : State) (running : halted state = false) :
    state.phase = 0 ∨ state.phase = 1 := by
  simp only [halted, decide_eq_false_iff_not] at running
  have : state.phase.val = 0 ∨ state.phase.val = 1 := by omega
  rcases this with h | h <;> [left; right] <;> exact Fin.ext h

private theorem readPayload_zero (bound : ℕ) (accumulator : Fin (bound + 1))
    (suffix : List Bool) : readPayload bound 0 accumulator suffix = some (accumulator, suffix) := by
  rw [readPayload.eq_def]
  simp

theorem residual_next (bound : ℕ) (input : List Bool) (state : State)
    (wf : WellFormed bound state) (running : halted state = false) :
    residual bound (next bound (state, input[state.cursor]?))
      (next_wellFormed _ _ _ wf) (input.drop (next bound (state, input[state.cursor]?)).cursor) =
      residual bound state wf (input.drop state.cursor) := by
  rcases running_phase state running with pref | payload
  · cases bit : input[state.cursor]? with
    | none => simp [next, residual, pref, drop_of_none input state.cursor bit, readPrefix]
    | some bitValue =>
      rw [drop_of_some input state.cursor bitValue bit]
      cases bitValue with
      | false =>
        have fits := room_iff bound state wf
        by_cases room : 2 ≤ state.room
        · have below := fits.mp room
          simp [next, residual, pref, room, readPrefix, below]
        · have full : ¬state.zeros < bound.log2 := by omega
          simp [next, residual, pref, room, readPrefix, full]
      | true =>
        by_cases nonzero : 0 < bound
        · by_cases empty : state.zeros = 0
          · simp [next, residual, pref, nonzero, empty, readPrefix, readPayload_zero]
          · simp [next, residual, pref, nonzero, empty, readPrefix]
        · simp [next, residual, pref, nonzero, readPrefix]
  · have positive := wf.payload_positive payload
    have notPrefix : state.phase ≠ 0 := by simp [payload]
    cases bit : input[state.cursor]? with
    | none =>
      simp [next, residual, payload, drop_of_none input state.cursor bit, readPayload,
        Nat.ne_of_gt positive]
    | some bitValue =>
      rw [drop_of_some input state.cursor bitValue bit]
      let acc : Fin (bound + 1) := ⟨state.accumulator, by have := wf.accumulator_le; omega⟩
      have append := appendValue_eq_appendBit bound acc bitValue
      cases result : appendBit bound acc bitValue with
      | none =>
        have raw : appendValue bound state.accumulator bitValue = none := by simpa [result] using append
        simp [next, residual, payload, raw, readPayload, Nat.ne_of_gt positive, result, acc]
      | some value =>
        have raw : appendValue bound state.accumulator bitValue = some value.val := by
          simpa [result] using append
        by_cases last : state.remaining ≤ 1
        · have one : state.remaining = 1 := by omega
          simp [next, residual, payload, raw, one, readPayload, result, acc, readPayload_zero]
        · simp [next, residual, payload, raw, last, readPayload, Nat.ne_of_gt positive,
            result, acc]

theorem run_residual (bound : ℕ) (input : List Bool) (start fuel : ℕ) :
    residual bound (run bound input start fuel) (run_wellFormed _ _ _ _)
      (input.drop (run bound input start fuel).cursor) = gamma bound (input.drop start) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [run_succ]
    unfold step
    split_ifs with done
    · exact ih
    · exact (residual_next bound input _ (run_wellFormed _ _ _ _) (by simpa using done)).trans ih

private theorem next_cursor (bound : ℕ) (state : State) (bit : Option Bool) :
    state.cursor ≤ (next bound (state, bit)).cursor ∧
      (next bound (state, bit)).cursor ≤ state.cursor + 1 ∧
      (bit = none → (next bound (state, bit)).cursor = state.cursor) := by
  cases bit with
  | none => simp only [next]; split_ifs <;> simp
  | some bit =>
    cases bit <;> simp only [next, appendValue] <;> split_ifs <;> simp_all

theorem step_cursor_bounds (bound : ℕ) (input : List Bool) (state : State)
    (start : ℕ) (bounds : start ≤ state.cursor ∧ state.cursor ≤ max start input.length) :
    start ≤ (step bound input state).cursor ∧
      (step bound input state).cursor ≤ max start input.length := by
  unfold step
  split_ifs
  · exact bounds
  · have movement := next_cursor bound state input[state.cursor]?
    refine ⟨bounds.1.trans movement.1, ?_⟩
    by_cases within : state.cursor < input.length
    · have : input.length ≤ max start input.length := le_max_right _ _
      omega
    · have absent : input[state.cursor]? = none := List.getElem?_eq_none (by omega)
      rw [movement.2.2 absent]
      exact bounds.2

theorem run_cursor_bounds (bound : ℕ) (input : List Bool) (start fuel : ℕ) :
    start ≤ (run bound input start fuel).cursor ∧
      (run bound input start fuel).cursor ≤ max start input.length := by
  induction fuel with
  | zero => simp [initial]
  | succ fuel ih => rw [run_succ]; exact step_cursor_bounds _ _ _ _ ih

/-- All registers are bounded even for truncated, excessive, or overflowing codewords.
An out-of-range starting cursor is retained until the first EOF query rejects. -/
theorem run_register_bounds (bound : ℕ) (input : List Bool) (start fuel : ℕ) :
    let state := run bound input start fuel
    start ≤ state.cursor ∧ state.cursor ≤ max start input.length ∧
      state.zeros ≤ bound.log2 ∧ state.remaining ≤ bound.log2 ∧
      state.accumulator ≤ bound ∧ state.room ≤ bound := by
  have wf := run_wellFormed bound input start fuel
  have cursor := run_cursor_bounds bound input start fuel
  exact ⟨cursor.1, cursor.2, wf.zeros_le, wf.remaining_le.trans wf.zeros_le,
    wf.accumulator_le, wf.room_le⟩

private theorem next_running_cursor (bound : ℕ) (state : State) (bit : Option Bool)
    (before : halted state = false) (after : halted (next bound (state, bit)) = false) :
    (next bound (state, bit)).cursor = state.cursor + 1 := by
  rcases running_phase state before with pref | payload
  · cases bit with
    | none => simp [next, pref, halted] at after
    | some bit =>
      cases bit <;> simp only [next, pref, ↓reduceIte] at after ⊢ <;>
        split_ifs at after ⊢ <;> simp_all [halted]
  · cases bit with
    | none => simp [next, payload, halted] at after
    | some bit =>
      cases result : appendValue bound state.accumulator bit <;>
        simp [next, payload, result, halted] at after ⊢

theorem running_cursor (bound : ℕ) (input : List Bool) (start fuel : ℕ)
    (running : halted (run bound input start fuel) = false) :
    (run bound input start fuel).cursor = start + fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [run_succ] at running ⊢
    unfold step at running ⊢
    split_ifs with done
    · simp [done] at running
    · have before : halted (run bound input start fuel) = false := by simpa using done
      simp only [ite_eq_right done] at running
      rw [next_running_cursor _ _ _ before running, ih before]
      omega

theorem halts_by_length (bound : ℕ) (input : List Bool) (start : ℕ) :
    halted (run bound input start (input.length + 1)) = true := by
  by_contra notDone
  have running : halted (run bound input start (input.length + 1)) = false :=
    Bool.eq_false_iff.mpr notDone
  have cursor := running_cursor bound input start _ running
  have bounded := (run_cursor_bounds bound input start (input.length + 1)).2
  omega

/-- Finite cursor evaluation. The fuel counter is at most `input.length + 1`;
the input itself remains immutable and is never copied into the state. -/
def read (bound : ℕ) (input : List Bool) (start : ℕ) : Option (ℕ × ℕ) :=
  output (run bound input start (input.length + 1))

theorem halted_result (bound : ℕ) (input : List Bool) (start fuel : ℕ)
    (done : halted (run bound input start fuel) = true) :
    (gamma bound (input.drop start)).map (fun pair => (pair.1.val, pair.2)) =
      (output (run bound input start fuel)).map (fun pair => (pair.1, input.drop pair.2)) := by
  let state := run bound input start fuel
  have phases : state.phase ≠ 0 ∧ state.phase ≠ 1 := by
    simp only [halted, decide_eq_true_eq] at done
    constructor <;> intro h <;> change (run bound input start fuel).phase = _ at h <;>
      rw [h] at done <;> norm_num at done
  rw [← run_residual bound input start fuel]
  change (residual bound state _ (input.drop state.cursor)).map _ = (output state).map _
  simp only [residual, phases.1, phases.2, ↓reduceIte, output]
  split_ifs <;> rfl

theorem read_correct (bound : ℕ) (input : List Bool) (start : ℕ) :
    (gamma bound (input.drop start)).map (fun pair => (pair.1.val, pair.2)) =
      (read bound input start).map (fun pair => (pair.1, input.drop pair.2)) :=
  halted_result bound input start _ (halts_by_length _ _ _)

theorem read_cursor_bounds (bound : ℕ) (input : List Bool) (start value cursor : ℕ)
    (success : read bound input start = some (value, cursor)) :
    start ≤ cursor ∧ cursor ≤ max start input.length := by
  have bounds := run_cursor_bounds bound input start (input.length + 1)
  unfold read output at success
  split_ifs at success
  have pair := Option.some.inj success
  have same := congrArg Prod.snd pair
  dsimp only at same
  simpa [same] using bounds

/-- Every accepted prefix is canonical and advances by exactly its code length. -/
theorem read_sound (bound : ℕ) (input : List Bool) (start value cursor : ℕ)
    (success : read bound input start = some (value, cursor)) :
    0 < value ∧ value ≤ bound ∧
      input.drop start = gammaEncode value ++ input.drop cursor ∧
      cursor = start + (gammaEncode value).length := by
  have equation := read_correct bound input start
  rw [success] at equation
  cases parsed : gamma bound (input.drop start) with
  | none => simp [parsed] at equation
  | some pair =>
    rcases pair with ⟨v, rest⟩
    simp only [parsed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at equation
    obtain ⟨positive, fits, canonical⟩ := gamma_sound bound (input.drop start) rest v parsed
    rw [equation.1] at positive fits canonical
    rw [equation.2] at canonical
    refine ⟨positive, fits, canonical, ?_⟩
    have lengths := congrArg List.length canonical
    have codePositive : 0 < (gammaEncode value).length := by rw [gammaEncode_length]; omega
    have bounds := read_cursor_bounds bound input start value cursor success
    simp only [List.length_drop, List.length_append] at lengths
    have startWithin : start < input.length := by omega
    have cursorWithin : cursor ≤ input.length := by simpa [max_eq_right startWithin.le] using bounds.2
    omega

/-- Exact acceptance/rejection characterization, including the cursor rather
than an allocated suffix. -/
theorem read_some_iff (bound : ℕ) (input : List Bool) (start value cursor : ℕ) :
    read bound input start = some (value, cursor) ↔
      0 < value ∧ value ≤ bound ∧
        input.drop start = gammaEncode value ++ input.drop cursor ∧
        cursor = start + (gammaEncode value).length := by
  constructor
  · exact read_sound bound input start value cursor
  · rintro ⟨positive, fits, canonical, cursorEq⟩
    have parsed := gamma_encode_append bound value positive fits (input.drop cursor)
    rw [← canonical] at parsed
    have equation := read_correct bound input start
    rw [parsed] at equation
    cases result : read bound input start with
    | none => simp [result] at equation
    | some pair =>
      rcases pair with ⟨value', cursor'⟩
      simp only [result, Option.map_some, Option.some.injEq, Prod.mk.injEq] at equation
      obtain ⟨_, _, _, consumed⟩ := read_sound bound input start value' cursor' result
      rw [← equation.1] at consumed
      have same : cursor' = cursor := consumed.trans cursorEq.symm
      simp [same, equation.1]

theorem read_none_iff (bound : ℕ) (input : List Bool) (start : ℕ) :
    read bound input start = none ↔ gamma bound (input.drop start) = none := by
  have equation := read_correct bound input start
  cases parsed : gamma bound (input.drop start) <;>
    cases result : read bound input start <;> simp_all

theorem read_encode_append (bound value : ℕ) (positive : 0 < value) (fits : value ≤ bound)
    (before after : List Bool) :
    read bound (before ++ gammaEncode value ++ after) before.length =
      some (value, before.length + (gammaEncode value).length) := by
  apply (read_some_iff _ _ _ _ _).mpr
  refine ⟨positive, fits, ?_, rfl⟩
  simp [List.append_assoc, ← List.drop_drop]

end NtimeDspace.BoundedGammaPayload
