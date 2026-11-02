import NtimeDspace.BoundedSupportParser
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine

/-!
A gamma-prefix parser with a constant initial state and indexed bit queries.
The executing state contains five scalar registers and no input suffix or
decoded bit list.  The list parsers below occur only in specifications.
Callback compilation and encoded-space accounting are separate theorems in
`GammaQueryResources`.
-/

namespace NtimeDspace.GammaQueryMachine

open SupportEncoding BoundedSupportParser

/-- Phases 0, 1, 2, 3 mean prefix, payload, accepted, rejected respectively. -/
@[ext]
structure State where
  phase : Fin 4
  cursor : ℕ
  zeros : ℕ
  remaining : ℕ
  accumulator : ℕ
  deriving DecidableEq

def initial : State := ⟨0, 0, 0, 0, 0⟩

/-- An EOF query rejects. Each successful query consumes exactly one bit. -/
def next (argument : State × Option Bool) : State :=
  let s := argument.1
  if s.phase = 0 then
    match argument.2 with
    | none => { s with phase := 3 }
    | some false => { s with cursor := s.cursor + 1, zeros := s.zeros + 1 }
    | some true =>
      ⟨if s.zeros = 0 then 2 else 1, s.cursor + 1, s.zeros, s.zeros, 1⟩
  else if s.phase = 1 then
    match argument.2 with
    | none => { s with phase := 3 }
    | some bit =>
      ⟨if s.remaining ≤ 1 then 2 else 1, s.cursor + 1, s.zeros,
        s.remaining - 1, 2 * s.accumulator + bitValue bit⟩
  else s

def halted (s : State) : Bool := decide (2 ≤ s.phase.val)

def finish (s : State) : List Bool := [decide (s.phase = 2)]

def machine : Turing.QueryMachine State where
  init := initial
  query := State.cursor
  next := next
  emit := fun _ => []
  halted := halted
  finish := finish

/-- A specification of the remaining parse, never stored by the machine. -/
def residual (s : State) (suffix : List Bool) : Option (ℕ × List Bool) :=
  if s.phase = 0 then
    (scanZeros s.zeros suffix).map fun x => (foldBits 1 x.1, x.2)
  else if s.phase = 1 then
    (takeBits s.remaining suffix).map fun x => (foldBits s.accumulator x.1, x.2)
  else if s.phase = 2 then some (s.accumulator, suffix)
  else none

def WellFormed (s : State) : Prop := s.phase = 1 → 0 < s.remaining

private theorem drop_of_none (input : List Bool) (cursor : ℕ)
    (h : input[cursor]? = none) : input.drop cursor = [] := by
  induction input generalizing cursor with
  | nil => simp
  | cons bit rest ih =>
    cases cursor with
    | zero => simp at h
    | succ cursor => exact ih cursor (by simpa using h)

private theorem drop_of_some (input : List Bool) (cursor : ℕ) (bit : Bool)
    (h : input[cursor]? = some bit) :
    input.drop cursor = bit :: input.drop (cursor + 1) := by
  induction input generalizing cursor with
  | nil => simp at h
  | cons b rest ih =>
    cases cursor with
    | zero => simpa using h
    | succ cursor => simpa using ih cursor (by simpa using h)

private theorem payload_cons (remaining accumulator : ℕ) (bit : Bool) (rest : List Bool) :
    (takeBits (remaining + 1) (bit :: rest)).map
        (fun x => (foldBits accumulator x.1, x.2)) =
      (takeBits remaining rest).map
        (fun x => (foldBits (2 * accumulator + bitValue bit) x.1, x.2)) := by
  cases h : takeBits remaining rest <;> simp [takeBits, h, foldBits]

theorem next_wellFormed (s : State) (bit : Option Bool) (wf : WellFormed s) :
    WellFormed (next (s, bit)) := by
  by_cases hp : s.phase = 0
  · cases bit with
    | none => simp [next, hp, WellFormed]
    | some b =>
      cases b with
      | false => simp [next, hp, WellFormed]
      | true =>
        by_cases hz : s.zeros = 0 <;> simp [next, hp, hz, WellFormed]; omega
  · by_cases hq : s.phase = 1
    · cases bit with
      | none => simp [next, hq, WellFormed]
      | some b =>
        by_cases hr : s.remaining ≤ 1 <;>
          simp [next, hq, hr, WellFormed]; omega
    · simpa [next, hp, hq] using wf

theorem residual_next (input : List Bool) (s : State) (wf : WellFormed s)
    (running : halted s = false) :
    residual (next (s, input[s.cursor]?))
        (input.drop (next (s, input[s.cursor]?)).cursor) =
      residual s (input.drop s.cursor) := by
  have phases : s.phase = 0 ∨ s.phase = 1 := by
    have := s.phase.isLt
    simp only [halted, decide_eq_false_iff_not] at running
    have : s.phase.val = 0 ∨ s.phase.val = 1 := by omega
    rcases this with h | h <;> [left; right] <;> exact Fin.ext h
  rcases phases with hp | hp
  · cases h : input[s.cursor]? with
    | none => simp [next, residual, hp, drop_of_none input s.cursor h, scanZeros]
    | some bit =>
      rw [drop_of_some input s.cursor bit h]
      cases bit with
      | false => simp [next, residual, hp, scanZeros]
      | true =>
        by_cases hz : s.zeros = 0
        · simp [next, residual, hp, hz, scanZeros, takeBits, foldBits]
        · simp [next, residual, hp, hz, scanZeros]
  · have positive := wf hp
    obtain ⟨remaining, hr⟩ : ∃ r, s.remaining = r + 1 := ⟨s.remaining - 1, by omega⟩
    cases h : input[s.cursor]? with
    | none => simp [next, residual, hp, hr, drop_of_none input s.cursor h, takeBits]
    | some bit =>
      rw [drop_of_some input s.cursor bit h]
      simp only [next, hp, Fin.isValue, one_ne_zero, ↓reduceIte, hr,
        Nat.add_sub_cancel, residual]
      cases remaining with
      | zero => simp [takeBits, foldBits]
      | succ remaining =>
        simpa using (payload_cons (remaining + 1) s.accumulator bit
          (input.drop (s.cursor + 1))).symm

theorem run_wellFormed (input : List Bool) (time : ℕ) :
    WellFormed (machine.run input time) := by
  induction time with
  | zero => simp [machine, initial, WellFormed]
  | succ time ih =>
    rw [Turing.QueryMachine.run_succ]
    simp only [Turing.QueryMachine.step]
    split_ifs
    · exact ih
    · exact next_wellFormed _ _ ih

theorem run_residual (input : List Bool) (time : ℕ) :
    residual (machine.run input time) (input.drop (machine.run input time).cursor) =
      gammaDecode input := by
  induction time with
  | zero =>
    simp only [Turing.QueryMachine.run_zero, machine, initial, residual,
      Fin.isValue, ↓reduceIte, List.drop_zero, gammaDecode]
    apply Option.map_congr
    intro pair h
    congr 1
    simpa using foldBits_reverse pair.1.reverse
  | succ time ih =>
    rw [Turing.QueryMachine.run_succ]
    simp only [Turing.QueryMachine.step]
    split_ifs with done
    · exact ih
    · exact (residual_next input _ (run_wellFormed input time)
        (by simpa [machine] using done)).trans ih

/-- Bounds on every reachable register, including malformed inputs. -/
def RegisterBounds (inputLength : ℕ) (s : State) : Prop :=
  s.cursor ≤ inputLength ∧ s.zeros ≤ s.cursor ∧ s.remaining ≤ s.zeros ∧
    s.accumulator < 2 ^ (s.cursor + 1)

private theorem some_cursor_lt (input : List Bool) (cursor : ℕ) (bit : Bool)
    (h : input[cursor]? = some bit) : cursor < input.length := by
  by_contra absent
  have empty : input[cursor]? = none := List.getElem?_eq_none (by omega)
  rw [empty] at h
  contradiction

private theorem step_registerBounds (input : List Bool) (s : State)
    (bounds : RegisterBounds input.length s) :
    RegisterBounds input.length (machine.step input s) := by
  rcases bounds with ⟨cursor, zeros, remaining, accumulator⟩
  unfold Turing.QueryMachine.step
  split_ifs with done
  · exact ⟨cursor, zeros, remaining, accumulator⟩
  · change RegisterBounds input.length (next (s, input[s.cursor]?))
    by_cases hp : s.phase = 0
    · simp only [next, hp, ↓reduceIte]
      cases bit : input[s.cursor]? with
      | none => exact ⟨cursor, zeros, remaining, accumulator⟩
      | some b =>
        have within := some_cursor_lt input s.cursor b bit
        cases b with
        | false =>
          refine ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, ?_⟩
          exact accumulator.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp; omega))
        | true =>
          refine ⟨by dsimp; omega, by dsimp; omega, le_rfl, ?_⟩
          exact lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
            (Nat.pow_le_pow_right (by decide) (by dsimp; omega))
    · by_cases hq : s.phase = 1
      · simp only [next, hq, ↓reduceIte]
        cases bit : input[s.cursor]? with
        | none => exact ⟨cursor, zeros, remaining, accumulator⟩
        | some b =>
          have within := some_cursor_lt input s.cursor b bit
          refine ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, ?_⟩
          have small : bitValue b ≤ 1 := by cases b <;> decide
          change 2 * s.accumulator + bitValue b < 2 ^ (s.cursor + 1 + 1)
          rw [pow_succ]
          omega
      · simpa only [next, hp, hq, ↓reduceIte] using
          (show RegisterBounds input.length s from ⟨cursor, zeros, remaining, accumulator⟩)

theorem run_registerBounds (input : List Bool) (time : ℕ) :
    RegisterBounds input.length (machine.run input time) := by
  induction time with
  | zero => simp [machine, initial, RegisterBounds]
  | succ time ih =>
    rw [Turing.QueryMachine.run_succ]
    exact step_registerBounds input _ ih

/-- `cursor - zeros` counts the consumed significant bits, including the
leading one. Prefix states have no significant bits and accumulator zero. -/
def PayloadBounds (s : State) : Prop :=
  (s.phase = 0 → s.zeros = s.cursor ∧ s.accumulator = 0) ∧
    s.accumulator < 2 ^ (s.cursor - s.zeros)

private theorem step_payloadBounds (input : List Bool) (s : State)
    (zeros : s.zeros ≤ s.cursor) (bounds : PayloadBounds s) :
    PayloadBounds (machine.step input s) := by
  obtain ⟨prefixState, accumulator⟩ := bounds
  unfold Turing.QueryMachine.step
  split_ifs with done
  · exact ⟨prefixState, accumulator⟩
  · change PayloadBounds (next (s, input[s.cursor]?))
    by_cases hp : s.phase = 0
    · obtain ⟨same, empty⟩ := prefixState hp
      cases bit : input[s.cursor]? with
      | none => simpa [next, hp, bit, PayloadBounds] using accumulator
      | some b =>
        cases b with
        | false => simp [next, hp, PayloadBounds, same, empty]
        | true =>
          by_cases hz : s.zeros = 0 <;>
            simp [next, hp, hz, PayloadBounds, ← same]
    · by_cases hq : s.phase = 1
      · cases bit : input[s.cursor]? with
        | none => simpa [next, hq, bit, PayloadBounds] using accumulator
        | some b =>
          simp only [next, hq, Fin.isValue, one_ne_zero, ↓reduceIte, PayloadBounds]
          refine ⟨?_, ?_⟩
          · intro wrong
            split_ifs at wrong <;> norm_num at wrong
          · have small : bitValue b ≤ 1 := by cases b <;> decide
            change 2 * s.accumulator + bitValue b < 2 ^ (s.cursor + 1 - s.zeros)
            rw [show s.cursor + 1 - s.zeros = s.cursor - s.zeros + 1 by omega, pow_succ]
            omega
      · simpa only [next, hp, hq, ↓reduceIte] using
          (show PayloadBounds s from ⟨prefixState, accumulator⟩)

theorem run_payloadBounds (input : List Bool) (time : ℕ) :
    PayloadBounds (machine.run input time) := by
  induction time with
  | zero => simp [machine, initial, PayloadBounds]
  | succ time ih =>
    rw [Turing.QueryMachine.run_succ]
    exact step_payloadBounds input _ (run_registerBounds input time).2.1 ih

theorem accumulator_mono (input : List Bool) :
    Monotone (fun time => (machine.run input time).accumulator) := by
  apply monotone_nat_of_le_succ
  intro time
  have prefixState := (run_payloadBounds input time).1
  rw [Turing.QueryMachine.run_succ]
  unfold Turing.QueryMachine.step
  split_ifs with done
  · exact le_rfl
  · change (machine.run input time).accumulator ≤
      (next (machine.run input time, input[(machine.run input time).cursor]?)).accumulator
    generalize machine.run input time = s at *
    by_cases hp : s.phase = 0
    · have empty := (prefixState hp).2
      cases bit : input[s.cursor]? with
      | none => simp [next, hp]
      | some b => cases b <;> simp [next, hp, empty]
    · by_cases hq : s.phase = 1
      · cases bit : input[s.cursor]? with
        | none => simp [next, hq]
        | some b => simp only [next, hq, Fin.isValue, one_ne_zero, ↓reduceIte]; omega
      · simp [next, hp, hq]

private theorem next_running_cursor (s : State) (bit : Option Bool)
    (before : halted s = false) (after : halted (next (s, bit)) = false) :
    (next (s, bit)).cursor = s.cursor + 1 := by
  have phase : s.phase = 0 ∨ s.phase = 1 := by
    simp only [halted, decide_eq_false_iff_not] at before
    have : s.phase.val = 0 ∨ s.phase.val = 1 := by omega
    rcases this with h | h <;> [left; right] <;> exact Fin.ext h
  rcases phase with hp | hp
  · cases bit with
    | none => simp [next, hp, halted] at after
    | some b => cases b <;> simp [next, hp]
  · cases bit with
    | none => simp [next, hp, halted] at after
    | some b => simp [next, hp]

theorem running_cursor (input : List Bool) (time : ℕ)
    (running : halted (machine.run input time) = false) :
    (machine.run input time).cursor = time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [Turing.QueryMachine.run_succ] at running ⊢
    unfold Turing.QueryMachine.step at running ⊢
    split_ifs with done
    · simp only [ite_eq_left done] at running
      have : halted (machine.run input time) = true := done
      rw [this] at running
      contradiction
    · have before : halted (machine.run input time) = false := by
        simpa [machine] using done
      simp only [ite_eq_right done] at running
      exact (next_running_cursor _ _ before running).trans (congrArg (· + 1) (ih before))

theorem halts_by_length (input : List Bool) :
    halted (machine.run input (input.length + 1)) = true := by
  by_contra notDone
  have running : halted (machine.run input (input.length + 1)) = false :=
    Bool.eq_false_iff.mpr notDone
  have cursor := running_cursor input _ running
  have bounded := (run_registerBounds input (input.length + 1)).1
  omega

/-- A specification clock: it is not stored by the executing machine. -/
def stopTime (input : List Bool) : ℕ :=
  Nat.find (show ∃ t, halted (machine.run input t) = true from
    ⟨input.length + 1, halts_by_length input⟩)

theorem stopTime_halts (input : List Bool) :
    halted (machine.run input (stopTime input)) = true := by
  unfold stopTime
  exact Nat.find_spec (show ∃ t, halted (machine.run input t) = true from
    ⟨input.length + 1, halts_by_length input⟩)

theorem before_stopTime (input : List Bool) (time : ℕ) (before : time < stopTime input) :
    halted (machine.run input time) = false := by
  exact Bool.eq_false_iff.mpr (Nat.find_min _ before)

theorem stopTime_le (input : List Bool) : stopTime input ≤ input.length + 1 :=
  Nat.find_min' _ (halts_by_length input)

/-- Whether an input begins with a complete gamma codeword. Trailing bits are
allowed; the accepted state records their starting offset. -/
def valid (input : List Bool) : Bool := (gammaDecode input).isSome

theorem halted_result (input : List Bool) (time : ℕ)
    (done : halted (machine.run input time) = true) :
    gammaDecode input =
      if (machine.run input time).phase = 2 then
        some ((machine.run input time).accumulator,
          input.drop (machine.run input time).cursor)
      else none := by
  have phases : (machine.run input time).phase ≠ 0 ∧
      (machine.run input time).phase ≠ 1 := by
    simp only [halted, decide_eq_true_eq] at done
    constructor <;> intro h <;> rw [h] at done <;> norm_num at done
  simpa [residual, phases.1, phases.2] using (run_residual input time).symm

theorem output_correct (input : List Bool) :
    machine.output input (stopTime input) = [valid input] := by
  have result := halted_result input _ (stopTime_halts input)
  have empty : ∀ time, machine.emit (machine.run input time,
      machine.read input (machine.run input time)) = [] := fun _ => rfl
  rw [machine.output_eq_of_not_halted input (before_stopTime input)]
  simp only [empty, List.map_const', List.length_range,
    List.flatten_replicate_nil, List.nil_append]
  change finish (machine.run input (stopTime input)) = _
  unfold finish valid
  rw [result]
  split_ifs <;> simp_all

private theorem takeBits_sound (count : ℕ) (input payload rest : List Bool)
    (success : takeBits count input = some (payload, rest)) :
    input = payload ++ rest ∧ payload.length = count := by
  induction count generalizing input payload with
  | zero =>
    simp only [takeBits, Option.some.injEq, Prod.mk.injEq] at success
    rcases success with ⟨rfl, rfl⟩
    simp
  | succ count ih =>
    cases input with
    | nil => simp [takeBits] at success
    | cons bit input =>
      cases step : takeBits count input with
      | none => simp [takeBits, step] at success
      | some pair =>
        rcases pair with ⟨tail, rest'⟩
        simp only [takeBits, step, Option.some.injEq, Prod.mk.injEq] at success
        rcases success with ⟨rfl, rfl⟩
        obtain ⟨suffix, length⟩ := ih input tail step
        simp [suffix, length]

private theorem scanZeros_sound (count : ℕ) (input payload rest : List Bool)
    (success : scanZeros count input = some (payload, rest)) :
    ∃ zeros, input = List.replicate zeros false ++ true :: (payload ++ rest) ∧
      payload.length = count + zeros := by
  induction input generalizing count with
  | nil => simp [scanZeros] at success
  | cons bit input ih =>
    cases bit with
    | false =>
      obtain ⟨zeros, suffix, length⟩ := ih (count + 1) success
      refine ⟨zeros + 1, ?_, by omega⟩
      simp [List.replicate_succ, suffix]
    | true =>
      obtain ⟨suffix, length⟩ := takeBits_sound count input payload rest success
      exact ⟨0, by simp [suffix], by simpa using length⟩

theorem gammaDecode_sound (input rest : List Bool) (value : ℕ)
    (success : gammaDecode input = some (value, rest)) :
    0 < value ∧ input = gammaEncode value ++ rest := by
  unfold gammaDecode at success
  cases scanned : scanZeros 0 input with
  | none => simp [scanned] at success
  | some pair =>
    rcases pair with ⟨payload, rest'⟩
    simp only [scanned, Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
    rcases success with ⟨rfl, rfl⟩
    obtain ⟨zeros, suffix, length⟩ := scanZeros_sound 0 input payload rest' scanned
    refine ⟨binaryValue_positive _, ?_⟩
    have value : foldBits 1 payload = binaryValue payload.reverse := by
      simpa using foldBits_reverse payload.reverse
    rw [← value, gammaEncode_foldBits, suffix]
    simp only [Nat.zero_add] at length
    simp [length, List.append_assoc]

/-- Acceptance identifies a positive canonical codeword and its exact consumed
length. This also rules out accepting malformed noncanonical representations. -/
theorem accepted_sound (input : List Bool) (time : ℕ)
    (accepted : (machine.run input time).phase = 2) :
    0 < (machine.run input time).accumulator ∧
      input = gammaEncode (machine.run input time).accumulator ++
        input.drop (machine.run input time).cursor ∧
      (machine.run input time).cursor =
        (gammaEncode (machine.run input time).accumulator).length := by
  have done : halted (machine.run input time) = true := by simp [halted, accepted]
  have decoded := halted_result input time done
  rw [ite_eq_left accepted] at decoded
  obtain ⟨positive, canonical⟩ := gammaDecode_sound input _ _ decoded
  refine ⟨positive, canonical, ?_⟩
  have length := congrArg List.length canonical
  have bounded := (run_registerBounds input time).1
  simp only [List.length_append, List.length_drop] at length
  omega

/-- On every positive encoded integer, the actual query run returns that
integer and advances exactly past its codeword, preserving arbitrary suffixes. -/
theorem encode_run_correct (value : ℕ) (positive : 0 < value) (rest : List Bool) :
    let input := gammaEncode value ++ rest
    let result := machine.run input (stopTime input)
    result.phase = 2 ∧ result.accumulator = value ∧
      result.cursor = (gammaEncode value).length := by
  dsimp only
  let input := gammaEncode value ++ rest
  have decoded := gammaDecode_encode_append value positive rest
  have result := halted_result input (stopTime input) (stopTime_halts input)
  rw [decoded] at result
  split_ifs at result with accepted
  · have pair := Option.some.inj result
    have value_eq := (congrArg Prod.fst pair).symm
    dsimp only at value_eq
    refine ⟨accepted, value_eq, ?_⟩
    simpa only [value_eq] using (accepted_sound input (stopTime input) accepted).2.2

/-- The unbounded query parser agrees with the bounded support parser whenever
its accepted integer fits the supplied bound. No bound is hidden in `initial`. -/
theorem accepted_bounded (input : List Bool) (time bound : ℕ)
    (accepted : (machine.run input time).phase = 2)
    (fits : (machine.run input time).accumulator ≤ bound) :
    BoundedSupportParser.gamma bound input =
      some (⟨(machine.run input time).accumulator, by omega⟩,
        input.drop (machine.run input time).cursor) := by
  obtain ⟨positive, canonical, _⟩ := accepted_sound input time accepted
  have parsed := gamma_encode_append bound (machine.run input time).accumulator positive fits
    (input.drop (machine.run input time).cursor)
  rw [← canonical] at parsed
  exact parsed

end NtimeDspace.GammaQueryMachine
