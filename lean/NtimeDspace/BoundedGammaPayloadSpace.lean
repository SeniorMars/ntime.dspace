import NtimeDspace.BoundedGammaPayload
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Machine certificates for the bounded gamma reader's scalar callbacks

The phase and five natural registers have an explicit injective binary
encoding. The bound and initial cursor are encoded inputs, and each transition
receives the bound, state, and queried bit as encoded data. All callback space
certificates cover arbitrary raw registers, not only well-formed run states.

This module certifies initialization and the scalar callbacks. It does not
compile their input-query/bootstrap protocol or claim a complete reader
machine. No decoded payload, support list, or input suffix is stored.
-/

namespace NtimeDspace.BoundedGammaPayloadSpace

open Turing Turing.MultiTapeTM ComputableInSpace BoundedGammaPayload

abbrev Data := Fin 4 × ℕ × ℕ × ℕ × ℕ × ℕ

def encPhase : Fin 4 ↪ List Bool := Fin.valEmbedding.trans encNat

def toData : State ↪ Data :=
  ⟨fun s => (s.phase, s.cursor, s.zeros, s.remaining, s.accumulator, s.room), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, State.mk.injEq] using same⟩

def encData : Data ↪ List Bool :=
  encPair encPhase (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))

def encState : State ↪ List Bool := toData.trans encData

abbrev InitialInput := ℕ × ℕ
def encInitial : InitialInput ↪ List Bool := encPair encNat encNat

abbrev AppendInput := ℕ × ℕ × Bool
def encAppend : AppendInput ↪ List Bool := encPair encNat (encPair encNat encBool)

abbrev NextInput := ℕ × State × Option Bool
def encNext : NextInput ↪ List Bool := encPair encNat (encPair encState (encOption encBool))

def encOutput : Option (ℕ × ℕ) ↪ List Bool := encOption (encPair encNat encNat)

private theorem assemble {α : Type} {encIn : α ↪ List Bool}
    {phase : α → Fin 4} {cursor zeros remaining accumulator room : α → ℕ}
    (hp : ComputableInSpace phase encIn encPhase (fun a => (encIn a).length))
    (hc : ComputableInSpace cursor encIn encNat (fun a => (encIn a).length))
    (hz : ComputableInSpace zeros encIn encNat (fun a => (encIn a).length))
    (hr : ComputableInSpace remaining encIn encNat (fun a => (encIn a).length))
    (ha : ComputableInSpace accumulator encIn encNat (fun a => (encIn a).length))
    (hw : ComputableInSpace room encIn encNat (fun a => (encIn a).length)) :
    ComputableInSpace
      (fun a => (⟨phase a, cursor a, zeros a, remaining a, accumulator a, room a⟩ : State))
      encIn encState (fun a => (encIn a).length) :=
  (budget_prod hp (budget_prod hc (budget_prod hz (budget_prod hr (budget_prod ha hw))))).of_enc_eq
    (fun _ => rfl)

theorem initial_inSpace :
    ComputableInSpace (fun input : InitialInput => initial input.1 input.2)
      encInitial encState (fun input => (encInitial input).length) :=
  assemble (budget_const 0 (.refl _)) (snd _ _) (budget_const 0 (.refl _))
    (budget_const 0 (.refl _)) (budget_const 0 (.refl _)) (fst _ _)

theorem phase_inSpace :
    ComputableInSpace State.phase encState encPhase (fun state => (encState state).length) :=
  (fst encPhase (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))).of_encIn_eq
    toData (fun _ => rfl)

private theorem registers_inSpace :
    ComputableInSpace (fun state : State =>
      (state.cursor, state.zeros, state.remaining, state.accumulator, state.room))
      encState (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
      (fun state => (encState state).length) :=
  (snd encPhase (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))).of_encIn_eq
    toData (fun _ => rfl)

theorem query_inSpace :
    ComputableInSpace State.cursor encState encNat (fun state => (encState state).length) :=
  fst' registers_inSpace

theorem zeros_inSpace :
    ComputableInSpace State.zeros encState encNat (fun state => (encState state).length) :=
  fst' (snd' registers_inSpace)

theorem remaining_inSpace :
    ComputableInSpace State.remaining encState encNat (fun state => (encState state).length) :=
  fst' (snd' (snd' registers_inSpace))

theorem accumulator_inSpace :
    ComputableInSpace State.accumulator encState encNat (fun state => (encState state).length) :=
  fst' (snd' (snd' (snd' registers_inSpace)))

theorem room_inSpace :
    ComputableInSpace State.room encState encNat (fun state => (encState state).length) :=
  snd' (snd' (snd' (snd' registers_inSpace)))

/-- The two guards are computed before selecting the enlarged payload branch.
The certificate is global, including bound zero and oversized accumulators. -/
theorem appendValue_inSpace :
    ComputableInSpace (fun input : AppendInput => appendValue input.1 input.2.1 input.2.2)
      encAppend (encOption encNat) (fun input => (encAppend input).length) := by
  have bound : ComputableInSpace (fun input : AppendInput => input.1) encAppend encNat
      (fun input => (encAppend input).length) := fst _ _
  have rest : ComputableInSpace (fun input : AppendInput => input.2) encAppend
      (encPair encNat encBool) (fun input => (encAppend input).length) := snd _ _
  have accumulator := fst' rest
  have bit := budget_finite (encC := encNat) BoundedSupportParser.bitValue (snd' rest)
  have low := budget_natLt bit (budget_natSucc bound)
  have half := budget_natDiv (budget_natSub bound bit) (budget_const 2 (.refl _))
  have fits := budget_natLt accumulator (budget_natSucc half)
  have enlarged := budget_optionSome
    (budget_natAdd (budget_natMul (budget_const 2 (.refl _)) accumulator) bit)
  have absent := budget_const (encIn := encAppend) (encB := encOption encNat) none (.refl _)
  apply (budget_ite low (budget_ite fits enlarged absent) absent).of_enc_eq
  intro input
  simp only [appendValue, decide_eq_true_eq, Nat.lt_succ_iff]

theorem halted_inSpace :
    ComputableInSpace halted encState encBool (fun state => (encState state).length) :=
  budget_finite (fun phase : Fin 4 => decide (2 ≤ phase.val)) phase_inSpace

theorem output_inSpace :
    ComputableInSpace output encState encOutput (fun state => (encState state).length) := by
  have accepted := budget_finite (encC := encBool)
    (fun phase : Fin 4 => decide (phase = 2)) phase_inSpace
  have pair := budget_prod accumulator_inSpace query_inSpace
  have tagged := budget_comp_linear
    (of_inO (ComputableInDegree.optionSome
      (enc₁ := encPair encNat encNat) (enc := encOption (encPair encNat encNat))).inO_one) pair
  apply (budget_ite accepted tagged
    (budget_const (encB := encOutput) none (.refl _))).of_enc_eq
  intro state
  simp only [output, decide_eq_true_eq, encOutput]

private theorem boundNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.1) encNext encNat
      (fun input => (encNext input).length) := fst _ _

private theorem readNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.2) encNext
      (encPair encState (encOption encBool)) (fun input => (encNext input).length) := snd _ _

private theorem stateNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.2.1) encNext encState
      (fun input => (encNext input).length) := fst' readNext_inSpace

private theorem bitNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.2.2) encNext (encOption encBool)
      (fun input => (encNext input).length) := snd' readNext_inSpace

private theorem phaseNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.2.1.phase) encNext encPhase
      (fun input => (encNext input).length) := budget_comp_linear phase_inSpace stateNext_inSpace

private theorem cursorNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.2.1.cursor) encNext encNat
      (fun input => (encNext input).length) := budget_comp_linear query_inSpace stateNext_inSpace

private theorem zerosNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.2.1.zeros) encNext encNat
      (fun input => (encNext input).length) := budget_comp_linear zeros_inSpace stateNext_inSpace

private theorem remainingNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.2.1.remaining) encNext encNat
      (fun input => (encNext input).length) := budget_comp_linear remaining_inSpace stateNext_inSpace

private theorem accumulatorNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.2.1.accumulator) encNext encNat
      (fun input => (encNext input).length) := budget_comp_linear accumulator_inSpace stateNext_inSpace

private theorem roomNext_inSpace :
    ComputableInSpace (fun input : NextInput => input.2.1.room) encNext encNat
      (fun input => (encNext input).length) := budget_comp_linear room_inSpace stateNext_inSpace

private theorem reject_inSpace :
    ComputableInSpace (fun input : NextInput => ({input.2.1 with phase := 3} : State))
      encNext encState (fun input => (encNext input).length) :=
  assemble (budget_const 3 (.refl _)) cursorNext_inSpace zerosNext_inSpace
    remainingNext_inSpace accumulatorNext_inSpace roomNext_inSpace

private theorem zero_inSpace :
    ComputableInSpace (fun input : NextInput =>
      ({input.2.1 with
        cursor := input.2.1.cursor + 1
        zeros := input.2.1.zeros + 1
        room := input.2.1.room / 2} : State))
      encNext encState (fun input => (encNext input).length) :=
  assemble phaseNext_inSpace (budget_natSucc cursorNext_inSpace)
    (budget_natSucc zerosNext_inSpace) remainingNext_inSpace accumulatorNext_inSpace
    (budget_natDiv roomNext_inSpace (budget_const 2 (.refl _)))

private theorem start_inSpace :
    ComputableInSpace (fun input : NextInput =>
      (⟨if input.2.1.zeros = 0 then 2 else 1, input.2.1.cursor + 1,
        input.2.1.zeros, input.2.1.zeros, 1, input.2.1.room⟩ : State))
      encNext encState (fun input => (encNext input).length) := by
  have phase := budget_ite (budget_natIsZero zerosNext_inSpace)
    (budget_const (encB := encPhase) 2 (.refl _)) (budget_const 1 (.refl _))
  apply (assemble phase (budget_natSucc cursorNext_inSpace) zerosNext_inSpace zerosNext_inSpace
    (budget_const 1 (.refl _)) roomNext_inSpace).of_enc_eq
  intro input
  simp only [decide_eq_true_eq]

private theorem appendNext_inSpace :
    ComputableInSpace (fun input : NextInput =>
      appendValue input.1 input.2.1.accumulator (input.2.2.getD false))
      encNext (encOption encNat) (fun input => (encNext input).length) :=
  budget_comp_linear appendValue_inSpace
    (budget_prod boundNext_inSpace (budget_prod accumulatorNext_inSpace
      (budget_finite (encC := encBool) (fun bit : Option Bool => bit.getD false) bitNext_inSpace)))

private theorem payload_inSpace :
    ComputableInSpace (fun input : NextInput =>
      match appendValue input.1 input.2.1.accumulator (input.2.2.getD false) with
      | none => ({input.2.1 with phase := 3} : State)
      | some value =>
        ⟨if input.2.1.remaining ≤ 1 then 2 else 1, input.2.1.cursor + 1,
          input.2.1.zeros, input.2.1.remaining - 1, value, input.2.1.room⟩)
      encNext encState (fun input => (encNext input).length) := by
  have hasValue := budget_comp_linear
    (of_inO (ComputableInDegree.isSome encNat).inO_one) appendNext_inSpace
  have value := budget_comp_linear
    (of_inO (ComputableInDegree.getD (enc₁ := encNat) (enc := encOption encNat) 0).inO_one)
    appendNext_inSpace
  have phase := budget_ite
    (budget_natLt remainingNext_inSpace (budget_const (encB := encNat) 2 (.refl _)))
    (budget_const (encB := encPhase) 2 (.refl _)) (budget_const 1 (.refl _))
  have advanced := assemble phase (budget_natSucc cursorNext_inSpace) zerosNext_inSpace
    (budget_natPred remainingNext_inSpace) value roomNext_inSpace
  apply (budget_ite hasValue advanced reject_inSpace).of_enc_eq
  intro input
  cases appendValue input.1 input.2.1.accumulator (input.2.2.getD false) <;>
    simp [show input.2.1.remaining < 2 ↔ input.2.1.remaining ≤ 1 by omega]

/-- One finite-control machine computes every transition. Both the payload
overflow guards and the prefix-room guard are explicit arithmetic branches. -/
theorem next_inSpace :
    ComputableInSpace (fun input : NextInput => next input.1 input.2)
      encNext encState (fun input => (encNext input).length) := by
  have noBit := budget_finite (encC := encBool) Option.isNone bitNext_inSpace
  have bit := budget_finite (encC := encBool) (fun bit : Option Bool => bit.getD false) bitNext_inSpace
  have room := budget_natLt (budget_const (encB := encNat) 1 (.refl _)) roomNext_inSpace
  have positive := budget_natLt (budget_const (encB := encNat) 0 (.refl _)) boundNext_inSpace
  have prefixBranch := budget_ite noBit reject_inSpace
    (budget_ite bit (budget_ite positive start_inSpace reject_inSpace)
      (budget_ite room zero_inSpace reject_inSpace))
  have payloadBranch := budget_ite noBit reject_inSpace payload_inSpace
  have phase0 := budget_finite (encC := encBool)
    (fun phase : Fin 4 => decide (phase = 0)) phaseNext_inSpace
  have phase1 := budget_finite (encC := encBool)
    (fun phase : Fin 4 => decide (phase = 1)) phaseNext_inSpace
  apply (budget_ite phase0 prefixBranch
    (budget_ite phase1 payloadBranch stateNext_inSpace)).of_enc_eq
  rintro ⟨bound, state, bit⟩
  cases bit with
  | none => simp [next]
  | some bit =>
    by_cases pref : state.phase = 0
    · cases bit <;> simp [next, pref, show 1 < state.room ↔ 2 ≤ state.room by omega]
    · by_cases payload : state.phase = 1
      · cases parsed : appendValue bound state.accumulator bit <;>
          simp [next, payload, parsed]
      · simp [next, pref, payload]

theorem encState_length (state : State) :
    (encState state).length = 2 * (encNat state.phase.val).length +
      2 * (encNat state.cursor).length + 2 * (encNat state.zeros).length +
      2 * (encNat state.remaining).length + 2 * (encNat state.accumulator).length +
      (encNat state.room).length + 5 := by
  change (encPair encPhase
    (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
    (state.phase, state.cursor, state.zeros, state.remaining, state.accumulator, state.room)).length = _
  simp only [length_encPair]
  change 2 * (encNat state.phase.val).length + 1 +
    (2 * (encNat state.cursor).length + 1 + (2 * (encNat state.zeros).length + 1 +
      (2 * (encNat state.remaining).length + 1 +
        (2 * (encNat state.accumulator).length + 1 + (encNat state.room).length)))) = _
  omega

theorem encPhase_length_le (phase : Fin 4) : (encPhase phase).length ≤ 2 := by
  fin_cases phase <;> decide

/-- The cursor may have a different binary width from the bounded payload
registers, so their contributions remain separate. -/
theorem encState_length_le (state : State) (B C : ℕ)
    (cursor : (encNat state.cursor).length ≤ C)
    (zeros : (encNat state.zeros).length ≤ B)
    (remaining : (encNat state.remaining).length ≤ B)
    (accumulator : (encNat state.accumulator).length ≤ B)
    (room : (encNat state.room).length ≤ B) :
    (encState state).length ≤ 2 * C + 7 * B + 9 := by
  have phase := encPhase_length_le state.phase
  change (encNat state.phase.val).length ≤ 2 at phase
  rw [encState_length]
  omega

theorem encState_length_of_values (state : State) (bound cursorBound : ℕ)
    (cursor : state.cursor ≤ cursorBound) (zeros : state.zeros ≤ bound)
    (remaining : state.remaining ≤ bound) (accumulator : state.accumulator ≤ bound)
    (room : state.room ≤ bound) :
    (encState state).length ≤
      9 * ((bound.log2 + 1) + (cursorBound.log2 + 1)) := by
  have bounded := encState_length_le state (bound.log2 + 1) (cursorBound.log2 + 1)
    (length_encNat_le_log2 cursor) (length_encNat_le_log2 zeros)
    (length_encNat_le_log2 remaining) (length_encNat_le_log2 accumulator)
    (length_encNat_le_log2 room)
  omega

theorem encInitial_length (bound start : ℕ) :
    (encInitial (bound, start)).length =
      2 * (encNat bound).length + (encNat start).length + 1 := by
  simp only [encInitial, length_encPair]
  omega

theorem encNext_length (bound : ℕ) (state : State) (bit : Option Bool) :
    (encNext (bound, state, bit)).length = 2 * (encNat bound).length +
      2 * (encState state).length + (encOption encBool bit).length + 2 := by
  simp only [encNext, length_encPair]
  omega

private theorem encBit_length_le (bit : Option Bool) :
    (encOption encBool bit).length ≤ 2 := by
  cases bit with
  | none => decide
  | some bit => cases bit <;> decide

/-- Invalid, excessive, and truncated candidates obey the same logarithmic
bound; an out-of-range starting cursor is accounted for by the maximum. -/
theorem run_encoding_length (bound : ℕ) (input : List Bool) (start fuel : ℕ) :
    (encState (run bound input start fuel)).length ≤
      9 * ((bound.log2 + 1) + ((max start input.length).log2 + 1)) := by
  obtain ⟨_, cursor, zeros, remaining, accumulator, room⟩ :=
    run_register_bounds bound input start fuel
  exact encState_length_of_values _ bound (max start input.length) cursor
    (zeros.trans (Nat.log2_le_self bound)) (remaining.trans (Nat.log2_le_self bound))
    accumulator room

/-- The complete transition argument is bounded, including its runtime bound
and query response. The immutable source bits are not included in this word. -/
theorem run_next_encoding_length (bound : ℕ) (input : List Bool) (start fuel : ℕ)
    (bit : Option Bool) :
    (encNext (bound, run bound input start fuel, bit)).length ≤
      27 * ((bound.log2 + 1) + ((max start input.length).log2 + 1)) := by
  have state := run_encoding_length bound input start fuel
  have boundBits := length_encNat_le_log2 (Nat.le_refl bound)
  have bitBits := encBit_length_le bit
  rw [encNext_length]
  omega

end NtimeDspace.BoundedGammaPayloadSpace
