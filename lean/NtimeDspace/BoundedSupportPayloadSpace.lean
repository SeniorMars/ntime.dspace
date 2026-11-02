import NtimeDspace.BoundedSupportPayload
import NtimeDspace.BoundedGammaPayloadSpace

/-!
Explicit binary state encoding and global machine certificates for the
cursor-only support parser's scalar callbacks. Both universe bound and support
capacity are runtime fields of the complete transition and commit arguments.
The certificates cover arbitrary raw registers, including malformed parser
states. Reachable-register size bounds do not replace these global premises.
Input-query/bootstrap compilation is a separate layer; no suffix or decoded
support list is stored here.
-/

namespace NtimeDspace.BoundedSupportPayloadSpace

open Turing Turing.MultiTapeTM ComputableInSpace BoundedSupportPayload

abbrev encPhase := BoundedGammaPayloadSpace.encPhase
abbrev StateData := Fin 4 × ℕ × ℕ × BoundedGammaPayload.State

def stateData : State ↪ StateData :=
  ⟨fun state => (state.phase, state.cumulative, state.rank, state.parser), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, State.mk.injEq] using same⟩

def encStateData : StateData ↪ List Bool :=
  encPair encPhase (encPair encNat (encPair encNat BoundedGammaPayloadSpace.encState))

def encState : State ↪ List Bool := stateData.trans encStateData

abbrev CommitInput := ℕ × ℕ × State × BoundedGammaPayload.State
def encCommit : CommitInput ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encState BoundedGammaPayloadSpace.encState))

abbrev NextInput := ℕ × ℕ × State × Option Bool
def encNext : NextInput ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encState (encOption encBool)))

abbrev encOutput := encOption encNat

private theorem assemble {α : Type} {encIn : α ↪ List Bool} {B : α → ℕ}
    {phase : α → Fin 4} {cumulative rank : α → ℕ} {parser : α → BoundedGammaPayload.State}
    (hp : ComputableInSpace phase encIn encPhase B)
    (hc : ComputableInSpace cumulative encIn encNat B)
    (hr : ComputableInSpace rank encIn encNat B)
    (hg : ComputableInSpace parser encIn BoundedGammaPayloadSpace.encState B) :
    ComputableInSpace (fun a => (⟨phase a, cumulative a, rank a, parser a⟩ : State))
      encIn encState B :=
  (budget_prod hp (budget_prod hc (budget_prod hr hg))).of_enc_eq fun _ => rfl

private theorem stateData_inSpace :
    ComputableInSpace stateData encState encStateData (fun state => (encState state).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

theorem phase_inSpace :
    ComputableInSpace State.phase encState encPhase (fun state => (encState state).length) :=
  fst' stateData_inSpace

theorem cumulative_inSpace :
    ComputableInSpace State.cumulative encState encNat (fun state => (encState state).length) :=
  fst' (snd' stateData_inSpace)

theorem rank_inSpace :
    ComputableInSpace State.rank encState encNat (fun state => (encState state).length) :=
  fst' (snd' (snd' stateData_inSpace))

theorem parser_inSpace :
    ComputableInSpace State.parser encState BoundedGammaPayloadSpace.encState
      (fun state => (encState state).length) := snd' (snd' (snd' stateData_inSpace))

theorem initial_inSpace :
    ComputableInSpace initial encNat encState (fun bound => (encNat bound).length) := by
  have identity : ComputableInSpace (fun bound : ℕ => bound) encNat encNat
      (fun bound => (encNat bound).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  have parser := budget_comp_linear BoundedGammaPayloadSpace.initial_inSpace
    (budget_prod identity (budget_const 0 (.refl _)))
  exact assemble (budget_const 0 (.refl _)) (budget_const 0 (.refl _))
    (budget_const 0 (.refl _)) parser

theorem query_inSpace :
    ComputableInSpace BoundedSupportPayload.query encState encNat (fun state => (encState state).length) := by
  apply (budget_comp_linear BoundedGammaPayloadSpace.query_inSpace parser_inSpace).of_enc_eq
  intro state
  rfl

theorem halted_inSpace :
    ComputableInSpace halted encState encBool (fun state => (encState state).length) :=
  budget_finite (fun phase : Fin 4 => decide (2 ≤ phase.val)) phase_inSpace

theorem output_inSpace :
    ComputableInSpace output encState encOutput (fun state => (encState state).length) := by
  have accepted := budget_finite (encC := encBool)
    (fun phase : Fin 4 => decide (phase = 2)) phase_inSpace
  apply (budget_ite accepted (budget_optionSome rank_inSpace)
    (budget_const (encB := encOutput) none (.refl _))).of_enc_eq
  intro state
  simp only [output, decide_eq_true_eq]

/-- Positive-gap, cumulative-index, and capacity guards precede the committed
updates. Every parameter, including the candidate gamma state, is encoded. -/
theorem commit_inSpace :
    ComputableInSpace (fun input : CommitInput => commit input.1 input.2.1 input.2.2.1 input.2.2.2)
      encCommit encState (fun input => (encCommit input).length) := by
  have bound : ComputableInSpace (fun input : CommitInput => input.1) encCommit encNat
      (fun input => (encCommit input).length) := fst _ _
  have rest : ComputableInSpace (fun input : CommitInput => input.2) encCommit
      (encPair encNat (encPair encState BoundedGammaPayloadSpace.encState))
      (fun input => (encCommit input).length) := snd _ _
  have capacity := fst' rest
  have state := fst' (snd' rest)
  have parsed := snd' (snd' rest)
  have cumulative := budget_comp_linear cumulative_inSpace state
  have rank := budget_comp_linear rank_inSpace state
  have gap := budget_comp_linear BoundedGammaPayloadSpace.accumulator_inSpace parsed
  have phase := budget_comp_linear BoundedGammaPayloadSpace.phase_inSpace parsed
  have accepted := budget_finite (encC := encBool) (fun phase : Fin 4 => decide (phase = 2)) phase
  have rejected := budget_finite (encC := encBool) (fun phase : Fin 4 => decide (phase = 3)) phase
  have positive := budget_natLt (budget_const (encB := encNat) 0 (.refl _)) gap
  have fits := budget_natLt gap (budget_natSucc (budget_natSub bound cumulative))
  have available := budget_natLt rank capacity
  have committed := assemble (budget_const (encB := encPhase) 0 (.refl _))
    (budget_natAdd cumulative gap) (budget_natSucc rank) parsed
  have failed := assemble (budget_const (encB := encPhase) 3 (.refl _)) cumulative rank parsed
  have pending := assemble (budget_const (encB := encPhase) 1 (.refl _)) cumulative rank parsed
  apply (budget_ite accepted
    (budget_ite positive (budget_ite fits (budget_ite available committed failed) failed) failed)
    (budget_ite rejected failed pending)).of_enc_eq
  intro input
  simp only [commit, decide_eq_true_eq, Nat.lt_succ_iff]

/-- One global transition machine, with universe bound and capacity present
in every encoded call. The gamma submachine is reused through its certificate. -/
theorem next_inSpace :
    ComputableInSpace (fun input : NextInput => next input.1 input.2.1 input.2.2)
      encNext encState (fun input => (encNext input).length) := by
  have bound : ComputableInSpace (fun input : NextInput => input.1) encNext encNat
      (fun input => (encNext input).length) := fst _ _
  have rest : ComputableInSpace (fun input : NextInput => input.2) encNext
      (encPair encNat (encPair encState (encOption encBool)))
      (fun input => (encNext input).length) := snd _ _
  have capacity := fst' rest
  have state := fst' (snd' rest)
  have bit := snd' (snd' rest)
  have phase := budget_comp_linear phase_inSpace state
  have cumulative := budget_comp_linear cumulative_inSpace state
  have rank := budget_comp_linear rank_inSpace state
  have parser := budget_comp_linear parser_inSpace state
  have cursor := budget_comp_linear BoundedGammaPayloadSpace.query_inSpace parser
  have reset := budget_comp_linear BoundedGammaPayloadSpace.initial_inSpace (budget_prod bound cursor)
  have started := budget_comp_linear BoundedGammaPayloadSpace.next_inSpace
    (budget_prod bound (budget_prod reset bit))
  have advanced := budget_comp_linear BoundedGammaPayloadSpace.next_inSpace
    (budget_prod bound (budget_prod parser bit))
  have commitStarted := budget_comp_linear commit_inSpace
    (budget_prod bound (budget_prod capacity (budget_prod state started)))
  have commitAdvanced := budget_comp_linear commit_inSpace
    (budget_prod bound (budget_prod capacity (budget_prod state advanced)))
  have accepted := assemble (budget_const (encB := encPhase) 2 (.refl _)) cumulative rank parser
  have rejected := assemble (budget_const (encB := encPhase) 3 (.refl _)) cumulative rank parser
  have noBit := budget_finite (encC := encBool) Option.isNone bit
  have available := budget_natLt rank capacity
  have phase0 := budget_finite (encC := encBool) (fun phase : Fin 4 => decide (phase = 0)) phase
  have phase1 := budget_finite (encC := encBool) (fun phase : Fin 4 => decide (phase = 1)) phase
  apply (budget_ite phase0 (budget_ite noBit accepted (budget_ite available commitStarted rejected))
    (budget_ite phase1 commitAdvanced state)).of_enc_eq
  rintro ⟨bound, capacity, state, bit⟩
  cases bit <;> simp [next]

theorem encState_length (state : State) :
    (encState state).length = 2 * (encNat state.phase.val).length +
      2 * (encNat state.cumulative).length + 2 * (encNat state.rank).length +
      (BoundedGammaPayloadSpace.encState state.parser).length + 3 := by
  change (encPair encPhase (encPair encNat (encPair encNat BoundedGammaPayloadSpace.encState))
    (state.phase, state.cumulative, state.rank, state.parser)).length = _
  simp only [length_encPair]
  change 2 * (encNat state.phase.val).length + 1 +
    (2 * (encNat state.cumulative).length + 1 +
      (2 * (encNat state.rank).length + 1 + (BoundedGammaPayloadSpace.encState state.parser).length)) = _
  omega

theorem encCommit_length (bound capacity : ℕ) (state : State) (parsed : BoundedGammaPayload.State) :
    (encCommit (bound, capacity, state, parsed)).length =
      2 * (encNat bound).length + 2 * (encNat capacity).length +
        2 * (encState state).length + (BoundedGammaPayloadSpace.encState parsed).length + 3 := by
  simp only [encCommit, length_encPair]
  omega

theorem encNext_length (bound capacity : ℕ) (state : State) (bit : Option Bool) :
    (encNext (bound, capacity, state, bit)).length =
      2 * (encNat bound).length + 2 * (encNat capacity).length +
        2 * (encState state).length + (encOption encBool bit).length + 3 := by
  simp only [encNext, length_encPair]
  omega

/-- A scalar value bound translates to an actual serialized-state bound. The
cursor width is separate from the universe and support-cardinality widths. -/
theorem encState_length_of_values (state : State) (bound capacity cursorBound : ℕ)
    (cumulative : state.cumulative ≤ bound) (rank : state.rank ≤ capacity)
    (cursor : state.parser.cursor ≤ cursorBound) (zeros : state.parser.zeros ≤ bound)
    (remaining : state.parser.remaining ≤ bound) (accumulator : state.parser.accumulator ≤ bound)
    (room : state.parser.room ≤ bound) :
    (encState state).length ≤
      20 * ((bound.log2 + 1) + (capacity.log2 + 1) + (cursorBound.log2 + 1)) := by
  have phase := BoundedGammaPayloadSpace.encPhase_length_le state.phase
  change (encNat state.phase.val).length ≤ 2 at phase
  have cumulativeBits := length_encNat_le_log2 cumulative
  have rankBits := length_encNat_le_log2 rank
  have parserBits := BoundedGammaPayloadSpace.encState_length_of_values state.parser
    bound cursorBound cursor zeros remaining accumulator room
  rw [encState_length]
  omega

private theorem encBit_length_le (bit : Option Bool) :
    (encOption encBool bit).length ≤ 2 := by
  cases bit with
  | none => decide
  | some bit => cases bit <;> decide

/-- Complete transition arguments retain the bound and capacity alongside the
state and response bit. The immutable input payload is not copied here. -/
theorem encNext_length_of_state_bound (bound capacity cursorBound : ℕ)
    (state : State) (bit : Option Bool)
    (stateBound : (encState state).length ≤
      20 * ((bound.log2 + 1) + (capacity.log2 + 1) + (cursorBound.log2 + 1))) :
    (encNext (bound, capacity, state, bit)).length ≤
      44 * ((bound.log2 + 1) + (capacity.log2 + 1) + (cursorBound.log2 + 1)) := by
  have boundBits := length_encNat_le_log2 (Nat.le_refl bound)
  have capacityBits := length_encNat_le_log2 (Nat.le_refl capacity)
  have bitBits := encBit_length_le bit
  rw [encNext_length]
  omega

/-- Every prefix, including invalid and already halted inputs, satisfies the
same bound on the actual serialized registers. No support list is retained. -/
theorem run_encoding_length (bound capacity : ℕ) (input : List Bool) (fuel : ℕ) :
    (encState (run bound capacity input fuel)).length ≤
      20 * ((bound.log2 + 1) + (capacity.log2 + 1) + (input.length.log2 + 1)) := by
  have wf := run_wellFormed bound capacity input fuel
  have zeros := wf.parser_wellFormed.zeros_le.trans (Nat.log2_le_self bound)
  exact encState_length_of_values _ bound capacity input.length wf.cumulative_le wf.rank_le
    (run_cursor_bound bound capacity input fuel) zeros
    (wf.parser_wellFormed.remaining_le.trans zeros)
    wf.parser_wellFormed.accumulator_le wf.parser_wellFormed.room_le

/-- The corresponding full callback argument bound counts both runtime
parameters and the optional input bit in addition to all stored registers. -/
theorem run_next_encoding_length (bound capacity : ℕ) (input : List Bool) (fuel : ℕ)
    (bit : Option Bool) :
    (encNext (bound, capacity, run bound capacity input fuel, bit)).length ≤
      44 * ((bound.log2 + 1) + (capacity.log2 + 1) + (input.length.log2 + 1)) :=
  encNext_length_of_state_bound bound capacity input.length _ bit
    (run_encoding_length bound capacity input fuel)

end NtimeDspace.BoundedSupportPayloadSpace
