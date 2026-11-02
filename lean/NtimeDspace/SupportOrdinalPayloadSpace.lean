import NtimeDspace.SupportOrdinalPayload
import NtimeDspace.BoundedSupportPayloadSpace

/-!
Explicit binary serialization and global callback certificates for a complete
support scan retaining one queried position. The universe bound, capacity, and
queried positive index are encoded runtime arguments. The callbacks cover every
raw state; reachable-register bounds are separate theorems. Neither a support
list nor a source suffix is stored in the executing state.
-/

namespace NtimeDspace.SupportOrdinalPayloadSpace

open Turing Turing.MultiTapeTM ComputableInSpace SupportOrdinalPayload

abbrev StateData := BoundedSupportPayload.State × ℕ

def stateData : State ↪ StateData :=
  ⟨fun state => (state.core, state.ordinal), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, State.mk.injEq] using same⟩

def encStateData : StateData ↪ List Bool :=
  encPair BoundedSupportPayloadSpace.encState encNat

def encState : State ↪ List Bool := stateData.trans encStateData

abbrev NextInput := ℕ × ℕ × ℕ × State × Option Bool

def encNext : NextInput ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encState (encOption encBool))))

abbrev encOutput := encOption (encPair encNat encNat)

private theorem assemble {α : Type} {encIn : α ↪ List Bool} {B : α → ℕ}
    {core : α → BoundedSupportPayload.State} {ordinal : α → ℕ}
    (hc : ComputableInSpace core encIn BoundedSupportPayloadSpace.encState B)
    (ho : ComputableInSpace ordinal encIn encNat B) :
    ComputableInSpace (fun a => (⟨core a, ordinal a⟩ : State)) encIn encState B :=
  (budget_prod hc ho).of_enc_eq fun _ => rfl

private theorem stateData_inSpace :
    ComputableInSpace stateData encState encStateData (fun state => (encState state).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

theorem core_inSpace :
    ComputableInSpace State.core encState BoundedSupportPayloadSpace.encState
      (fun state => (encState state).length) := fst' stateData_inSpace

theorem ordinal_inSpace :
    ComputableInSpace State.ordinal encState encNat (fun state => (encState state).length) :=
  snd' stateData_inSpace

theorem initial_inSpace :
    ComputableInSpace initial encNat encState (fun bound => (encNat bound).length) :=
  assemble BoundedSupportPayloadSpace.initial_inSpace (budget_const 0 (.refl _))

theorem query_inSpace :
    ComputableInSpace SupportOrdinalPayload.query encState encNat
      (fun state => (encState state).length) := by
  apply (budget_comp_linear BoundedSupportPayloadSpace.query_inSpace core_inSpace).of_enc_eq
  intro state
  rfl

theorem halted_inSpace :
    ComputableInSpace halted encState encBool (fun state => (encState state).length) := by
  apply (budget_comp_linear BoundedSupportPayloadSpace.halted_inSpace core_inSpace).of_enc_eq
  intro state
  rfl

theorem output_inSpace :
    ComputableInSpace output encState encOutput (fun state => (encState state).length) := by
  have phase := budget_comp_linear BoundedSupportPayloadSpace.phase_inSpace core_inSpace
  have rank := budget_comp_linear BoundedSupportPayloadSpace.rank_inSpace core_inSpace
  have accepted := budget_finite (encC := encBool)
    (fun phase : Fin 4 => decide (phase = 2)) phase
  have present := budget_comp_linear
    (of_inO (ComputableInDegree.optionSome
      (enc₁ := encPair encNat encNat) (enc := encOutput)).inO_one)
    (budget_prod rank ordinal_inSpace)
  apply (budget_ite accepted present
    (budget_const (encB := encOutput) none (.refl _))).of_enc_eq
  intro state
  simp only [output, BoundedSupportPayload.output, decide_eq_true_eq]
  split_ifs <;> rfl

/-- The target index is supplied in the encoded transition argument, together
with both parser bounds and the queried input bit. -/
theorem next_inSpace :
    ComputableInSpace (fun input : NextInput => next input.1 input.2.1 input.2.2.1 input.2.2.2)
      encNext encState (fun input => (encNext input).length) := by
  have bound : ComputableInSpace (fun input : NextInput => input.1) encNext encNat
      (fun input => (encNext input).length) := fst _ _
  have rest : ComputableInSpace (fun input : NextInput => input.2) encNext
      (encPair encNat (encPair encNat (encPair encState (encOption encBool))))
      (fun input => (encNext input).length) := snd _ _
  have capacity := fst' rest
  have target := fst' (snd' rest)
  have state := fst' (snd' (snd' rest))
  have bit := snd' (snd' (snd' rest))
  have core := budget_comp_linear core_inSpace state
  have ordinal := budget_comp_linear ordinal_inSpace state
  have oldRank := budget_comp_linear BoundedSupportPayloadSpace.rank_inSpace core
  have advanced := budget_comp_linear BoundedSupportPayloadSpace.next_inSpace
    (budget_prod bound (budget_prod capacity (budget_prod core bit)))
  have newRank := budget_comp_linear BoundedSupportPayloadSpace.rank_inSpace advanced
  have cumulative := budget_comp_linear BoundedSupportPayloadSpace.cumulative_inSpace advanced
  have increased := budget_natLt oldRank newRank
  have hit := budget_natEq cumulative target
  have updated := budget_ite increased (budget_ite hit newRank ordinal) ordinal
  apply (assemble advanced updated).of_enc_eq
  rintro ⟨bound, capacity, target, state, bit⟩
  by_cases increased : state.core.rank < (BoundedSupportPayload.next bound capacity (state.core, bit)).rank
  · by_cases hit : (BoundedSupportPayload.next bound capacity (state.core, bit)).cumulative = target
    · simp [next, increased, hit]
    · simp [next, increased, hit]
  · simp [next, increased]

theorem encState_length (state : State) :
    (encState state).length =
      2 * (BoundedSupportPayloadSpace.encState state.core).length +
        (encNat state.ordinal).length + 1 := by
  change (encPair BoundedSupportPayloadSpace.encState encNat
    (state.core, state.ordinal)).length = _
  simp only [length_encPair]
  omega

theorem encNext_length (bound capacity target : ℕ) (state : State) (bit : Option Bool) :
    (encNext (bound, capacity, target, state, bit)).length =
      2 * (encNat bound).length + 2 * (encNat capacity).length +
        2 * (encNat target).length + 2 * (encState state).length +
          (encOption encBool bit).length + 4 := by
  simp only [encNext, length_encPair]
  omega

/-- The retained ordinal is charged at the capacity's binary width. The
query value is an argument of the transition, not a hidden state constant. -/
theorem encState_length_of_bounds (state : State) (bound capacity cursorBound : ℕ)
    (coreBound : (BoundedSupportPayloadSpace.encState state.core).length ≤
      20 * ((bound.log2 + 1) + (capacity.log2 + 1) + (cursorBound.log2 + 1)))
    (ordinalBound : state.ordinal ≤ capacity) :
    (encState state).length ≤
      50 * ((bound.log2 + 1) + (capacity.log2 + 1) + (cursorBound.log2 + 1)) := by
  have ordinalBits := length_encNat_le_log2 ordinalBound
  rw [encState_length]
  omega

private theorem encBit_length_le (bit : Option Bool) :
    (encOption encBool bit).length ≤ 2 := by
  cases bit with
  | none => decide
  | some bit => cases bit <;> decide

/-- Complete callback arguments include the queried positive index as well as
the validation parameters and response bit. -/
theorem encNext_length_of_state_bound (bound capacity target cursorBound : ℕ)
    (state : State) (bit : Option Bool)
    (stateBound : (encState state).length ≤
      50 * ((bound.log2 + 1) + (capacity.log2 + 1) + (cursorBound.log2 + 1))) :
    (encNext (bound, capacity, target, state, bit)).length ≤
      104 * ((bound.log2 + 1) + (capacity.log2 + 1) +
        (target.log2 + 1) + (cursorBound.log2 + 1)) := by
  have boundBits := length_encNat_le_log2 (Nat.le_refl bound)
  have capacityBits := length_encNat_le_log2 (Nat.le_refl capacity)
  have targetBits := length_encNat_le_log2 (Nat.le_refl target)
  have bitBits := encBit_length_le bit
  rw [encNext_length]
  omega

/-- Every prefix retains only the bounded support-parser state and one ordinal.
This estimate is independent of the queried value, whose width is charged in
the complete transition argument and in the enclosing query-machine header. -/
theorem run_encoding_length (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ) :
    (encState (run bound capacity target input fuel)).length ≤
      50 * ((bound.log2 + 1) + (capacity.log2 + 1) + (input.length.log2 + 1)) := by
  apply encState_length_of_bounds _ bound capacity input.length
  · rw [run_core]
    exact BoundedSupportPayloadSpace.run_encoding_length bound capacity input fuel
  · exact run_ordinal_le_capacity bound capacity target input fuel

theorem run_next_encoding_length (bound capacity target : ℕ) (input : List Bool) (fuel : ℕ)
    (bit : Option Bool) :
    (encNext (bound, capacity, target, run bound capacity target input fuel, bit)).length ≤
      104 * ((bound.log2 + 1) + (capacity.log2 + 1) +
        (target.log2 + 1) + (input.length.log2 + 1)) :=
  encNext_length_of_state_bound bound capacity target input.length _ bit
    (run_encoding_length bound capacity target input fuel)

end NtimeDspace.SupportOrdinalPayloadSpace
