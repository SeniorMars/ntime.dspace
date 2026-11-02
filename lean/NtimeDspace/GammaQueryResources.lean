import NtimeDspace.GammaQueryMachine
import NtimeDspace.ComplexityReuse
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
Concrete binary encoding and global linear-space callback certificates for the
gamma-prefix query parser. Each certificate constructs a finite-control CSLib
machine through the imported arithmetic and encoding calculus. No callback
certificate or unencoded input accessor is assumed.
-/

namespace NtimeDspace.GammaQueryResources

open Turing Turing.MultiTapeTM ComputableInSpace GammaQueryMachine

abbrev Data := Fin 4 × ℕ × ℕ × ℕ × ℕ

/-- The phase encoding uses its explicit numeric tag. -/
def encPhase : Fin 4 ↪ List Bool := Fin.valEmbedding.trans encNat

def toData : State ↪ Data :=
  ⟨fun s => (s.phase, s.cursor, s.zeros, s.remaining, s.accumulator), by
    intro a b h
    cases a
    cases b
    simpa only [Prod.mk.injEq, State.mk.injEq] using h⟩

def encData : Data ↪ List Bool :=
  encPair encPhase (encPair encNat (encPair encNat (encPair encNat encNat)))

def encState : State ↪ List Bool := toData.trans encData

abbrev ReadState := State × Option Bool

def encRead : ReadState ↪ List Bool := encPair encState (encOption encBool)

theorem encState_length (s : State) :
    (encState s).length = 2 * (encNat s.phase.val).length +
      2 * (encNat s.cursor).length + 2 * (encNat s.zeros).length +
      2 * (encNat s.remaining).length + (encNat s.accumulator).length + 4 := by
  change (encPair encPhase (encPair encNat (encPair encNat (encPair encNat encNat)))
    (s.phase, s.cursor, s.zeros, s.remaining, s.accumulator)).length = _
  simp only [length_encPair]
  change 2 * (encNat s.phase.val).length + 1 +
    (2 * (encNat s.cursor).length + 1 + (2 * (encNat s.zeros).length + 1 +
      (2 * (encNat s.remaining).length + 1 + (encNat s.accumulator).length))) = _
  omega

theorem encPhase_length_le (phase : Fin 4) : (encPhase phase).length ≤ 2 := by
  fin_cases phase <;> decide

/-- Exact per-register binary widths give a linear bound for the complete state. -/
theorem encState_length_le (s : State) (B : ℕ)
    (cursor : (encNat s.cursor).length ≤ B) (zeros : (encNat s.zeros).length ≤ B)
    (remaining : (encNat s.remaining).length ≤ B)
    (accumulator : (encNat s.accumulator).length ≤ B) :
    (encState s).length ≤ 7 * B + 8 := by
  have phase := encPhase_length_le s.phase
  change (encNat s.phase.val).length ≤ 2 at phase
  rw [encState_length]
  omega

/-- Numeric bounds on all four registers give logarithmic encoded space. -/
theorem encState_length_of_values (s : State) (B : ℕ)
    (cursor : s.cursor ≤ B) (zeros : s.zeros ≤ B)
    (remaining : s.remaining ≤ B) (accumulator : s.accumulator ≤ B) :
    (encState s).length ≤ 15 * (B.log2 + 1) := by
  have h := encState_length_le s (B.log2 + 1)
    (length_encNat_le_log2 cursor) (length_encNat_le_log2 zeros)
    (length_encNat_le_log2 remaining) (length_encNat_le_log2 accumulator)
  omega

private theorem state_inSpace :
    ComputableInSpace (fun s : State => s) encState encState
      (fun s => (encState s).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

theorem phase_inSpace :
    ComputableInSpace State.phase encState encPhase (fun s => (encState s).length) := by
  exact (fst encPhase (encPair encNat (encPair encNat (encPair encNat encNat)))).of_encIn_eq
    toData (by intro s; rfl)

private theorem registers_inSpace :
    ComputableInSpace (fun s : State => (s.cursor, s.zeros, s.remaining, s.accumulator))
      encState (encPair encNat (encPair encNat (encPair encNat encNat)))
      (fun s => (encState s).length) := by
  exact (snd encPhase (encPair encNat (encPair encNat (encPair encNat encNat)))).of_encIn_eq
    toData (by intro s; rfl)

theorem cursor_inSpace :
    ComputableInSpace State.cursor encState encNat (fun s => (encState s).length) :=
  fst' registers_inSpace

theorem zeros_inSpace :
    ComputableInSpace State.zeros encState encNat (fun s => (encState s).length) :=
  fst' (snd' registers_inSpace)

theorem remaining_inSpace :
    ComputableInSpace State.remaining encState encNat (fun s => (encState s).length) :=
  fst' (snd' (snd' registers_inSpace))

theorem accumulator_inSpace :
    ComputableInSpace State.accumulator encState encNat (fun s => (encState s).length) :=
  snd' (snd' (snd' registers_inSpace))

private theorem stateRead_inSpace :
    ComputableInSpace Prod.fst encRead encState (fun s => (encRead s).length) :=
  fst _ _

private theorem bitRead_inSpace :
    ComputableInSpace Prod.snd encRead (encOption encBool) (fun s => (encRead s).length) :=
  snd _ _

private theorem phaseRead_inSpace :
    ComputableInSpace (fun s : ReadState => s.1.phase) encRead encPhase
      (fun s => (encRead s).length) := budget_comp_linear phase_inSpace stateRead_inSpace

private theorem cursorRead_inSpace :
    ComputableInSpace (fun s : ReadState => s.1.cursor) encRead encNat
      (fun s => (encRead s).length) := budget_comp_linear cursor_inSpace stateRead_inSpace

private theorem zerosRead_inSpace :
    ComputableInSpace (fun s : ReadState => s.1.zeros) encRead encNat
      (fun s => (encRead s).length) := budget_comp_linear zeros_inSpace stateRead_inSpace

private theorem remainingRead_inSpace :
    ComputableInSpace (fun s : ReadState => s.1.remaining) encRead encNat
      (fun s => (encRead s).length) := budget_comp_linear remaining_inSpace stateRead_inSpace

private theorem accumulatorRead_inSpace :
    ComputableInSpace (fun s : ReadState => s.1.accumulator) encRead encNat
      (fun s => (encRead s).length) := budget_comp_linear accumulator_inSpace stateRead_inSpace

private theorem assemble {phase : ReadState → Fin 4} {cursor zeros remaining accumulator : ReadState → ℕ}
    (hp : ComputableInSpace phase encRead encPhase (fun s => (encRead s).length))
    (hc : ComputableInSpace cursor encRead encNat (fun s => (encRead s).length))
    (hz : ComputableInSpace zeros encRead encNat (fun s => (encRead s).length))
    (hr : ComputableInSpace remaining encRead encNat (fun s => (encRead s).length))
    (ha : ComputableInSpace accumulator encRead encNat (fun s => (encRead s).length)) :
    ComputableInSpace (fun s => (⟨phase s, cursor s, zeros s, remaining s, accumulator s⟩ : State))
      encRead encState (fun s => (encRead s).length) :=
  (budget_prod hp (budget_prod hc (budget_prod hz (budget_prod hr ha)))).of_enc_eq
    (fun _ => rfl)

private theorem reject_inSpace :
    ComputableInSpace (fun s : ReadState => ({s.1 with phase := 3} : State))
      encRead encState (fun s => (encRead s).length) :=
  assemble (budget_const 3 (.refl _)) cursorRead_inSpace zerosRead_inSpace
    remainingRead_inSpace accumulatorRead_inSpace

private theorem zero_inSpace :
    ComputableInSpace (fun s : ReadState =>
      ({s.1 with cursor := s.1.cursor + 1, zeros := s.1.zeros + 1} : State))
      encRead encState (fun s => (encRead s).length) :=
  assemble phaseRead_inSpace (budget_natSucc cursorRead_inSpace)
    (budget_natSucc zerosRead_inSpace) remainingRead_inSpace accumulatorRead_inSpace

private theorem start_inSpace :
    ComputableInSpace (fun s : ReadState =>
      (⟨if s.1.zeros = 0 then 2 else 1, s.1.cursor + 1, s.1.zeros, s.1.zeros, 1⟩ : State))
      encRead encState (fun s => (encRead s).length) := by
  have phase := budget_ite (budget_natIsZero zerosRead_inSpace)
    (budget_const (encB := encPhase) 2 (.refl _)) (budget_const 1 (.refl _))
  apply (assemble phase (budget_natSucc cursorRead_inSpace) zerosRead_inSpace
    zerosRead_inSpace (budget_const 1 (.refl _))).of_enc_eq
  intro s
  simp only [decide_eq_true_eq]

private theorem payload_inSpace :
    ComputableInSpace (fun s : ReadState =>
      (⟨if s.1.remaining ≤ 1 then 2 else 1, s.1.cursor + 1, s.1.zeros,
        s.1.remaining - 1, 2 * s.1.accumulator + (if s.2.getD false then 1 else 0)⟩ : State))
      encRead encState (fun s => (encRead s).length) := by
  have phase := budget_ite
    (budget_natLt remainingRead_inSpace (budget_const (encB := encNat) 2 (.refl _)))
    (budget_const (encB := encPhase) 2 (.refl _)) (budget_const 1 (.refl _))
  have bit := budget_finite (encC := encNat)
    (fun b : Option Bool => if b.getD false then 1 else 0) bitRead_inSpace
  have accumulator := budget_natAdd
    (budget_natMul (budget_const 2 (.refl _)) accumulatorRead_inSpace) bit
  apply (assemble phase (budget_natSucc cursorRead_inSpace) zerosRead_inSpace
    (budget_natPred remainingRead_inSpace) accumulator).of_enc_eq
  intro s
  simp only [decide_eq_true_eq, show s.1.remaining < 2 ↔ s.1.remaining ≤ 1 by omega]

/-- The query is the explicitly stored input cursor. -/
theorem query_inSpace :
    ComputableInSpace machine.query encState encNat (fun s => (encState s).length) :=
  cursor_inSpace

/-- Every transition is globally linear in the binary state encoding, including
unreachable or malformed phase/register combinations. -/
theorem next_inSpace :
    ComputableInSpace machine.next encRead encState (fun s => (encRead s).length) := by
  have noBit := budget_finite (encC := encBool) Option.isNone bitRead_inSpace
  have bit := budget_finite (encC := encBool) (fun b : Option Bool => b.getD false) bitRead_inSpace
  have prefixBranch := budget_ite noBit reject_inSpace (budget_ite bit start_inSpace zero_inSpace)
  have payload := budget_ite noBit reject_inSpace payload_inSpace
  have phase0 := budget_finite (encC := encBool) (fun p : Fin 4 => decide (p = 0)) phaseRead_inSpace
  have phase1 := budget_finite (encC := encBool) (fun p : Fin 4 => decide (p = 1)) phaseRead_inSpace
  apply (budget_ite phase0 prefixBranch (budget_ite phase1 payload stateRead_inSpace)).of_enc_eq
  intro s
  rcases s with ⟨s, bit⟩
  cases bit with
  | none => simp [machine, GammaQueryMachine.next]
  | some bit => cases bit <;> simp [machine, GammaQueryMachine.next, BoundedSupportParser.bitValue]

theorem emit_inSpace :
    ComputableInSpace machine.emit encRead encBits (fun s => (encRead s).length) :=
  budget_const [] (.refl _)

theorem halted_inSpace :
    ComputableInSpace machine.halted encState encBool (fun s => (encState s).length) :=
  budget_finite (fun p : Fin 4 => decide (2 ≤ p.val)) phase_inSpace

theorem finish_inSpace :
    ComputableInSpace machine.finish encState encBits (fun s => (encState s).length) :=
  budget_finite (fun p : Fin 4 => [decide (p = 2)]) phase_inSpace

/-- All run states, including the fixed halted state, fit in a linear number
of bits in the original input length. The input itself is not part of the state. -/
theorem run_encoding_length (input : List Bool) (time : ℕ) :
    (encState (machine.run input time)).length ≤ 15 * (input.length + 2) := by
  have bounds := run_registerBounds input time
  rcases bounds with ⟨cursor, zeros, remaining, accumulator⟩
  have hcursor : (encNat (machine.run input time).cursor).length ≤ input.length + 1 :=
    (length_encNat_le_self _).trans (by omega)
  have hzeros : (encNat (machine.run input time).zeros).length ≤ input.length + 1 :=
    (length_encNat_le_self _).trans (by omega)
  have hremaining : (encNat (machine.run input time).remaining).length ≤ input.length + 1 :=
    (length_encNat_le_self _).trans (by omega)
  have haccumulator : (encNat (machine.run input time).accumulator).length ≤ input.length + 1 := by
    rw [length_encNat_eq_size]
    exact Nat.size_le.mpr (accumulator.trans_le
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have h := encState_length_le _ _ hcursor hzeros hremaining haccumulator
  omega

/-- Concrete gamma-prefix validity on arbitrary binary inputs is computed by
one finite-control CSLib machine, with visited work space linear in the input
length and simultaneous exponential time. All callback certificates above
are discharged; this theorem makes no assumption about a parser implementation. -/
theorem valid_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace valid encBits encBool
      (fun input => 2 ^ (C * (input.length + 2)))
      (fun input => C * (input.length + 2)) := by
  exact ComplexityReuse.query_simultaneous_bounds (enc := encBits) (encOut := encBool)
    (f := valid) machine
    query_inSpace next_inSpace emit_inSpace halted_inSpace finish_inSpace
    stopTime stopTime_halts before_stopTime
    (fun input => (output_correct input).symm)
    (fun input => input.length + 2)
    (fun input => by simpa only [encBits_apply] using
      (show input.length.log2 + 1 ≤ input.length + 2 by
        have := Nat.log2_le_self input.length
        omega))
    ⟨15, fun input time _ => run_encoding_length input time⟩

end NtimeDspace.GammaQueryResources
