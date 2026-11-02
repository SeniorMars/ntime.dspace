import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp

/-!
# Compiling a halting encoded-state loop

The initial state is computed from the input by its certified initializer.
Subsequent rounds operate only on that state. A live state is tagged with
`some`; the halting round produces the empty `none` encoding. The existing
`iterateWhile` machine returns the preceding live word, with space bounded by
the largest round and state word, independently of the number of rounds.

The halting time and maxima used below are proof witnesses, not machine
registers or computable-clock assumptions. Termination is required only for
the initialized inputs, while the step and halting callbacks have global
linear-space certificates. No input-dependent parameter is hidden in finite
control or in a fixed initial query-machine state.
-/

namespace NtimeDspace.HaltingStateCompiler

open Turing Turing.MultiTapeTM ComputableInSpace

def round {σ : Type} (fallback : σ) (step : σ → σ) (halted : σ → Bool)
    (value : Option σ) : Option σ :=
  if halted (value.getD fallback) then none else some (step (value.getD fallback))

theorem getD_inSpace {σ : Type} (encState : σ ↪ List Bool) (fallback : σ) :
    ComputableInSpace (fun value : Option σ => value.getD fallback)
      (encOption encState) encState (fun value => (encOption encState value).length) :=
  of_inO (ComputableInDegree.getD (enc₁ := encState) fallback).inO_one

theorem some_inSpace {σ : Type} (encState : σ ↪ List Bool) :
    ComputableInSpace (some : σ → Option σ) encState (encOption encState)
      (fun state => (encState state).length) :=
  of_inO (ComputableInDegree.optionSome (enc₁ := encState)).inO_one

theorem round_inSpace {σ : Type} (encState : σ ↪ List Bool)
    (fallback : σ) (step : σ → σ) (halted : σ → Bool)
    (stepSpace : ComputableInSpace step encState encState (fun state => (encState state).length))
    (haltSpace : ComputableInSpace halted encState encBool (fun state => (encState state).length)) :
    ComputableInSpace (round fallback step halted) (encOption encState) (encOption encState)
      (fun value => (encOption encState value).length) := by
  have decoded := getD_inSpace encState fallback
  have test := budget_comp_linear haltSpace decoded
  have advanced := budget_comp_linear stepSpace decoded
  have tagged := budget_comp_linear (some_inSpace encState) advanced
  exact budget_ite test (budget_const (encB := encOption encState) none (.refl _)) tagged

private def loopCoefficient (tapes callback coefficient : ℕ) : ℕ :=
  (2 * (tapes + 3) * (callback + 10) + 5) * coefficient +
    2 * (tapes + 3) * (callback + 6 * tapes + 44) + 4 * tapes + 26

private theorem loop_space_bound (tapes callback coefficient budget : ℕ) (positive : 1 ≤ budget) :
    2 * (tapes + 3) *
        (callback * (coefficient * budget + 1) + 10 * (coefficient * budget) + 6 * tapes + 44) +
      5 * (coefficient * budget) + 4 * tapes + 26 ≤
        loopCoefficient tapes callback coefficient * budget := by
  let constant := 2 * (tapes + 3) * (callback + 6 * tapes + 44) + 4 * tapes + 26
  have scale : constant ≤ constant * budget := Nat.le_mul_of_pos_right _ positive
  dsimp [constant, loopCoefficient] at *
  nlinarith

/-- Compile the terminal state, using a proof-only first-halting time. The
callback machines are global; termination and the prefix bound concern only
states reached from `initial input`. -/
theorem run_inSpace {α σ : Type} {encInput : α ↪ List Bool} {encState : σ ↪ List Bool}
    (fallback : σ) (initial : α → σ) (step : σ → σ) (halted : σ → Bool)
    (budget : α → ℕ)
    (initialSpace : ComputableInSpace initial encInput encState budget)
    (stepSpace : ComputableInSpace step encState encState (fun s => (encState s).length))
    (haltSpace : ComputableInSpace halted encState encBool (fun s => (encState s).length))
    (time : α → ℕ)
    (halts : ∀ a, halted (step^[time a] (initial a)) = true)
    (firstHalt : ∀ a n, n < time a → halted (step^[n] (initial a)) = false)
    (stateBound : ∃ C, ∀ a n, n ≤ time a →
      (encState (step^[n] (initial a))).length ≤ C * (budget a + 1)) :
    ComputableInSpace (fun a => step^[time a] (initial a)) encInput encState budget := by
  obtain ⟨C, bounded⟩ := stateBound
  have taggedInitial := budget_comp_linear (some_inSpace encState) initialSpace
  obtain ⟨TI, cI, ⟨kI, QI, finiteI, tmI, correctI⟩, _⟩ := taggedInitial.tidy
  obtain ⟨TR, cR, ⟨kR, QR, finiteR, tmR, correctR⟩, _⟩ :=
    (round_inSpace encState fallback step halted stepSpace haltSpace).tidy
  let d := C + 1
  let L : α → ℕ := fun a => d * (budget a + 1)
  let live : α → ℕ → Option σ := fun a n => some (step^[n] (initial a))
  let word : α → ℕ → List Bool := fun a n =>
    if n ≤ time a then encOption encState (live a n) else []
  have liveBound (a : α) (n : ℕ) (hn : n ≤ time a) :
      (encOption encState (live a n)).length ≤ L a := by
    have bound := bounded a n hn
    simp only [live, encOption_some, List.length_cons]
    dsimp [L, d]
    nlinarith
  let tMax : α → ℕ := fun a =>
    (Finset.Iic (time a)).sup (fun n => cR * (TR (live a n) + 1))
  have oneRound (a : α) (n : ℕ) (hn : n ≤ time a) :
      tmR.ComputesTidilyInTimeAndSpace (word a n) (word a (n + 1))
        (tMax a) (cR * (L a + 1)) := by
    have computation := (correctR (live a n)).mono
      (Finset.le_sup (f := fun n => cR * (TR (live a n) + 1)) (Finset.mem_Iic.mpr hn))
      (Nat.mul_le_mul_left cR (Nat.add_le_add_right (liveBound a n hn) 1))
    by_cases earlier : n < time a
    · simpa [word, hn, show n + 1 ≤ time a by omega, live, round,
        firstHalt a n earlier, Function.iterate_succ_apply'] using computation
    · have last : n = time a := by omega
      subst n
      simpa [word, live, round, halts a] using computation
  let loopTime : α → ℕ := fun a =>
    (time a + 1) * (tMax a + 10 * L a + 24) + 8 * L a + 17
  have loopCorrect (a : α) :
      (tmR.iterateWhile true).ComputesTidilyInTimeAndSpace
        (encOption encState (some (initial a)))
        (encOption encState (some (step^[time a] (initial a))))
        (loopTime a) (loopCoefficient kR cR d * (budget a + 1)) := by
    have loop := computesTidily_iterateWhile (tm := tmR) (w := word a) (r := time a)
      (oneRound a)
      (fun n hn => by simpa only [word, ite_eq_left hn] using liveBound a n hn)
      (fun n hn => by simp [word, show n + 1 ≤ time a by omega, live])
      (by simp [word]) true
    have lowered := loop.mono (t' := loopTime a) (s' := loopCoefficient kR cR d * (budget a + 1))
      le_rfl (loop_space_bound kR cR d (budget a + 1) (by omega))
    simpa only [word, Nat.zero_le, ↓reduceIte, live, Function.iterate_zero, id_eq, le_refl]
      using lowered
  let overhead := 6 * max kI (kR + 1 + 2) + 20
  let coefficient := cI + loopCoefficient kR cR d + 5 * d + overhead
  have optionComputed : ComputableInSpace (fun a => some (step^[time a] (initial a)))
      encInput (encOption encState) budget := by
    refine ⟨fun a => cI * (TI a + 1) + loopTime a +
        4 * (encOption encState (some (initial a))).length + 9,
      coefficient, ⟨_, _, inferInstance, (tmR.iterateWhile true).comp tmI true, ?_⟩, ?_⟩
    · intro a
      have initialLength := liveBound a 0 (Nat.zero_le _)
      have overheadBound : overhead ≤ overhead * (budget a + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      have computation := (correctI a).comp (loopCorrect a) true
      refine (computation.mono le_rfl ?_).computesInTimeAndSpace
      dsimp only [live, Function.iterate_zero, id_eq, L] at initialLength
      simp only [encOption_some, List.length_cons] at initialLength
      dsimp [coefficient, overhead]
      dsimp [overhead] at overheadBound
      nlinarith
    · intro a
      have outputBound := liveBound a (time a) le_rfl
      dsimp [live, L, coefficient]
      dsimp [live, L] at outputBound
      have coefficientBound : d ≤ cI + loopCoefficient kR cR d + 5 * d + overhead := by omega
      exact outputBound.trans (Nat.mul_le_mul_right _ coefficientBound)
  have untagged := budget_comp_linear (getD_inSpace encState fallback) optionComputed
  simpa only [Option.getD_some] using untagged

/-- Read out any certified scalar or structured result from the terminal state. -/
theorem computableInSpace {α σ β : Type} {encInput : α ↪ List Bool}
    {encState : σ ↪ List Bool} {encOutput : β ↪ List Bool}
    (fallback : σ) (initial : α → σ) (step : σ → σ) (halted : σ → Bool)
    (readout : σ → β) (f : α → β) (budget : α → ℕ)
    (initialSpace : ComputableInSpace initial encInput encState budget)
    (stepSpace : ComputableInSpace step encState encState (fun s => (encState s).length))
    (haltSpace : ComputableInSpace halted encState encBool (fun s => (encState s).length))
    (outputSpace : ComputableInSpace readout encState encOutput (fun s => (encState s).length))
    (time : α → ℕ)
    (halts : ∀ a, halted (step^[time a] (initial a)) = true)
    (firstHalt : ∀ a n, n < time a → halted (step^[n] (initial a)) = false)
    (output : ∀ a, readout (step^[time a] (initial a)) = f a)
    (stateBound : ∃ C, ∀ a n, n ≤ time a →
      (encState (step^[n] (initial a))).length ≤ C * (budget a + 1)) :
    ComputableInSpace f encInput encOutput budget := by
  have computed := budget_comp_linear outputSpace
    (run_inSpace fallback initial step halted budget initialSpace stepSpace haltSpace
      time halts firstHalt stateBound)
  exact computed.of_enc_eq (fun a => congrArg encOutput (output a).symm)

/-- Existential termination suffices: the least halting time is selected only
inside the proof. The constructed machine tests `halted` after each round. -/
theorem of_termination {α σ β : Type} {encInput : α ↪ List Bool}
    {encState : σ ↪ List Bool} {encOutput : β ↪ List Bool}
    (fallback : σ) (initial : α → σ) (step : σ → σ) (halted : σ → Bool)
    (readout : σ → β) (f : α → β) (budget : α → ℕ)
    (initialSpace : ComputableInSpace initial encInput encState budget)
    (stepSpace : ComputableInSpace step encState encState (fun s => (encState s).length))
    (haltSpace : ComputableInSpace halted encState encBool (fun s => (encState s).length))
    (outputSpace : ComputableInSpace readout encState encOutput (fun s => (encState s).length))
    (terminates : ∀ a, ∃ n, halted (step^[n] (initial a)) = true)
    (output : ∀ a n, halted (step^[n] (initial a)) = true → readout (step^[n] (initial a)) = f a)
    (stateBound : ∃ C, ∀ a n, (encState (step^[n] (initial a))).length ≤ C * (budget a + 1)) :
    ComputableInSpace f encInput encOutput budget := by
  let time : α → ℕ := fun a => Nat.find (terminates a)
  apply computableInSpace fallback initial step halted readout f budget initialSpace stepSpace
    haltSpace outputSpace time
  · intro a
    exact Nat.find_spec (terminates a)
  · intro a n earlier
    exact Bool.eq_false_iff.mpr (Nat.find_min (terminates a) earlier)
  · intro a
    exact output a _ (Nat.find_spec (terminates a))
  · obtain ⟨C, bounded⟩ := stateBound
    exact ⟨C, fun a n _ => bounded a n⟩

end NtimeDspace.HaltingStateCompiler
