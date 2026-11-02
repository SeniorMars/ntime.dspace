import NtimeDspace.HermiteFactorSpace
import NtimeDspace.CoefficientInitialization
import NtimeDspace.CoefficientTransitionBounds

/-!
# Closed scalar Hermite-coefficient evaluation

All persistent parameters and every continuation are explicit natural-number
data. The concrete factor accessor is called only for an active occupied leaf.
The iteration notation below describes execution prefixes and termination;
there is no supplied runtime clock or function-valued factor oracle.

The refinement identifies the total modular coefficient program for arbitrary
indices. Agreement with a reciprocal power-series coefficient additionally
uses the existing nonzero-factor, positive-multiplicity, and index-below-prime
theorems. This module supplies the closed loop and its encoded-state bounds;
machine compilation is a separate layer.
-/

namespace NtimeDspace.HermiteCoefficientLoop

open Turing Turing.MultiTapeTM CoefficientStackEncoding

abbrev Input := ℕ × ℕ × ℕ × ℕ × ℕ
abbrev encInput : Input ↪ List Bool := HermiteFactorSpace.encInput

structure State where
  modulus : ℕ
  count : ℕ
  node : ℕ
  order : ℕ
  evaluator : RawState
  deriving DecidableEq

abbrev StateData := ℕ × ℕ × ℕ × ℕ × RawState

def stateData : State ↪ StateData :=
  ⟨fun s => (s.modulus, s.count, s.node, s.order, s.evaluator), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, State.mk.injEq] using same⟩

def encState : State ↪ List Bool :=
  stateData.trans (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat CoefficientStackEncoding.encState))))

def initial (input : Input) : State :=
  ⟨input.1, input.2.1, input.2.2.1, input.2.2.2.1,
    CoefficientInitialization.initialState input.2.1 0 input.2.2.2.2⟩

def needsFactor (state : State) : Bool :=
  state.evaluator.result.isNone && decide (state.evaluator.request.height = 0) &&
    decide (state.evaluator.request.start < state.count)

def currentFactor (state : State) : ℕ × ℕ :=
  if needsFactor state then
    HermiteFactorSpace.factor state.modulus state.count state.node state.order state.evaluator.request.start
  else (0, 0)

def step (state : State) : State :=
  let factor := currentFactor state
  { state with evaluator := CoefficientTransition.advance (state.modulus, state.count, factor.1, factor.2, state.evaluator) }

def halted (state : State) : Bool := CoefficientTransition.halted state.evaluator

def output (state : State) : ℕ := state.evaluator.result.getD 0

def run (input : Input) (fuel : ℕ) : State := step^[fuel] (initial input)

theorem run_succ (input : Input) (fuel : ℕ) : run input (fuel + 1) = step (run input fuel) :=
  Function.iterate_succ_apply' step fuel (initial input)

/-- Proof-side typed accessor; the executing step calls the natural routine. -/
def factors (p Q : ℕ) [Fact p.Prime] (node : Fin Q) (order : ℕ) : IntervalCoefficients.Factors p :=
  ScalarRecoveryLoop.factorAccessor (fun i : Fin Q => ((i.val + 1 : ℕ) : ZMod p)) node order

theorem needsFactor_eq (state : State) : needsFactor state = true ↔
    state.evaluator.result = none ∧ state.evaluator.request.height = 0 ∧
      state.evaluator.request.start < state.count := by
  simp [needsFactor, and_assoc]

theorem step_parameters (state : State) :
    (step state).modulus = state.modulus ∧ (step state).count = state.count ∧
      (step state).node = state.node ∧ (step state).order = state.order := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem run_parameters (input : Input) (fuel : ℕ) :
    (run input fuel).modulus = input.1 ∧ (run input fuel).count = input.2.1 ∧
      (run input fuel).node = input.2.2.1 ∧ (run input fuel).order = input.2.2.2.1 := by
  induction fuel with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ fuel ih =>
    rw [run_succ]
    exact ih

theorem halted_stationary (state : State) (done : halted state = true) : step state = state := by
  have same := CoefficientTransition.halted_stationary
    (state.modulus, state.count, (currentFactor state).1, (currentFactor state).2, state.evaluator) done
  change { state with evaluator := CoefficientTransition.advance _ } = state
  rw [same]
  rfl

theorem step_refines (p Q : ℕ) [Fact p.Prime] (node : Fin Q) (order : ℕ)
    (state : State) (modulus : state.modulus = p) (count : state.count = Q)
    (selected : state.node = node.val) (multiplicity : state.order = order) :
    CoefficientStackEncoding.cast p (step state).evaluator =
      (SpanCoefficientStack.step (factors p Q node order) Q
        (CoefficientStackEncoding.cast p state.evaluator)).getD
          (CoefficientStackEncoding.cast p state.evaluator) := by
  change CoefficientStackEncoding.cast p (CoefficientTransition.advance
    (state.modulus, state.count, (currentFactor state).1, (currentFactor state).2, state.evaluator)) = _
  rw [modulus, count]
  apply CoefficientTransition.advance_refines_on_demand
  intro result height occupied
  have active : needsFactor state = true := (needsFactor_eq state).mpr
    ⟨result, height, by simpa [count] using occupied⟩
  rw [currentFactor, active]
  simpa only [modulus, count, selected, multiplicity, factors, ite_true] using
    (HermiteFactorSpace.factor_cast p Q order state.evaluator.request.start node).symm

theorem run_canonical (p Q node order index fuel : ℕ) [Fact p.Prime] :
    Canonical p (run (p, Q, node, order, index) fuel).evaluator := by
  induction fuel with
  | zero => simp [run, initial, CoefficientInitialization.initialState, Canonical]
  | succ fuel ih =>
    have parameters := run_parameters (p, Q, node, order, index) fuel
    rw [run_succ]
    change Canonical p (CoefficientTransition.advance _)
    rw [parameters.1]
    exact CoefficientTransitionBounds.advance_canonical _ (Fact.out : p.Prime).pos ih

/-- The stationary extension of the typed one-step relation agrees with its
existing finite-prefix driver. -/
theorem span_run_succ (p : ℕ) [Fact p.Prime] (factor : IntervalCoefficients.Factors p)
    (count fuel : ℕ) (state : SpanCoefficientStack.State p) :
    SpanCoefficientStack.run factor count (fuel + 1) state =
      (SpanCoefficientStack.step factor count (SpanCoefficientStack.run factor count fuel state)).getD
        (SpanCoefficientStack.run factor count fuel state) := by
  induction fuel generalizing state with
  | zero => cases next : SpanCoefficientStack.step factor count state <;> simp [SpanCoefficientStack.run, next]
  | succ fuel ih =>
    cases next : SpanCoefficientStack.step factor count state with
    | none => simp [SpanCoefficientStack.run, next]
    | some after => simpa only [SpanCoefficientStack.run, next] using ih after

theorem run_refines (p Q : ℕ) [Fact p.Prime] (node : Fin Q) (order index fuel : ℕ) :
    CoefficientStackEncoding.cast p (run (p, Q, node.val, order, index) fuel).evaluator =
      SpanCoefficientStack.run (factors p Q node order) Q fuel
        (SpanCoefficientStack.evaluating (CoefficientInitialization.request Q 0 index) []) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [run_succ]
    obtain ⟨modulus, count, selected, multiplicity⟩ :=
      run_parameters (p, Q, node.val, order, index) fuel
    rw [step_refines p Q node order _ modulus count selected multiplicity, ih, span_run_succ]

/-- Exact raw state, using canonical residues rather than only cast equality. -/
theorem run_evaluator_eq (p Q : ℕ) [Fact p.Prime] (node : Fin Q) (order index fuel : ℕ) :
    (run (p, Q, node.val, order, index) fuel).evaluator =
      lift (SpanCoefficientStack.run (factors p Q node order) Q fuel
        (SpanCoefficientStack.evaluating (CoefficientInitialization.request Q 0 index) [])) := by
  rw [← run_refines p Q node order index fuel]
  exact (lift_cast _ (run_canonical p Q node.val order index fuel)).symm

theorem encState_length (state : State) :
    (encState state).length =
      2 * ((encNat state.modulus).length + (encNat state.count).length +
        (encNat state.node).length + (encNat state.order).length) +
      (CoefficientStackEncoding.encState state.evaluator).length + 4 := by
  change (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat CoefficientStackEncoding.encState)))
    (state.modulus, state.count, state.node, state.order, state.evaluator)).length = _
  simp only [length_encPair]
  omega

/-- The budget includes the original input, all retained parameters, and the
serialized operational stack. It is not computed as a runtime clock. -/
def spaceBound (input : Input) : ℕ :=
  (encInput input).length +
    2 * ((encNat input.1).length + (encNat input.2.1).length +
      (encNat input.2.2.1).length + (encNat input.2.2.2.1).length) + 4 +
    (CoefficientInitialization.height input.2.1 + 1) *
      (28 * ((runRegisterBound (CoefficientInitialization.request input.2.1 0 input.2.2.2.2)
        input.1).log2 + 1) + 15)

theorem input_length_le_spaceBound (input : Input) : (encInput input).length ≤ spaceBound input := by
  unfold spaceBound
  omega

theorem spaceBound_positive (input : Input) : 0 < spaceBound input := by
  unfold spaceBound
  omega

/-- Every execution prefix has a concrete bounded binary state, with the
modulus, factor count, distinguished node, and order explicitly included. -/
theorem run_encoding_length (p Q : ℕ) [Fact p.Prime] (node : Fin Q) (order index fuel : ℕ) :
    (encState (run (p, Q, node.val, order, index) fuel)).length ≤
      spaceBound (p, Q, node.val, order, index) := by
  obtain ⟨modulus, count, selected, multiplicity⟩ := run_parameters (p, Q, node.val, order, index) fuel
  rw [encState_length, modulus, count, selected, multiplicity, run_evaluator_eq]
  have bounded := CoefficientStackEncoding.run_encoding_length (factors p Q node order) Q fuel
    (CoefficientInitialization.request Q 0 index) (CoefficientInitialization.request_span Q 0 index)
  change _ ≤ (CoefficientInitialization.height Q + 1) * _ at bounded
  unfold spaceBound
  dsimp only
  omega

/-- Existence of a genuine terminal return of the closed loop. The witness is
used only in proofs; no natural clock is an input to the runtime transition. -/
theorem terminates (p Q : ℕ) [Fact p.Prime] (node : Fin Q) (order index : ℕ) :
    ∃ fuel, halted (run (p, Q, node.val, order, index) fuel) = true ∧
      output (run (p, Q, node.val, order, index) fuel) =
        (IntervalCoefficients.allCoefficient (factors p Q node order) Q index).val := by
  obtain ⟨fuel, done⟩ := SpanCoefficientStack.terminates (factors p Q node order) Q
    (CoefficientInitialization.request Q 0 index) (CoefficientInitialization.request_span Q 0 index)
  have state := run_evaluator_eq p Q node order index fuel
  rw [done] at state
  have coefficient : IntervalCoefficients.coefficient (factors p Q node order) Q
      (CoefficientInitialization.request Q 0 index).height
      (CoefficientInitialization.request Q 0 index).start
      (CoefficientInitialization.request Q 0 index).degree =
      IntervalCoefficients.allCoefficient (factors p Q node order) Q index := by
    simp only [CoefficientInitialization.request, CoefficientInitialization.height_eq_clog,
      IntervalCoefficients.allCoefficient]
  rw [coefficient] at state
  refine ⟨fuel, ?_, ?_⟩ <;>
    simp [halted, output, state, CoefficientTransition.halted,
      CoefficientStackEncoding.lift, SpanCoefficientStack.returning]

theorem iterate_of_halted (state : State) (done : halted state = true) (fuel : ℕ) :
    step^[fuel] state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply', ih, halted_stationary state done]

theorem run_add_of_halted (input : Input) (fuel rest : ℕ)
    (done : halted (run input fuel) = true) : run input (fuel + rest) = run input fuel := by
  change step^[fuel + rest] (initial input) = _
  rw [Nat.add_comm fuel rest, Function.iterate_add_apply]
  exact iterate_of_halted _ done rest

/-- Every terminal prefix has the same canonical answer, so a first-halt
compiler may choose its stopping time without a supplied time function. -/
theorem output_correct (p Q : ℕ) [Fact p.Prime] (node : Fin Q) (order index fuel : ℕ)
    (done : halted (run (p, Q, node.val, order, index) fuel) = true) :
    output (run (p, Q, node.val, order, index) fuel) =
      (IntervalCoefficients.allCoefficient (factors p Q node order) Q index).val := by
  obtain ⟨terminal, halts, correct⟩ := terminates p Q node order index
  have same : run (p, Q, node.val, order, index) fuel =
      run (p, Q, node.val, order, index) terminal := by
    rcases Nat.le_total fuel terminal with before | after
    · have fixed := run_add_of_halted (p, Q, node.val, order, index) fuel (terminal - fuel) done
      rw [Nat.add_sub_of_le before] at fixed
      exact fixed.symm
    · have fixed := run_add_of_halted (p, Q, node.val, order, index) terminal (fuel - terminal) halts
      rw [Nat.add_sub_of_le after] at fixed
      exact fixed
  rw [same, correct]

end NtimeDspace.HermiteCoefficientLoop
