import NtimeDspace.HermiteCoefficientCorrectness

/-!
# Closed scalar evaluation of a Hermite recovery weight

The header and two natural registers are explicit binary data. Each iteration
uses the already compiled coefficient function, modular exponentiation, and
reduced multiplication and addition. The coefficient function is named by its
semantic specification, whose realizing machine is proved in
`HermiteCoefficientMachine`; it is not an assumed arithmetic oracle.
-/

namespace NtimeDspace.HermiteWeightLoop

open Turing Turing.MultiTapeTM

abbrev RawHeader := ℕ × ℕ × ℕ × ℕ × ℕ

def Valid (input : RawHeader) : Prop :=
  input.1.Prime ∧ input.2.2.1 < input.2.1 ∧ input.2.1 < input.1 ∧
    input.2.2.2.1 ≤ input.1 ∧ input.2.2.2.2 < input.1

abbrev Header := {input : RawHeader // Valid input}

def fallbackHeader : Header := ⟨(2, 1, 0, 0, 0), by norm_num [Valid]⟩

def encHeader : Header ↪ List Bool :=
  (⟨Subtype.val, Subtype.val_injective⟩ : Header ↪ RawHeader).trans HermiteFactorSpace.encInput

def modulus (header : Header) : ℕ := header.val.1
def count (header : Header) : ℕ := header.val.2.1
def node (header : Header) : ℕ := header.val.2.2.1
def order (header : Header) : ℕ := header.val.2.2.2.1
def point (header : Header) : ℕ := header.val.2.2.2.2

theorem modulus_prime (header : Header) : (modulus header).Prime := header.property.1
theorem node_lt_count (header : Header) : node header < count header := header.property.2.1
theorem count_lt_modulus (header : Header) : count header < modulus header := header.property.2.2.1
theorem order_le_modulus (header : Header) : order header ≤ modulus header := header.property.2.2.2.1
theorem point_lt_modulus (header : Header) : point header < modulus header := header.property.2.2.2.2

structure State where
  header : Header
  remaining : ℕ
  accumulator : ℕ

abbrev StateData := Header × ℕ × ℕ

def stateData : State ↪ StateData :=
  ⟨fun s => (s.header, s.remaining, s.accumulator), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, State.mk.injEq] using same⟩

def encState : State ↪ List Bool := stateData.trans (encPair encHeader (encPair encNat encNat))

def initial (header : Header) : State := ⟨header, order header, 0⟩

/-- The modulo makes every query a valid bounded-machine input, even on raw
states whose remaining counter violates the reachable-state invariant. -/
def queryIndex (state : State) : ℕ := (state.remaining - 1) % (modulus state.header + 1)

def coefficientInput (state : State) : HermiteCoefficientMachine.BoundedInput :=
  ⟨⟨(modulus state.header, count state.header, node state.header, order state.header, queryIndex state),
    modulus_prime state.header, node_lt_count state.header⟩,
    (count_lt_modulus state.header).le, order_le_modulus state.header,
    Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))⟩

noncomputable def step (state : State) : State :=
  if state.remaining = 0 then state else
    { state with
      remaining := state.remaining - 1
      accumulator := ResidueArithmetic.add (modulus state.header)
        (ResidueArithmetic.mul (modulus state.header)
          (HermiteCoefficientMachine.coefficient (coefficientInput state).val)
          (ResidueArithmetic.power (modulus state.header) (point state.header) (queryIndex state)))
        state.accumulator }

def halted (state : State) : Bool := decide (state.remaining = 0)
def output (state : State) : ℕ := state.accumulator

noncomputable def run (header : Header) (fuel : ℕ) : State := step^[fuel] (initial header)

theorem step_header (state : State) : (step state).header = state.header := by
  unfold step
  split_ifs <;> rfl

theorem step_remaining (state : State) : (step state).remaining = state.remaining - 1 := by
  unfold step
  split_ifs with zero
  · simp [zero]
  · rfl

theorem run_succ (header : Header) (fuel : ℕ) :
    run header (fuel + 1) = step (run header fuel) := Function.iterate_succ_apply' ..

theorem run_header (header : Header) (fuel : ℕ) : (run header fuel).header = header := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [run_succ, step_header, ih]

theorem run_remaining (header : Header) (fuel : ℕ) :
    (run header fuel).remaining = order header - fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [run_succ, step_remaining, ih]; omega

theorem run_remaining_le_order (header : Header) (fuel : ℕ) :
    (run header fuel).remaining ≤ order header := by
  rw [run_remaining]
  exact Nat.sub_le _ _

theorem step_accumulator_lt (state : State)
    (canonical : state.accumulator < modulus state.header) :
    (step state).accumulator < modulus state.header := by
  unfold step
  split_ifs
  · exact canonical
  · exact ResidueArithmetic.add_lt_modulus _ _ _ (modulus_prime state.header).pos

theorem run_accumulator_lt (header : Header) (fuel : ℕ) :
    (run header fuel).accumulator < modulus header := by
  induction fuel with
  | zero => exact (modulus_prime header).pos
  | succ fuel ih =>
    rw [run_succ]
    simpa only [run_header] using
      step_accumulator_lt (run header fuel) (by simpa only [run_header] using ih)

theorem halted_iff (state : State) : halted state = true ↔ state.remaining = 0 := by
  simp [halted]

theorem run_halted_iff (header : Header) (fuel : ℕ) :
    halted (run header fuel) = true ↔ order header ≤ fuel := by
  rw [halted_iff, run_remaining]
  exact Nat.sub_eq_zero_iff_le

theorem terminal_halted (header : Header) : halted (run header (order header)) = true :=
  (run_halted_iff header (order header)).mpr le_rfl

theorem terminates (header : Header) : ∃ fuel, halted (run header fuel) = true :=
  ⟨order header, terminal_halted header⟩

theorem halted_stationary (state : State) (done : halted state = true) : step state = state := by
  simp [step, (halted_iff state).mp done]

theorem iterate_of_halted (state : State) (done : halted state = true) (fuel : ℕ) :
    step^[fuel] state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply', ih, halted_stationary state done]

theorem run_eq_terminal (header : Header) (fuel : ℕ) (done : halted (run header fuel) = true) :
    run header fuel = run header (order header) := by
  have enough := (run_halted_iff header fuel).mp done
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le enough
  change step^[order header + rest] (initial header) = _
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact iterate_of_halted _ (terminal_halted header) rest

theorem queryIndex_eq (state : State) (bounded : state.remaining ≤ order state.header) :
    queryIndex state = state.remaining - 1 := by
  apply Nat.mod_eq_of_lt
  have within := order_le_modulus state.header
  omega

/-- Field-valued coefficient used only as a specification of the compiled
natural-valued callee. -/
noncomputable def coefficientValue (header : Header) (index : ℕ) : ZMod (modulus header) := by
  let : Fact (modulus header).Prime := ⟨modulus_prime header⟩
  exact IntervalCoefficients.allCoefficient
    (HermiteCoefficientLoop.factors (modulus header) (count header)
      ⟨node header, node_lt_count header⟩ (order header)) (count header) index

noncomputable def term (header : Header) (index : ℕ) : ZMod (modulus header) :=
  coefficientValue header index * (point header : ZMod (modulus header)) ^ index

noncomputable def fieldWeight (header : Header) : ZMod (modulus header) := by
  let : Fact (modulus header).Prime := ⟨modulus_prime header⟩
  exact ScalarRecoveryLoop.weight
    (SelectedCounter.nodeValue (p := modulus header) (nodes := count header))
    ⟨node header, node_lt_count header⟩ (order header) (point header : ZMod (modulus header))

noncomputable def weight (header : Header) : ℕ := (fieldWeight header).val

theorem fieldWeight_eq_sumLoop (header : Header) :
    fieldWeight header = sumLoop (term header) (order header) 0 := rfl

theorem coefficient_cast (state : State) :
    (HermiteCoefficientMachine.coefficient (coefficientInput state).val :
      ZMod (modulus state.header)) = coefficientValue state.header (queryIndex state) := by
  let : Fact (modulus state.header).Prime := ⟨modulus_prime state.header⟩
  change ((coefficientValue state.header (queryIndex state)).val : ZMod (modulus state.header)) = _
  exact ZMod.natCast_zmod_val _

theorem step_accumulator_cast (state : State) (positive : 0 < state.remaining) :
    ((step state).accumulator : ZMod (modulus state.header)) =
      term state.header (queryIndex state) + (state.accumulator : ZMod (modulus state.header)) := by
  have nonzero : state.remaining ≠ 0 := Nat.ne_of_gt positive
  simp only [step, nonzero, ↓reduceIte]
  rw [ResidueArithmetic.add_cast, ResidueArithmetic.mul_cast,
    ResidueArithmetic.power_cast _ _ _ (modulus_prime state.header).ne_zero, coefficient_cast]
  rfl

theorem iterate_output_cast (header : Header) (remaining accumulator : ℕ)
    (bounded : remaining ≤ order header) :
    (output (step^[remaining] (⟨header, remaining, accumulator⟩ : State)) : ZMod (modulus header)) =
      sumLoop (term header) remaining (accumulator : ZMod (modulus header)) := by
  induction remaining generalizing accumulator with
  | zero => rfl
  | succ remaining ih =>
    have query : queryIndex (⟨header, remaining + 1, accumulator⟩ : State) = remaining := by
      rw [queryIndex_eq _ bounded]
      rfl
    rw [Function.iterate_succ_apply]
    have first : step (⟨header, remaining + 1, accumulator⟩ : State) =
        ⟨header, remaining,
          (step (⟨header, remaining + 1, accumulator⟩ : State)).accumulator⟩ := by
      simp [step]
    rw [first, ih _ (by omega), sumLoop]
    rw [step_accumulator_cast _ (by simp), query]

theorem terminal_output_cast (header : Header) :
    (output (run header (order header)) : ZMod (modulus header)) = fieldWeight header := by
  rw [fieldWeight_eq_sumLoop]
  simpa only [run, initial, Nat.cast_zero] using iterate_output_cast header (order header) 0 le_rfl

theorem output_correct (header : Header) (fuel : ℕ) (done : halted (run header fuel) = true) :
    output (run header fuel) = weight header := by
  rw [run_eq_terminal header fuel done]
  have castCorrect := congrArg ZMod.val (terminal_output_cast header)
  have small : output (run header (order header)) < modulus header :=
    run_accumulator_lt header (order header)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt small] at castCorrect
  exact castCorrect

noncomputable def polynomialWeight (header : Header) : ℕ := by
  let : Fact (modulus header).Prime := ⟨modulus_prime header⟩
  exact ((HermiteRecovery.nodeWeight
    (Finset.univ.image (SelectedCounter.nodeValue (p := modulus header) (nodes := count header)))
    (SelectedCounter.nodeValue (p := modulus header)
      (⟨node header, node_lt_count header⟩ : Fin (count header))) (order header)).eval
    (point header : ZMod (modulus header))).val

theorem weight_eq_nodeWeight (header : Header) (positive : 0 < order header) :
    weight header = polynomialWeight header := by
  let : Fact (modulus header).Prime := ⟨modulus_prime header⟩
  have correct := ScalarRecoveryLoop.weight_correct
    (SelectedCounter.nodeValue (p := modulus header) (nodes := count header))
    (SelectedCounter.nodeValue_injective (count_lt_modulus header))
    ⟨node header, node_lt_count header⟩
    (SelectedCounter.nodeValue_nonzero (count_lt_modulus header)
      ⟨node header, node_lt_count header⟩)
    (order header) positive (order_le_modulus header) (point header : ZMod (modulus header))
  exact congrArg ZMod.val correct

end NtimeDspace.HermiteWeightLoop
