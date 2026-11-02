import NtimeDspace.CoefficientTransition

/-!
Canonical-residue preservation and exact lifting for the uniform coefficient
transition. These invariants connect its natural registers to the established
typed execution bounds. The current factor is still supplied as two explicit
scalar inputs; obtaining those inputs is a separate obligation.
-/

namespace NtimeDspace.CoefficientTransitionBounds

open CoefficientStackEncoding CoefficientTransition
open Turing Turing.MultiTapeTM

/-- The compiler receives all four scalar parameters as well as the complete
state. Each scalar contributes its framed binary word, not just its value tag. -/
theorem encInput_length (input : Input) :
    (encInput input).length = (encState (state input)).length +
      2 * ((encNat (modulus input)).length + (encNat (count input)).length +
        (encNat (factorValue input)).length + (encNat (factorMultiplicity input)).length) + 4 := by
  simp only [encInput, length_encPair, state, modulus, count, factorValue, factorMultiplicity]
  omega

/-- Separate bounds for fetched factor values and multiplicities. No factor
read correctness premise is needed to account for their stored bits. -/
theorem input_length_of_factor_bounds (p count a multiplicity : ℕ) (s : RawState)
    (valueBound multiplicityBound : ℕ) (value : a ≤ valueBound)
    (multiplicitySmall : multiplicity ≤ multiplicityBound) :
    (encInput (p, count, a, multiplicity, s)).length ≤ (encState s).length +
      2 * ((p.log2 + 1) + (count.log2 + 1) + (valueBound.log2 + 1) +
        (multiplicityBound.log2 + 1)) + 4 := by
  have hp := length_encNat_le_log2 (Nat.le_refl p)
  have hc := length_encNat_le_log2 (Nat.le_refl count)
  have ha := length_encNat_le_log2 value
  have hm := length_encNat_le_log2 multiplicitySmall
  rw [encInput_length]
  dsimp only [state, modulus, CoefficientTransition.count, factorValue, factorMultiplicity]
  omega

theorem input_length_of_envelope (p count a multiplicity : ℕ) (s : RawState)
    (bound : ℕ) (modulusSmall : p ≤ bound) (countSmall : count ≤ bound)
    (valueSmall : a ≤ bound) (multiplicitySmall : multiplicity ≤ bound) :
    (encInput (p, count, a, multiplicity, s)).length ≤
      (encState s).length + 8 * (bound.log2 + 1) + 4 := by
  have hp := length_encNat_le_log2 modulusSmall
  have hc := length_encNat_le_log2 countSmall
  have ha := length_encNat_le_log2 valueSmall
  have hm := length_encNat_le_log2 multiplicitySmall
  rw [encInput_length]
  dsimp only [state, modulus, CoefficientTransition.count, factorValue, factorMultiplicity]
  omega

theorem leaf_lt_modulus (input : Input) (positive : 0 < modulus input) :
    leaf input < modulus input := by
  unfold leaf
  split_ifs
  · exact ReciprocalLeafSpace.reciprocal_lt_modulus _ _ _ _ positive
  · exact Nat.mod_lt _ positive
  · exact positive

private theorem evaluating_canonical (p : ℕ) (request : RawRequest)
    (stack : List RawContinuation)
    (frames : ∀ frame ∈ stack, frame.accumulator < p ∧ ∀ value ∈ frame.savedLeft, value < p) :
    Canonical p (evaluating request stack) := by
  exact ⟨by simp [evaluating], frames⟩

private theorem returning_canonical (p : ℕ) (request : RawRequest) (value : ℕ)
    (stack : List RawContinuation) (small : value < p)
    (frames : ∀ frame ∈ stack, frame.accumulator < p ∧ ∀ value ∈ frame.savedLeft, value < p) :
    Canonical p (returning request value stack) := by
  exact ⟨by simpa [returning] using small, frames⟩

theorem descend_canonical (p : ℕ) (positive : 0 < p) (s : RawState)
    (canonical : Canonical p s) : Canonical p (descend s) := by
  apply evaluating_canonical
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨positive, by simp⟩
  · exact canonical.2 frame member

theorem saveLeft_canonical (p : ℕ) (positive : 0 < p) (s : RawState)
    (canonical : Canonical p s) : Canonical p (saveLeft s) := by
  apply evaluating_canonical
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · refine ⟨?_, canonical.1⟩
    cases stack : s.stack with
    | nil => simpa [stack, defaultFrame] using positive
    | cons head rest =>
      simpa [stack] using (canonical.2 head (by simp [stack])).1
  · exact canonical.2 frame (List.mem_of_mem_tail member)

theorem combine_canonical (p : ℕ) (positive : 0 < p) (s : RawState)
    (canonical : Canonical p s) : Canonical p (combine p s) := by
  have small := ResidueArithmetic.add_lt_modulus p
    (ResidueArithmetic.mul p ((s.stack.headD defaultFrame).savedLeft.getD 0)
      (s.result.getD 0)) (s.stack.headD defaultFrame).accumulator positive
  unfold combine
  dsimp only
  split_ifs
  · exact returning_canonical p _ _ _ small
      (fun frame member => canonical.2 frame (List.mem_of_mem_tail member))
  · apply evaluating_canonical
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨small, by simp⟩
    · exact canonical.2 frame (List.mem_of_mem_tail member)

/-- Every stored scalar remains the canonical residue, even when the other
registers have malformed heights, spans, or indices. -/
theorem advance_canonical (input : Input) (positive : 0 < modulus input)
    (canonical : Canonical (modulus input) (state input)) :
    Canonical (modulus input) (advance input) := by
  unfold advance
  dsimp only
  split_ifs
  · exact canonical
  · exact combine_canonical _ positive _ canonical
  · exact saveLeft_canonical _ positive _ canonical
  · exact returning_canonical _ _ _ _ (leaf_lt_modulus input positive) canonical.2
  · exact descend_canonical _ positive _ canonical

/-- Casting no longer loses information: a canonical raw transition is exactly
the canonical lift of the typed transition, including its stationary halt. -/
theorem advance_eq_lift (p count a multiplicity : ℕ) [Fact p.Prime]
    (s : RawState) (canonical : Canonical p s) (factor : IntervalCoefficients.Factors p)
    (reads : s.request.start < count → factor s.request.start = ((a : ZMod p), multiplicity)) :
    advance (p, count, a, multiplicity, s) =
      lift ((SpanCoefficientStack.step factor count (cast p s)).getD (cast p s)) := by
  have preserved := advance_canonical (p, count, a, multiplicity, s)
    (Fact.out : p.Prime).pos canonical
  calc
    _ = lift (cast p (advance (p, count, a, multiplicity, s))) :=
      (lift_cast (p := p) _ preserved).symm
    _ = _ := congrArg lift (advance_refines p count a multiplicity s factor reads)

theorem advance_lift (p count a multiplicity : ℕ) [Fact p.Prime]
    (s : SpanCoefficientStack.State p) (factor : IntervalCoefficients.Factors p)
    (reads : s.request.start < count → factor s.request.start = ((a : ZMod p), multiplicity)) :
    advance (p, count, a, multiplicity, lift s) =
      lift ((SpanCoefficientStack.step factor count s).getD s) := by
  simpa only [cast_lift] using
    advance_eq_lift p count a multiplicity (lift s) (lift_canonical s) factor reads

/-- Only an occupied leaf evaluation needs a fetched factor. All internal,
returning, terminal and padding states may supply arbitrary dummy fields. -/
theorem advance_eq_lift_on_demand (p count a multiplicity : ℕ) [Fact p.Prime]
    (s : RawState) (canonical : Canonical p s) (factor : IntervalCoefficients.Factors p)
    (reads : s.result = none → s.request.height = 0 → s.request.start < count →
      factor s.request.start = ((a : ZMod p), multiplicity)) :
    advance (p, count, a, multiplicity, s) =
      lift ((SpanCoefficientStack.step factor count (cast p s)).getD (cast p s)) := by
  have preserved := advance_canonical (p, count, a, multiplicity, s)
    (Fact.out : p.Prime).pos canonical
  calc
    _ = lift (cast p (advance (p, count, a, multiplicity, s))) :=
      (lift_cast (p := p) _ preserved).symm
    _ = _ := congrArg lift (advance_refines_on_demand p count a multiplicity s factor reads)

theorem advance_lift_on_demand (p count a multiplicity : ℕ) [Fact p.Prime]
    (s : SpanCoefficientStack.State p) (factor : IntervalCoefficients.Factors p)
    (reads : s.result = none → s.request.height = 0 → s.request.start < count →
      factor s.request.start = ((a : ZMod p), multiplicity)) :
    advance (p, count, a, multiplicity, lift s) =
      lift ((SpanCoefficientStack.step factor count s).getD s) := by
  have rawReads : (lift s).result = none → (lift s).request.height = 0 →
      (lift s).request.start < count →
      factor (lift s).request.start = ((a : ZMod p), multiplicity) := by
    intro empty height inside
    have resultNone : s.result = none := by
      cases result : s.result <;> simp_all [lift]
    exact reads resultNone height inside
  simpa only [cast_lift] using
    advance_eq_lift_on_demand p count a multiplicity (lift s) (lift_canonical s) factor rawReads

/-- The raw halting test recognizes exactly the typed transition's terminal
return; no factor-read or canonical-residue premise is needed for this test. -/
theorem halted_iff_step_none (p count : ℕ) [Fact p.Prime]
    (s : RawState) (factor : IntervalCoefficients.Factors p) :
    halted s = true ↔ SpanCoefficientStack.step factor count (cast p s) = none := by
  rcases s with ⟨⟨height, start, degree, span⟩, result, stack⟩
  cases result with
  | none =>
    cases height <;> simp [halted, CoefficientStackEncoding.cast, SpanCoefficientStack.step]
  | some value =>
    cases stack with
    | nil => simp [halted, CoefficientStackEncoding.cast, SpanCoefficientStack.step]
    | cons frame rest =>
      rcases frame with ⟨height', start', degree', split, span', accumulator, saved⟩
      cases saved with
      | none => simp [halted, CoefficientStackEncoding.cast, castContinuation, SpanCoefficientStack.step]
      | some left =>
        cases split <;> simp [halted, CoefficientStackEncoding.cast, castContinuation, SpanCoefficientStack.step]

theorem halted_lift_iff_step_none (p count : ℕ) [Fact p.Prime]
    (s : SpanCoefficientStack.State p) (factor : IntervalCoefficients.Factors p) :
    halted (lift s) = true ↔ SpanCoefficientStack.step factor count s = none := by
  simpa only [cast_lift] using halted_iff_step_none p count (lift s) factor

private theorem typed_run_succ {p : ℕ} [Fact p.Prime]
    (factor : IntervalCoefficients.Factors p) (count fuel : ℕ)
    (s : SpanCoefficientStack.State p) :
    SpanCoefficientStack.run factor count (fuel + 1) s =
      (SpanCoefficientStack.step factor count (SpanCoefficientStack.run factor count fuel s)).getD
        (SpanCoefficientStack.run factor count fuel s) := by
  induction fuel generalizing s with
  | zero =>
    simp only [SpanCoefficientStack.run]
    cases SpanCoefficientStack.step factor count s <;> rfl
  | succ fuel ih =>
    cases step : SpanCoefficientStack.step factor count s with
    | none => simp [SpanCoefficientStack.run, step]
    | some next => simpa only [SpanCoefficientStack.run, step] using ih next

/-- Exact next-prefix identity when the current raw state is a lifted typed run. -/
theorem advance_run_eq_lift (p count fuel a multiplicity : ℕ) [Fact p.Prime]
    (factor : IntervalCoefficients.Factors p) (root : RawRequest)
    (reads :
      (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).request.start < count →
        factor (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).request.start =
          ((a : ZMod p), multiplicity)) :
    advance (p, count, a, multiplicity,
      lift (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root []))) =
      lift (SpanCoefficientStack.run factor count (fuel + 1) (SpanCoefficientStack.evaluating root [])) := by
  rw [advance_lift p count a multiplicity _ factor reads, typed_run_succ]

theorem advance_run_eq_lift_on_demand (p count fuel a multiplicity : ℕ) [Fact p.Prime]
    (factor : IntervalCoefficients.Factors p) (root : RawRequest)
    (reads :
      (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).result = none →
      (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).request.height = 0 →
      (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).request.start < count →
        factor (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).request.start =
          ((a : ZMod p), multiplicity)) :
    advance (p, count, a, multiplicity,
      lift (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root []))) =
      lift (SpanCoefficientStack.run factor count (fuel + 1) (SpanCoefficientStack.evaluating root [])) := by
  rw [advance_lift_on_demand p count a multiplicity _ factor reads, typed_run_succ]

/-- Every numeric output field inherits the existing reachable-state envelope. -/
theorem advance_run_values_bounded (p count fuel a multiplicity : ℕ) [Fact p.Prime]
    (factor : IntervalCoefficients.Factors p) (root : RawRequest)
    (span : root.span = 2 ^ root.height)
    (reads :
      (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).request.start < count →
        factor (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).request.start =
          ((a : ZMod p), multiplicity)) :
    ValuesBounded (runRegisterBound root p)
      (advance (p, count, a, multiplicity,
        lift (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])))) := by
  rw [advance_run_eq_lift p count fuel a multiplicity factor root reads]
  exact run_values_bounded factor count (fuel + 1) root span

/-- Concrete serialized output bound, including all residues, option tags,
continuations and delimiters. Factor access and transition costs are separate. -/
theorem advance_run_encoding_length (p count fuel a multiplicity : ℕ) [Fact p.Prime]
    (factor : IntervalCoefficients.Factors p) (root : RawRequest)
    (span : root.span = 2 ^ root.height)
    (reads :
      (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).request.start < count →
        factor (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])).request.start =
          ((a : ZMod p), multiplicity)) :
    (encState (advance (p, count, a, multiplicity,
      lift (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root []))))).length ≤
      (root.height + 1) * (28 * ((runRegisterBound root p).log2 + 1) + 15) := by
  rw [advance_run_eq_lift p count fuel a multiplicity factor root reads]
  exact run_encoding_length factor count (fuel + 1) root span

/-- The complete input to the globally certified transition, at every execution
prefix. This includes modulus, factor count, fetched value and multiplicity in
addition to the serialized stack. Fetching costs remain a separate obligation. -/
theorem run_input_encoding_length (p count fuel a multiplicity : ℕ) [Fact p.Prime]
    (factor : IntervalCoefficients.Factors p) (root : RawRequest)
    (span : root.span = 2 ^ root.height) (bound : ℕ)
    (registers : runRegisterBound root p ≤ bound) (countSmall : count ≤ bound)
    (valueSmall : a ≤ bound) (multiplicitySmall : multiplicity ≤ bound) :
    (encInput (p, count, a, multiplicity,
      lift (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])))).length ≤
      (root.height + 1) * (28 * (bound.log2 + 1) + 15) +
        8 * (bound.log2 + 1) + 4 := by
  have modulusSmall : p ≤ bound := by
    unfold runRegisterBound at registers
    omega
  have logarithms : (runRegisterBound root p).log2 ≤ bound.log2 := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) registers
  have stateBound := run_encoding_length factor count fuel root span
  have inputBound := input_length_of_envelope p count a multiplicity
    (lift (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])))
    bound modulusSmall countSmall valueSmall multiplicitySmall
  have larger : (root.height + 1) * (28 * ((runRegisterBound root p).log2 + 1) + 15) ≤
      (root.height + 1) * (28 * (bound.log2 + 1) + 15) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end NtimeDspace.CoefficientTransitionBounds
