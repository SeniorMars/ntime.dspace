import NtimeDspace.CoefficientStackEncoding
import NtimeDspace.ReciprocalLeafSpace

/-!
Uniform natural-register control for one coefficient-stack transition.
The modulus, factor count, and current factor's two scalar fields are data.
The transition contains no field-valued register or function-valued accessor.
The input factor pair must still be fetched by the enclosing evaluator; the
refinement theorem states that connection explicitly.
-/

namespace NtimeDspace.CoefficientTransition

open CoefficientStackEncoding

abbrev Input := ℕ × ℕ × ℕ × ℕ × RawState

def encInput : Input ↪ List Bool :=
  Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat encState)))

def modulus (input : Input) : ℕ := input.1
def count (input : Input) : ℕ := input.2.1
def factorValue (input : Input) : ℕ := input.2.2.1
def factorMultiplicity (input : Input) : ℕ := input.2.2.2.1
def state (input : Input) : RawState := input.2.2.2.2

def defaultFrame : RawContinuation := ⟨0, 0, 0, 0, 0, 0, none⟩

def parent (frame : RawContinuation) : RawRequest :=
  ⟨frame.height + 1, frame.start, frame.degree, 2 * frame.span⟩

def child (frame : RawContinuation) : RawRequest :=
  if frame.savedLeft.isSome then
    ⟨frame.height, frame.start + frame.span, frame.degree - frame.split, frame.span⟩
  else ⟨frame.height, frame.start, frame.split, frame.span⟩

def evaluating (request : RawRequest) (stack : List RawContinuation) : RawState :=
  ⟨request, none, stack⟩

def returning (request : RawRequest) (value : ℕ) (stack : List RawContinuation) : RawState :=
  ⟨request, some value, stack⟩

/-- The current factor is an explicit pair of natural inputs. Padding leaves
need no factor lookup. All arithmetic is reduced modulo the encoded modulus. -/
def leaf (input : Input) : ℕ :=
  if (state input).request.start < count input then
    ReciprocalLeafSpace.reciprocal (modulus input) (factorValue input)
      (factorMultiplicity input) (state input).request.degree
  else if (state input).request.degree = 0 then 1 % modulus input else 0

def descend (s : RawState) : RawState :=
  let frame : RawContinuation :=
    ⟨s.request.height - 1, s.request.start, s.request.degree, s.request.degree,
      s.request.span / 2, 0, none⟩
  evaluating (child frame) (frame :: s.stack)

def saveLeft (s : RawState) : RawState :=
  let frame := { s.stack.headD defaultFrame with savedLeft := s.result }
  evaluating (child frame) (frame :: s.stack.tail)

def combine (p : ℕ) (s : RawState) : RawState :=
  let frame := s.stack.headD defaultFrame
  let acc := ResidueArithmetic.add p
    (ResidueArithmetic.mul p (frame.savedLeft.getD 0) (s.result.getD 0)) frame.accumulator
  if frame.split = 0 then returning (parent frame) acc s.stack.tail
  else
    let next := { frame with split := frame.split - 1, accumulator := acc, savedLeft := none }
    evaluating (child next) (next :: s.stack.tail)

/-- A halted return is stationary. Every other transition uses only binary
register arithmetic, one stack push/pop, and the certified reciprocal leaf. -/
def advance (input : Input) : RawState :=
  let s := state input
  if s.result.isSome then
    if s.stack.isEmpty then s
    else if (s.stack.headD defaultFrame).savedLeft.isSome then combine (modulus input) s
    else saveLeft s
  else if s.request.height = 0 then returning s.request (leaf input) s.stack
  else descend s

def halted (s : RawState) : Bool := s.result.isSome && s.stack.isEmpty

theorem halted_stationary (input : Input) (done : halted (state input) = true) :
    advance input = state input := by
  simp only [halted, Bool.and_eq_true] at done
  simp [advance, done.1, done.2]

theorem cast_parent (p : ℕ) (frame : RawContinuation) :
    parent frame = (castContinuation p frame).parent := rfl

theorem cast_child (p : ℕ) (frame : RawContinuation) :
    child frame = (castContinuation p frame).child := by
  cases saved : frame.savedLeft <;>
    simp [child, castContinuation, SpanCoefficientStack.Continuation.child, saved]

theorem cast_evaluating (p : ℕ) (request : RawRequest) (stack : List RawContinuation) :
    CoefficientStackEncoding.cast p (evaluating request stack) =
      SpanCoefficientStack.evaluating request (stack.map (castContinuation p)) := rfl

theorem cast_returning (p : ℕ) (request : RawRequest) (value : ℕ)
    (stack : List RawContinuation) :
    CoefficientStackEncoding.cast p (returning request value stack) =
      SpanCoefficientStack.returning request (value : ZMod p) (stack.map (castContinuation p)) := rfl

/-- Factor fetching is a separate obligation: the two explicit input fields
must agree with the indexed factor at the requested occupied leaf. -/
theorem leaf_cast (p count a multiplicity : ℕ) [Fact p.Prime]
    (s : RawState) (factor : IntervalCoefficients.Factors p)
    (reads : s.request.start < count → factor s.request.start = ((a : ZMod p), multiplicity)) :
    (leaf (p, count, a, multiplicity, s) : ZMod p) =
      IntervalCoefficients.coefficient factor count 0 s.request.start s.request.degree := by
  change ((if s.request.start < count then
    ReciprocalLeafSpace.reciprocal p a multiplicity s.request.degree
    else if s.request.degree = 0 then 1 % p else 0 : ℕ) : ZMod p) = _
  by_cases occupied : s.request.start < count
  · simp only [occupied, ↓reduceIte, IntervalCoefficients.coefficient, reads occupied]
    exact ReciprocalLeafSpace.reciprocal_cast p a multiplicity s.request.degree
  · by_cases zero : s.request.degree = 0 <;>
      simp [occupied, zero, IntervalCoefficients.coefficient, ZMod.natCast_mod]

/-- Exact refinement of one operational transition. No field-valued runtime
register or hidden arithmetic callback is used; only the indexed factor-read
identity remains a premise. The legacy halt is represented by a stationary
state, as required by a query-machine transition. -/
theorem advance_refines (p count a multiplicity : ℕ) [Fact p.Prime]
    (s : RawState) (factor : IntervalCoefficients.Factors p)
    (reads : s.request.start < count → factor s.request.start = ((a : ZMod p), multiplicity)) :
    CoefficientStackEncoding.cast p (advance (p, count, a, multiplicity, s)) =
      (SpanCoefficientStack.step factor count (CoefficientStackEncoding.cast p s)).getD (CoefficientStackEncoding.cast p s) := by
  have leafCorrect := leaf_cast p count a multiplicity s factor reads
  rcases s with ⟨⟨height, start, degree, span⟩, result, stack⟩
  cases result with
  | none =>
    cases height with
    | zero =>
      simpa [advance, state, CoefficientStackEncoding.cast,
        SpanCoefficientStack.step, returning, SpanCoefficientStack.returning] using
        congrArg (fun value : ZMod p =>
          SpanCoefficientStack.returning (⟨0, start, degree, span⟩ : RawRequest)
            value (stack.map (castContinuation p))) leafCorrect
    | succ height =>
      simp [advance, state, descend, child, evaluating, CoefficientStackEncoding.cast, castContinuation,
        SpanCoefficientStack.step, SpanCoefficientStack.evaluating,
        SpanCoefficientStack.Continuation.child]
  | some value =>
    cases stack with
    | nil =>
      simp [advance, state, CoefficientStackEncoding.cast, SpanCoefficientStack.step]
    | cons frame rest =>
      rcases frame with ⟨height', start', degree', split, span', accumulator, saved⟩
      cases saved with
      | none =>
        simp [advance, state, saveLeft, defaultFrame, child, evaluating,
          CoefficientStackEncoding.cast, castContinuation, SpanCoefficientStack.step,
          SpanCoefficientStack.evaluating, SpanCoefficientStack.Continuation.child]
      | some left =>
        cases split with
        | zero =>
          simp [advance, state, modulus, combine, parent, returning,
            CoefficientStackEncoding.cast, castContinuation, ResidueArithmetic.add_cast, ResidueArithmetic.mul_cast,
            SpanCoefficientStack.step, SpanCoefficientStack.returning,
            SpanCoefficientStack.Continuation.parent]
        | succ split =>
          simp [advance, state, modulus, combine, child, evaluating,
            CoefficientStackEncoding.cast, castContinuation, ResidueArithmetic.add_cast, ResidueArithmetic.mul_cast,
            SpanCoefficientStack.step, SpanCoefficientStack.evaluating,
            SpanCoefficientStack.Continuation.child]

/-- Factor data are irrelevant outside occupied leaf evaluation. A caller may
use constant dummy fields during descent, convolution, and terminal returns. -/
theorem advance_factor_irrelevant (p count a multiplicity a' multiplicity' : ℕ)
    (s : RawState)
    (inactive : ¬ (s.result = none ∧ s.request.height = 0 ∧ s.request.start < count)) :
    advance (p, count, a, multiplicity, s) = advance (p, count, a', multiplicity', s) := by
  rcases s with ⟨⟨height, start, degree, span⟩, result, stack⟩
  cases result with
  | some value => simp [advance, state, modulus]
  | none =>
    cases height with
    | succ height => simp [advance, state]
    | zero =>
      have outside : ¬ start < count := by simpa using inactive
      simp [advance, state, leaf, CoefficientTransition.count, modulus, outside]
      rfl

/-- Demand-driven refinement: only an occupied leaf evaluation requires the
current factor pair. The choice of canonical factor representatives in the
proof is a semantic witness, never an executing lookup or allocation. -/
theorem advance_refines_on_demand (p count a multiplicity : ℕ) [Fact p.Prime]
    (s : RawState) (factor : IntervalCoefficients.Factors p)
    (reads : s.result = none → s.request.height = 0 → s.request.start < count →
      factor s.request.start = ((a : ZMod p), multiplicity)) :
    CoefficientStackEncoding.cast p (advance (p, count, a, multiplicity, s)) =
      (SpanCoefficientStack.step factor count (CoefficientStackEncoding.cast p s)).getD
        (CoefficientStackEncoding.cast p s) := by
  by_cases active : s.result = none ∧ s.request.height = 0 ∧ s.request.start < count
  · exact advance_refines p count a multiplicity s factor
      (fun occupied => reads active.1 active.2.1 occupied)
  · rw [advance_factor_irrelevant p count a multiplicity
      (factor s.request.start).1.val (factor s.request.start).2 s active]
    apply advance_refines
    intro _
    simp only [ZMod.natCast_zmod_val, Prod.mk.eta]

end NtimeDspace.CoefficientTransition

