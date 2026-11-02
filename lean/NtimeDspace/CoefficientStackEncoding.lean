import NtimeDspace.SpanCoefficientStack
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Explicit binary serialization of coefficient-stack states

Raw field values are ordinary naturals, so the state type and its binary
encoding do not depend on the modulus. Right-nested pairs frame only their
first component; the stack is the concatenation of individually framed
continuations. No encoding repeatedly frames the entire remaining stack.

The encoding is an explicit injective `List Bool` representation. Its exact
length and additive bounds account for every stored natural, option tag, and
frame delimiter. These results do not assert a machine implementation of the
state transition or its leaf accessor.
-/

namespace NtimeDspace.CoefficientStackEncoding

open Turing Turing.MultiTapeTM

abbrev RawRequest := SpanCoefficientStack.Request

structure RawContinuation where
  height : ℕ
  start : ℕ
  degree : ℕ
  split : ℕ
  span : ℕ
  accumulator : ℕ
  savedLeft : Option ℕ
  deriving DecidableEq

structure RawState where
  request : RawRequest
  result : Option ℕ
  stack : List RawContinuation
  deriving DecidableEq

abbrev RequestData := ℕ × ℕ × ℕ × ℕ
abbrev ContinuationData := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Option ℕ
abbrev StateData := RawRequest × Option ℕ × List RawContinuation

def requestData : RawRequest ↪ RequestData :=
  ⟨fun r => (r.height, r.start, r.degree, r.span), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, SpanCoefficientStack.Request.mk.injEq] using same⟩

def continuationData : RawContinuation ↪ ContinuationData :=
  ⟨fun r => (r.height, r.start, r.degree, r.split, r.span, r.accumulator, r.savedLeft), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, RawContinuation.mk.injEq] using same⟩

def stateData : RawState ↪ StateData :=
  ⟨fun s => (s.request, s.result, s.stack), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, RawState.mk.injEq] using same⟩

def encRequest : RawRequest ↪ List Bool :=
  requestData.trans (encPair encNat (encPair encNat (encPair encNat encNat)))

def encContinuation : RawContinuation ↪ List Bool :=
  continuationData.trans (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat (encPair encNat (encPair encNat (encOption encNat)))))))

def encState : RawState ↪ List Bool :=
  stateData.trans (encPair encRequest (encPair (encOption encNat) (encList encContinuation)))

theorem encState_injective : Function.Injective encState := encState.injective

/-- Sum of payload bits in an optional natural, excluding its presence tag. -/
def optionWidth : Option ℕ → ℕ
  | none => 0
  | some value => (encNat value).length

def optionTag : Option ℕ → ℕ
  | none => 0
  | some _ => 1

def requestWidth (request : RawRequest) : ℕ :=
  (encNat request.height).length + (encNat request.start).length +
    (encNat request.degree).length + (encNat request.span).length

def continuationWidth (frame : RawContinuation) : ℕ :=
  (encNat frame.height).length + (encNat frame.start).length +
    (encNat frame.degree).length + (encNat frame.split).length +
    (encNat frame.span).length + (encNat frame.accumulator).length + optionWidth frame.savedLeft

def registerWidth (state : RawState) : ℕ :=
  requestWidth state.request + optionWidth state.result +
    (state.stack.map continuationWidth).sum

theorem option_length (value : Option ℕ) :
    (encOption encNat value).length = optionWidth value + optionTag value := by
  cases value <;> simp [optionWidth, optionTag]

theorem option_length_le (value : Option ℕ) :
    (encOption encNat value).length ≤ optionWidth value + 1 := by
  cases value <;> simp [optionWidth]

theorem encRequest_length (request : RawRequest) :
    (encRequest request).length =
      2 * (encNat request.height).length + 2 * (encNat request.start).length +
      2 * (encNat request.degree).length + (encNat request.span).length + 3 := by
  change (encPair encNat (encPair encNat (encPair encNat encNat))
    (request.height, request.start, request.degree, request.span)).length = _
  simp only [length_encPair]
  omega

theorem encContinuation_length (frame : RawContinuation) :
    (encContinuation frame).length =
      2 * ((encNat frame.height).length + (encNat frame.start).length +
        (encNat frame.degree).length + (encNat frame.split).length +
        (encNat frame.span).length + (encNat frame.accumulator).length) +
      optionWidth frame.savedLeft + optionTag frame.savedLeft + 6 := by
  change (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat (encPair encNat (encPair encNat (encOption encNat))))))
    (frame.height, frame.start, frame.degree, frame.split, frame.span,
      frame.accumulator, frame.savedLeft)).length = _
  simp only [length_encPair, option_length]
  omega

theorem encStack_length (stack : List RawContinuation) :
    (encList encContinuation stack).length =
      2 * (stack.map fun frame => (encContinuation frame).length).sum + stack.length := by
  induction stack with
  | nil => simp
  | cons frame rest ih =>
    simp only [encList_cons, List.length_append, length_frame, ih,
      List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem encState_length (state : RawState) :
    (encState state).length = 2 * (encRequest state.request).length +
      2 * (optionWidth state.result + optionTag state.result) +
      2 * (state.stack.map fun frame => (encContinuation frame).length).sum +
      state.stack.length + 2 := by
  change (encPair encRequest (encPair (encOption encNat) (encList encContinuation))
    (state.request, state.result, state.stack)).length = _
  simp only [length_encPair, option_length, encStack_length]
  omega

theorem encRequest_length_le (request : RawRequest) :
    (encRequest request).length ≤ 2 * requestWidth request + 3 := by
  rw [encRequest_length]
  unfold requestWidth
  omega

theorem encContinuation_length_le (frame : RawContinuation) :
    (encContinuation frame).length ≤ 2 * continuationWidth frame + 7 := by
  have tag : optionTag frame.savedLeft ≤ 1 := by cases frame.savedLeft <;> simp [optionTag]
  rw [encContinuation_length]
  unfold continuationWidth
  omega

/-- Linear additive serialization overhead. Each continuation contributes a
fixed delimiter cost, rather than multiplying the encoding of its suffix. -/
theorem encState_length_le (state : RawState) :
    (encState state).length ≤ 4 * registerWidth state + 15 * state.stack.length + 10 := by
  have request := encRequest_length_le state.request
  have tag : optionTag state.result ≤ 1 := by cases state.result <;> simp [optionTag]
  have frames : (state.stack.map fun frame => (encContinuation frame).length).sum ≤
      2 * (state.stack.map continuationWidth).sum + 7 * state.stack.length := by
    induction state.stack with
    | nil => simp
    | cons frame rest ih =>
      have bound := encContinuation_length_le frame
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  rw [encState_length]
  unfold registerWidth
  omega

def castContinuation (p : ℕ) (frame : RawContinuation) : SpanCoefficientStack.Continuation p :=
  ⟨frame.height, frame.start, frame.degree, frame.split, frame.span,
    (frame.accumulator : ZMod p), frame.savedLeft.map (fun value => (value : ZMod p))⟩

def cast (p : ℕ) (state : RawState) : SpanCoefficientStack.State p :=
  ⟨state.request, state.result.map (fun value => (value : ZMod p)),
    state.stack.map (castContinuation p)⟩

def liftContinuation {p : ℕ} (frame : SpanCoefficientStack.Continuation p) : RawContinuation :=
  ⟨frame.height, frame.start, frame.degree, frame.split, frame.span,
    frame.accumulator.val, frame.savedLeft.map ZMod.val⟩

def lift {p : ℕ} (state : SpanCoefficientStack.State p) : RawState :=
  ⟨state.request, state.result.map ZMod.val, state.stack.map liftContinuation⟩

theorem cast_liftContinuation {p : ℕ} [NeZero p] (frame : SpanCoefficientStack.Continuation p) :
    castContinuation p (liftContinuation frame) = frame := by
  cases frame with
  | mk height start degree split span accumulator saved =>
    cases saved <;> simp [castContinuation, liftContinuation]

theorem cast_lift {p : ℕ} [NeZero p] (state : SpanCoefficientStack.State p) :
    cast p (lift state) = state := by
  rcases state with ⟨request, result, stack⟩
  have frames : (stack.map liftContinuation).map (castContinuation p) = stack := by
    simp only [List.map_map, Function.comp_def, cast_liftContinuation]
    simp
  cases result <;> simp [cast, lift, frames]

/-- Canonical raw field representatives; all other registers are unrestricted. -/
def Canonical (p : ℕ) (state : RawState) : Prop :=
  (∀ value ∈ state.result, value < p) ∧
    ∀ frame ∈ state.stack, frame.accumulator < p ∧ ∀ value ∈ frame.savedLeft, value < p

theorem lift_canonical {p : ℕ} [NeZero p] (state : SpanCoefficientStack.State p) :
    Canonical p (lift state) := by
  constructor
  · intro value member
    obtain ⟨original, _, rfl⟩ := Option.mem_map.mp member
    exact original.val_lt
  · intro frame member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    refine ⟨original.accumulator.val_lt, ?_⟩
    intro value member
    obtain ⟨originalValue, _, rfl⟩ := Option.mem_map.mp member
    exact originalValue.val_lt

theorem lift_cast {p : ℕ} [NeZero p] (state : RawState) (canonical : Canonical p state) :
    lift (cast p state) = state := by
  have option {value : Option ℕ} (bounded : ∀ n ∈ value, n < p) :
      (value.map (fun n => (n : ZMod p))).map ZMod.val = value := by
    cases value with
    | none => rfl
    | some n => simp [ZMod.val_natCast, Nat.mod_eq_of_lt (bounded n (by simp))]
  have frames : (state.stack.map (castContinuation p)).map liftContinuation = state.stack := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id state.stack]
    apply List.map_congr_left
    intro frame member
    have bounded := canonical.2 frame member
    cases frame
    simp only [Function.comp_def, castContinuation, liftContinuation, ZMod.val_natCast,
      Nat.mod_eq_of_lt bounded.1, option bounded.2, id_eq]
  simp only [cast, lift, option canonical.1, frames]

/-- Numeric bounds on every raw payload; no reachability or valid-span premise. -/
def ValuesBounded (bound : ℕ) (state : RawState) : Prop :=
  state.request.Bounded bound ∧ (∀ value ∈ state.result, value ≤ bound) ∧
    ∀ frame ∈ state.stack,
      frame.height ≤ bound ∧ frame.start ≤ bound ∧ frame.degree ≤ bound ∧
      frame.split ≤ bound ∧ frame.span ≤ bound ∧ frame.accumulator ≤ bound ∧
      ∀ value ∈ frame.savedLeft, value ≤ bound

theorem optionWidth_le {value : Option ℕ} {bound : ℕ}
    (bounded : ∀ n ∈ value, n ≤ bound) : optionWidth value ≤ bound.log2 + 1 := by
  cases value with
  | none => simp [optionWidth]
  | some n => exact length_encNat_le_log2 (bounded n (by simp))

/-- A direct serialized bit bound from numeric register bounds. -/
theorem encState_length_of_values (state : RawState) (bound : ℕ)
    (bounded : ValuesBounded bound state) :
    (encState state).length ≤ (state.stack.length + 1) * (28 * (bound.log2 + 1) + 15) := by
  have request : requestWidth state.request ≤ 4 * (bound.log2 + 1) := by
    obtain ⟨height, start, degree, span⟩ := bounded.1
    have h := length_encNat_le_log2 height
    have s := length_encNat_le_log2 start
    have d := length_encNat_le_log2 degree
    have w := length_encNat_le_log2 span
    unfold requestWidth
    omega
  have result := optionWidth_le bounded.2.1
  have frames : (state.stack.map continuationWidth).sum ≤
      state.stack.length * (7 * (bound.log2 + 1)) := by
    have each (frame : RawContinuation) (member : frame ∈ state.stack) :
        continuationWidth frame ≤ 7 * (bound.log2 + 1) := by
      obtain ⟨height, start, degree, split, span, accumulator, saved⟩ := bounded.2.2 frame member
      have h := length_encNat_le_log2 height
      have s := length_encNat_le_log2 start
      have d := length_encNat_le_log2 degree
      have j := length_encNat_le_log2 split
      have w := length_encNat_le_log2 span
      have a := length_encNat_le_log2 accumulator
      have v := optionWidth_le saved
      unfold continuationWidth
      omega
    suffices general : ∀ stack : List RawContinuation,
        (∀ frame ∈ stack, continuationWidth frame ≤ 7 * (bound.log2 + 1)) →
        (stack.map continuationWidth).sum ≤ stack.length * (7 * (bound.log2 + 1)) from
      general state.stack each
    intro stack
    induction stack with
    | nil => simp
    | cons frame rest ih =>
      intro every
      have head := every frame (by simp)
      have tail := ih (fun f member => every f (by simp [member]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have encoded := encState_length_le state
  unfold registerWidth at encoded
  nlinarith

/-- A uniform numeric envelope for a reachable typed state. -/
def runRegisterBound (root : RawRequest) (p : ℕ) : ℕ :=
  max root.height (max (root.start + root.span) (max root.degree p))

theorem run_values_bounded {p : ℕ} [Fact p.Prime] (factor : IntervalCoefficients.Factors p)
    (count fuel : ℕ) (root : RawRequest) (span : root.span = 2 ^ root.height) :
    ValuesBounded (runRegisterBound root p)
      (lift (SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root []))) := by
  let state := SpanCoefficientStack.run factor count fuel (SpanCoefficientStack.evaluating root [])
  obtain ⟨_, _, height, start, finish, degree, frames⟩ :=
    SpanCoefficientStack.run_bounds factor count fuel root span
  have hbound : root.height ≤ runRegisterBound root p := le_max_left _ _
  have endpoint : root.start + root.span ≤ runRegisterBound root p :=
    (le_max_left _ _).trans (le_max_right _ _)
  have dbound : root.degree ≤ runRegisterBound root p :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have pbound : p ≤ runRegisterBound root p :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  change ValuesBounded (runRegisterBound root p) (lift state)
  refine ⟨⟨height.trans hbound, ?_, degree.trans dbound, ?_⟩, ?_, ?_⟩
  · exact (Nat.le_add_right state.request.start state.request.span).trans (finish.trans endpoint)
  · exact (Nat.le_add_left state.request.span state.request.start).trans (finish.trans endpoint)
  · intro value member
    obtain ⟨original, _, rfl⟩ := Option.mem_map.mp member
    exact (Nat.le_of_lt original.val_lt).trans pbound
  · intro frame member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨height, start, width, degree, split⟩ := frames original originalMember
    refine ⟨(Nat.le_of_lt height).trans hbound, (Nat.le_of_lt start).trans endpoint,
      degree.trans dbound, split.trans (degree.trans dbound), ?_,
      (Nat.le_of_lt original.accumulator.val_lt).trans pbound, ?_⟩
    · exact width.trans ((Nat.le_add_left root.span root.start).trans endpoint)
    · intro value member
      obtain ⟨originalValue, _, rfl⟩ := Option.mem_map.mp member
      exact (Nat.le_of_lt originalValue.val_lt).trans pbound

/-- Every actual execution prefix has a concrete serialized representation
with logarithmic register widths and at most the root height continuations. -/
theorem run_encoding_length {p : ℕ} [Fact p.Prime] (factor : IntervalCoefficients.Factors p)
    (count fuel : ℕ) (root : RawRequest) (span : root.span = 2 ^ root.height) :
    (encState (lift (SpanCoefficientStack.run factor count fuel
      (SpanCoefficientStack.evaluating root [])))).length ≤
      (root.height + 1) * (28 * ((runRegisterBound root p).log2 + 1) + 15) := by
  have bounded := run_values_bounded factor count fuel root span
  have size := encState_length_of_values _ _ bounded
  have depth := (SpanCoefficientStack.run_bounds factor count fuel root span).2.1
  have length : (lift (SpanCoefficientStack.run factor count fuel
      (SpanCoefficientStack.evaluating root []))).stack.length ≤ root.height := by
    simpa [lift] using depth
  exact size.trans (Nat.mul_le_mul_right _ (by omega))

end NtimeDspace.CoefficientStackEncoding
