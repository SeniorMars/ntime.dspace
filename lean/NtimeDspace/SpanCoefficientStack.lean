import NtimeDspace.CoefficientStack

/-!
# Coefficient continuations with explicit interval spans

The executable transition stores the binary interval span. It halves that
register when descending, adds it when selecting the right child, and doubles
it when returning to a parent. In particular, no transition exponentiates a
possibly malformed binary height register. Powers occur only in the legacy
specification and its well-formedness proofs.

This is still an arithmetic transition system: field operations and the indexed
coefficient leaf remain atomic. The unconditional register bounds below include
malformed states; they are not a compiler or a work-tape bound for these atoms.
-/

namespace NtimeDspace.SpanCoefficientStack

open IntervalCoefficients

variable {p : ℕ} [Fact p.Prime]

structure Request where
  height : ℕ
  start : ℕ
  degree : ℕ
  span : ℕ
  deriving DecidableEq

structure Continuation (p : ℕ) where
  height : ℕ
  start : ℕ
  degree : ℕ
  split : ℕ
  span : ℕ
  accumulator : ZMod p
  savedLeft : Option (ZMod p)
  deriving DecidableEq

def Continuation.parent (frame : Continuation p) : Request :=
  ⟨frame.height + 1, frame.start, frame.degree, 2 * frame.span⟩

def Continuation.child (frame : Continuation p) : Request :=
  match frame.savedLeft with
  | none => ⟨frame.height, frame.start, frame.split, frame.span⟩
  | some _ => ⟨frame.height, frame.start + frame.span, frame.degree - frame.split, frame.span⟩

structure State (p : ℕ) where
  request : Request
  result : Option (ZMod p)
  stack : List (Continuation p)
  deriving DecidableEq

def evaluating (request : Request) (stack : List (Continuation p)) : State p :=
  ⟨request, none, stack⟩

def returning (request : Request) (value : ZMod p) (stack : List (Continuation p)) : State p :=
  ⟨request, some value, stack⟩

/-- A total transition on arbitrary register contents. Outside the atomic leaf,
its natural-number operations are comparison, decrement, addition, halving, and
doubling. -/
def step (factor : Factors p) (count : ℕ) (state : State p) : Option (State p) :=
  match state.result with
  | none =>
    match state.request.height with
    | 0 => some (returning state.request
        (coefficient factor count 0 state.request.start state.request.degree) state.stack)
    | height + 1 =>
      let frame : Continuation p :=
        ⟨height, state.request.start, state.request.degree, state.request.degree,
          state.request.span / 2, 0, none⟩
      some (evaluating frame.child (frame :: state.stack))
  | some value =>
    match state.stack with
    | [] => none
    | frame :: rest =>
      match frame.savedLeft with
      | none =>
        let next := { frame with savedLeft := some value }
        some (evaluating next.child (next :: rest))
      | some left =>
        let acc := left * value + frame.accumulator
        match frame.split with
        | 0 => some (returning frame.parent acc rest)
        | split + 1 =>
          let next := { frame with split := split, accumulator := acc, savedLeft := none }
          some (evaluating next.child (next :: rest))

def Request.erase (request : Request) : IntervalCoefficients.Request :=
  ⟨request.height, request.start, request.degree⟩

def Continuation.erase (frame : Continuation p) : CoefficientStack.Continuation p :=
  ⟨frame.height, frame.start, frame.degree, frame.split, frame.accumulator, frame.savedLeft⟩

def State.erase (state : State p) : CoefficientStack.State p :=
  ⟨state.request.erase, state.result, state.stack.map Continuation.erase⟩

/-- Specification embedding, never called by `step`. The caller supplies the
initial span separately, with a proof that it has this value. -/
def Request.expand (request : IntervalCoefficients.Request) : Request :=
  ⟨request.height, request.start, request.degree, 2 ^ request.height⟩

def Continuation.expand (frame : CoefficientStack.Continuation p) : Continuation p :=
  ⟨frame.height, frame.start, frame.degree, frame.split, 2 ^ frame.height,
    frame.accumulator, frame.savedLeft⟩

def State.expand (state : CoefficientStack.State p) : State p :=
  ⟨Request.expand state.request, state.result, state.stack.map Continuation.expand⟩

def WellFormed (state : State p) : Prop := State.expand state.erase = state

omit [Fact p.Prime] in
theorem erase_expand (state : CoefficientStack.State p) : (State.expand state).erase = state := by
  rcases state with ⟨request, result, stack⟩
  simp [State.expand, State.erase, Request.expand, Request.erase,
    Continuation.expand, Continuation.erase, Function.comp_def]

omit [Fact p.Prime] in
theorem expand_wellFormed (state : CoefficientStack.State p) : WellFormed (State.expand state) := by
  simp [WellFormed, erase_expand]

omit [Fact p.Prime] in
theorem wellFormed_iff (state : State p) : WellFormed state ↔
    state.request.span = 2 ^ state.request.height ∧
      ∀ frame ∈ state.stack, frame.span = 2 ^ frame.height := by
  rcases state with ⟨⟨height, start, degree, span⟩, result, stack⟩
  have frames : stack.map (fun frame => Continuation.expand frame.erase) = stack ↔
      ∀ frame ∈ stack, frame.span = 2 ^ frame.height := by
    induction stack with
    | nil => simp
    | cons frame rest ih =>
      have head : Continuation.expand frame.erase = frame ↔ frame.span = 2 ^ frame.height := by
        cases frame
        simp [Continuation.expand, Continuation.erase, eq_comm]
      simp only [List.map_cons, List.cons.injEq, head, ih, List.forall_mem_cons]
  change (State.mk ⟨height, start, degree, 2 ^ height⟩ result
    (stack.map Continuation.erase |>.map Continuation.expand) =
    State.mk ⟨height, start, degree, span⟩ result stack) ↔ _
  simp only [State.mk.injEq, Request.mk.injEq, true_and, List.map_map,
    Function.comp_def, frames]
  tauto

/-- Exact agreement of the two operational transitions on canonical states. -/
theorem step_expand (factor : Factors p) (count : ℕ) (state : CoefficientStack.State p) :
    step factor count (State.expand state) =
      (CoefficientStack.step factor count state).map State.expand := by
  rcases state with ⟨⟨height, start, degree⟩, result, stack⟩
  cases result with
  | none =>
    cases height with
    | zero => rfl
    | succ height =>
      simp [step, CoefficientStack.step, State.expand, Request.expand, Continuation.expand,
        Continuation.child, CoefficientStack.Continuation.child, evaluating,
        CoefficientStack.evaluating, pow_succ]
  | some value =>
    cases stack with
    | nil => rfl
    | cons frame rest =>
      rcases frame with ⟨height', start', degree', split, accumulator, saved⟩
      cases saved with
      | none => rfl
      | some left =>
        cases split with
        | zero =>
          simp [step, CoefficientStack.step, State.expand, Request.expand, Continuation.expand,
            Continuation.parent, CoefficientStack.Continuation.parent, returning,
            CoefficientStack.returning, pow_succ, Nat.mul_comm]
        | succ split => rfl

theorem step_refines (factor : Factors p) (count : ℕ) {before after : State p}
    (valid : WellFormed before) (next : step factor count before = some after) :
    CoefficientStack.step factor count before.erase = some after.erase ∧ WellFormed after := by
  rw [← valid, step_expand] at next
  cases legacy : CoefficientStack.step factor count before.erase with
  | none => simp [legacy] at next
  | some state =>
    simp only [legacy, Option.map_some, Option.some.injEq] at next
    subst after
    exact ⟨by rw [erase_expand], expand_wellFormed state⟩

def run (factor : Factors p) (count : ℕ) : ℕ → State p → State p
  | 0, state => state
  | fuel + 1, state =>
      match step factor count state with
      | none => state
      | some next => run factor count fuel next

theorem run_expand (factor : Factors p) (count fuel : ℕ) (state : CoefficientStack.State p) :
    run factor count fuel (State.expand state) =
      State.expand (CoefficientStack.run factor count fuel state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [run, step_expand, CoefficientStack.run]
    cases CoefficientStack.step factor count state <;> simp [ih]

theorem run_refines (factor : Factors p) (count fuel : ℕ) (state : State p)
    (valid : WellFormed state) :
    (run factor count fuel state).erase = CoefficientStack.run factor count fuel state.erase ∧
      WellFormed (run factor count fuel state) := by
  have same : run factor count fuel state =
      State.expand (CoefficientStack.run factor count fuel state.erase) :=
    (congrArg (run factor count fuel) valid.symm).trans
      (run_expand factor count fuel state.erase)
  rw [same]
  exact ⟨erase_expand _, expand_wellFormed _⟩

/-- Correct scalar answer, with the initial binary span supplied by the caller. -/
theorem terminates (factor : Factors p) (count : ℕ) (root : Request)
    (span : root.span = 2 ^ root.height) :
    ∃ fuel, run factor count fuel (evaluating root []) =
      returning root (coefficient factor count root.height root.start root.degree) [] := by
  obtain ⟨fuel, done⟩ := CoefficientStack.terminates factor count root.height root.start root.degree
  refine ⟨fuel, ?_⟩
  have initial : evaluating root ([] : List (Continuation p)) =
      State.expand (CoefficientStack.evaluating root.erase []) := by
    cases root
    simp_all [evaluating, State.expand, CoefficientStack.evaluating, Request.expand, Request.erase]
  rw [initial, run_expand]
  change State.expand (CoefficientStack.run factor count fuel
    (CoefficientStack.evaluating ⟨root.height, root.start, root.degree⟩ [])) = _
  rw [done]
  cases root
  simp_all [returning, State.expand, CoefficientStack.returning, Request.expand]

/-- Every actual prefix has bounded stack depth, interval endpoints, degrees,
and stored spans. No power needs to be computed to read any of these registers. -/
theorem run_bounds (factor : Factors p) (count fuel : ℕ) (root : Request)
    (span : root.span = 2 ^ root.height) :
    let state := run factor count fuel (evaluating root [])
    WellFormed state ∧ state.stack.length ≤ root.height ∧
      state.request.height ≤ root.height ∧ root.start ≤ state.request.start ∧
      state.request.start + state.request.span ≤ root.start + root.span ∧
      state.request.degree ≤ root.degree ∧
      ∀ frame ∈ state.stack,
        frame.height < root.height ∧ frame.start < root.start + root.span ∧
          frame.span ≤ root.span ∧ frame.degree ≤ root.degree ∧ frame.split ≤ frame.degree := by
  have initial : evaluating root ([] : List (Continuation p)) =
      State.expand (CoefficientStack.evaluating root.erase []) := by
    cases root
    simp_all [evaluating, State.expand, CoefficientStack.evaluating, Request.expand, Request.erase]
  dsimp only
  rw [initial, run_expand]
  let old := CoefficientStack.run factor count fuel (CoefficientStack.evaluating root.erase [])
  obtain ⟨depth, bounds, frames⟩ := CoefficientStack.reachable_bounds factor count root.erase old
    (CoefficientStack.run_executes factor count fuel _)
  refine ⟨expand_wellFormed old, ?_, bounds.1, bounds.2.1, ?_, bounds.2.2.2, ?_⟩
  · simpa [State.expand, old, Request.erase] using depth
  · simpa [State.expand, Request.expand, Request.erase, span, old] using bounds.2.2.1
  · intro frame member
    change frame ∈ old.stack.map Continuation.expand at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨height, start, degree, split⟩ := frames original originalMember
    exact ⟨height, by simpa [Continuation.expand, Request.erase, span] using start,
      by simpa [Continuation.expand, Request.erase, span] using
        (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_of_lt height)), degree, split⟩

/-- Bounds on every natural-number field, with no structural validity premise. -/
def Request.Bounded (bound : ℕ) (request : Request) : Prop :=
  request.height ≤ bound ∧ request.start ≤ bound ∧ request.degree ≤ bound ∧ request.span ≤ bound

def Continuation.Bounded (bound : ℕ) (frame : Continuation p) : Prop :=
  frame.height ≤ bound ∧ frame.start ≤ bound ∧ frame.degree ≤ bound ∧
    frame.split ≤ bound ∧ frame.span ≤ bound

def State.Bounded (bound : ℕ) (state : State p) : Prop :=
  state.request.Bounded bound ∧ ∀ frame ∈ state.stack, frame.Bounded bound

omit [Fact p.Prime] in
theorem Request.Bounded.mono {a b : ℕ} {request : Request}
    (bounded : request.Bounded a) (le : a ≤ b) : request.Bounded b := by
  unfold Request.Bounded at *
  omega

omit [Fact p.Prime] in
theorem Continuation.Bounded.mono {a b : ℕ} {frame : Continuation p}
    (bounded : frame.Bounded a) (le : a ≤ b) : frame.Bounded b := by
  unfold Continuation.Bounded at *
  omega

/-- A global, including malformed-state, output-size bound for the control
transition. At most one frame is pushed and every natural register remains at
most twice the preceding bound plus one. Scalar values stay in `ZMod p` by type.
This removes the exponential-height output-size problem without claiming costs
for the arithmetic or factor-access atoms. -/
theorem step_bounded (factor : Factors p) (count bound : ℕ) {before after : State p}
    (bounded : before.Bounded bound) (next : step factor count before = some after) :
    after.Bounded (2 * bound + 1) ∧ after.stack.length ≤ before.stack.length + 1 := by
  rcases before with ⟨⟨height, start, degree, span⟩, result, stack⟩
  rcases bounded with ⟨requestBound, stackBound⟩
  have requestMono := requestBound.mono (by omega : bound ≤ 2 * bound + 1)
  have stackMono : ∀ frame ∈ stack, frame.Bounded (2 * bound + 1) :=
    fun frame member => (stackBound frame member).mono (by omega)
  cases result with
  | none =>
    cases height with
    | zero =>
      cases Option.some.inj next
      exact ⟨⟨requestMono, stackMono⟩, by simp [returning]⟩
    | succ height =>
      cases Option.some.inj next
      refine ⟨⟨?_, ?_⟩, by simp [evaluating]⟩
      · dsimp [Continuation.child, evaluating, Request.Bounded] at *
        omega
      · intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · dsimp [Continuation.Bounded]
          dsimp [Request.Bounded] at requestBound
          omega
        · exact stackMono frame member
  | some value =>
    cases stack with
    | nil => simp [step] at next
    | cons frame rest =>
      have frameBound := stackBound frame (by simp)
      have restBound : ∀ frame ∈ rest, frame.Bounded (2 * bound + 1) :=
        fun frame member => stackMono frame (by simp [member])
      rcases frame with ⟨height', start', degree', split, span', accumulator, saved⟩
      cases saved with
      | none =>
        cases Option.some.inj next
        refine ⟨⟨?_, ?_⟩, by simp [evaluating]⟩
        · dsimp [Continuation.child, evaluating, Request.Bounded]
          dsimp [Continuation.Bounded] at frameBound
          omega
        · intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · dsimp [Continuation.Bounded]
            dsimp [Continuation.Bounded] at frameBound
            omega
          · exact restBound frame member
      | some left =>
        cases split with
        | zero =>
          cases Option.some.inj next
          refine ⟨⟨?_, restBound⟩, by simp only [returning, List.length_cons]; omega⟩
          dsimp [Continuation.parent, returning, Request.Bounded]
          dsimp [Continuation.Bounded] at frameBound
          omega
        | succ split =>
          cases Option.some.inj next
          refine ⟨⟨?_, ?_⟩, by simp [evaluating]⟩
          · dsimp [Continuation.child, evaluating, Request.Bounded]
            dsimp [Continuation.Bounded] at frameBound
            omega
          · intro frame member
            rcases List.mem_cons.mp member with rfl | member
            · dsimp [Continuation.Bounded]
              dsimp [Continuation.Bounded] at frameBound
              omega
            · exact restBound frame member

/-- If all natural fields initially fit in `bits` binary digits, a single
transition needs at most one additional digit, even on malformed states. -/
theorem step_bit_width (factor : Factors p) (count bits : ℕ) {before after : State p}
    (bounded : before.Bounded (2 ^ bits - 1))
    (next : step factor count before = some after) :
    after.Bounded (2 ^ (bits + 1) - 1) ∧
      after.stack.length ≤ before.stack.length + 1 := by
  have same : 2 * (2 ^ bits - 1) + 1 = 2 ^ (bits + 1) - 1 := by
    have positive := Nat.two_pow_pos bits
    rw [pow_succ]
    omega
  simpa only [same] using step_bounded factor count (2 ^ bits - 1) bounded next

/-- Exact bounded registers, including the explicitly stored span. Each `Fin`
field below fits in `bits` binary digits. -/
abbrev EncodedRequest (bits : ℕ) :=
  Fin (2 ^ bits) × Fin (2 ^ bits) × Fin (2 ^ bits) × Fin (2 ^ bits)

abbrev EncodedContinuation (bits p : ℕ) :=
  Fin (2 ^ bits) × Fin (2 ^ bits) × Fin (2 ^ bits) × Fin (2 ^ bits) ×
    Fin (2 ^ bits) × ZMod p × Option (ZMod p)

def decodeRequest {bits : ℕ} (encoded : EncodedRequest bits) : Request :=
  ⟨encoded.1.val, encoded.2.1.val, encoded.2.2.1.val, encoded.2.2.2.val⟩

def decodeContinuation {bits : ℕ} (encoded : EncodedContinuation bits p) : Continuation p :=
  ⟨encoded.1.val, encoded.2.1.val, encoded.2.2.1.val, encoded.2.2.2.1.val,
    encoded.2.2.2.2.1.val, encoded.2.2.2.2.2.1, encoded.2.2.2.2.2.2⟩

def encodeRequest (bits : ℕ) (request : Request)
    (bounded : request.Bounded (2 ^ bits - 1)) : EncodedRequest bits :=
  (⟨request.height, by have := Nat.two_pow_pos bits; have := bounded.1; omega⟩,
   ⟨request.start, by have := Nat.two_pow_pos bits; have := bounded.2.1; omega⟩,
   ⟨request.degree, by have := Nat.two_pow_pos bits; have := bounded.2.2.1; omega⟩,
   ⟨request.span, by have := Nat.two_pow_pos bits; have := bounded.2.2.2; omega⟩)

def encodeContinuation (bits : ℕ) (frame : Continuation p)
    (bounded : frame.Bounded (2 ^ bits - 1)) : EncodedContinuation bits p :=
  (⟨frame.height, by have := Nat.two_pow_pos bits; have := bounded.1; omega⟩,
   ⟨frame.start, by have := Nat.two_pow_pos bits; have := bounded.2.1; omega⟩,
   ⟨frame.degree, by have := Nat.two_pow_pos bits; have := bounded.2.2.1; omega⟩,
   ⟨frame.split, by have := Nat.two_pow_pos bits; have := bounded.2.2.2.1; omega⟩,
   ⟨frame.span, by have := Nat.two_pow_pos bits; have := bounded.2.2.2.2; omega⟩,
   frame.accumulator, frame.savedLeft)

omit [Fact p.Prime] in
theorem decode_encodeRequest (bits : ℕ) (request : Request)
    (bounded : request.Bounded (2 ^ bits - 1)) :
    decodeRequest (encodeRequest bits request bounded) = request := rfl

omit [Fact p.Prime] in
theorem decode_encodeContinuation (bits : ℕ) (frame : Continuation p)
    (bounded : frame.Bounded (2 ^ bits - 1)) :
    decodeContinuation (encodeContinuation bits frame bounded) = frame := rfl

structure EncodedState (bits depth p : ℕ) where
  request : EncodedRequest bits
  result : Option (ZMod p)
  stack : List (EncodedContinuation bits p)
  stackLength : stack.length ≤ depth

def decodeState {bits depth : ℕ} (encoded : EncodedState bits depth p) : State p :=
  ⟨decodeRequest encoded.request, encoded.result, encoded.stack.map decodeContinuation⟩

omit [Fact p.Prime] in
/-- Exact finite-register representation for arbitrary bounded states. It does
not require span/height consistency, split bounds, or a reachable-state premise. -/
theorem bounded_encodable (bits depth : ℕ) (state : State p)
    (bounded : state.Bounded (2 ^ bits - 1)) (length : state.stack.length ≤ depth) :
    ∃ encoded : EncodedState bits depth p, decodeState encoded = state := by
  let encode := fun frame : { frame // frame ∈ state.stack } =>
    encodeContinuation bits frame.val (bounded.2 frame.val frame.property)
  let stack := state.stack.attach.map encode
  have same : stack.map decodeContinuation = state.stack := by
    simp only [stack, List.map_map, Function.comp_def, encode, decode_encodeContinuation]
    simp
  refine ⟨⟨encodeRequest bits state.request bounded.1, state.result, stack, ?_⟩, ?_⟩
  · simpa [stack] using length
  · change State.mk state.request state.result (stack.map decodeContinuation) = state
    rw [same]

/-- Global one-step output encoding, including states with invalid heights or
spans. The output has at most one additional frame and one additional binary
digit per natural field; field elements remain in their original finite type. -/
theorem step_encodable (factor : Factors p) (count bits depth : ℕ)
    {before after : State p} (bounded : before.Bounded (2 ^ bits - 1))
    (length : before.stack.length ≤ depth) (next : step factor count before = some after) :
    ∃ encoded : EncodedState (bits + 1) (depth + 1) p, decodeState encoded = after := by
  obtain ⟨fields, stack⟩ := step_bit_width factor count bits bounded next
  exact bounded_encodable (bits + 1) (depth + 1) after fields (by omega)

theorem encodedContinuation_card (bits : ℕ) :
    Fintype.card (EncodedContinuation bits p) = (2 ^ bits) ^ 5 * p * (p + 1) := by
  simp only [EncodedContinuation, Fintype.card_prod, Fintype.card_fin,
    ZMod.card, Fintype.card_option]
  ring

end NtimeDspace.SpanCoefficientStack
