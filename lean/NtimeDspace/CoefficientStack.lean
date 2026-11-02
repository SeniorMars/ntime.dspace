import NtimeDspace.IntervalCoefficients

/-!
# Operational coefficient evaluation with a continuation stack

This small-step arithmetic evaluator computes indexed interval coefficients.
Its live data are a current request, an optional scalar result, and explicitly
stored convolution continuations. Each continuation stores its accumulator,
split index, and (only while evaluating the right child) the saved left result.

Field arithmetic and the indexed modular leaf are atomic here. This is not a
Turing-machine implementation or a work-tape theorem; in particular, the factor
accessor and its multiplicity register still require their own implementation.
-/

namespace NtimeDspace.CoefficientStack

open HermiteRecovery IntervalCoefficients

variable {p : ℕ} [Fact p.Prime]

/-- `height` is the child height. The parent height is therefore `height + 1`.
An absent saved result means that the left child is being evaluated. -/
structure Continuation (p : ℕ) where
  height : ℕ
  start : ℕ
  degree : ℕ
  split : ℕ
  accumulator : ZMod p
  savedLeft : Option (ZMod p)
  deriving DecidableEq

def Continuation.parent (frame : Continuation p) : Request :=
  ⟨frame.height + 1, frame.start, frame.degree⟩

def Continuation.child (frame : Continuation p) : Request :=
  match frame.savedLeft with
  | none => ⟨frame.height, frame.start, frame.split⟩
  | some _ => ⟨frame.height, frame.start + 2 ^ frame.height, frame.degree - frame.split⟩

structure State (p : ℕ) where
  request : Request
  result : Option (ZMod p)
  stack : List (Continuation p)
  deriving DecidableEq

def evaluating (request : Request) (stack : List (Continuation p)) : State p :=
  ⟨request, none, stack⟩

def returning (request : Request) (value : ZMod p) (stack : List (Continuation p)) : State p :=
  ⟨request, some value, stack⟩

/-- One transition, including explicit push, left-result save, split decrement,
and pop. Halting is exactly a returned result with an empty stack. -/
def step (factor : Factors p) (count : ℕ) (state : State p) : Option (State p) :=
  match state.result with
  | none =>
    match state.request.height with
    | 0 => some (returning state.request
        (coefficient factor count 0 state.request.start state.request.degree) state.stack)
    | height + 1 =>
      let frame : Continuation p :=
        ⟨height, state.request.start, state.request.degree, state.request.degree, 0, none⟩
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

/-- A finite sequence of actual transitions. No evaluation rule unfolds an
entire subtree in one step. -/
inductive Executes (factor : Factors p) (count : ℕ) : State p → State p → Prop
  | refl (state) : Executes factor count state state
  | cons {first second last}
      (next : step factor count first = some second)
      (rest : Executes factor count second last) : Executes factor count first last

theorem Executes.trans {factor : Factors p} {count : ℕ} {first middle last : State p}
    (left : Executes factor count first middle) (right : Executes factor count middle last) :
    Executes factor count first last := by
  induction left with
  | refl => exact right
  | cons next rest ih => exact .cons next (ih right)

theorem Executes.single {factor : Factors p} {count : ℕ} {first second : State p}
    (next : step factor count first = some second) : Executes factor count first second :=
  .cons next (.refl second)

/-- Operational refinement of interval recursion, for every surrounding
continuation stack and without algebraic validity or characteristic premises. -/
theorem evaluates_coefficient (factor : Factors p) (count height start degree : ℕ)
    (stack : List (Continuation p)) :
    Executes factor count (evaluating ⟨height, start, degree⟩ stack)
      (returning ⟨height, start, degree⟩ (coefficient factor count height start degree) stack) := by
  induction height generalizing start degree stack with
  | zero => exact Executes.single rfl
  | succ height ih =>
    let term := fun split => coefficient factor count height start split *
      coefficient factor count height (start + 2 ^ height) (degree - split)
    have loop (split : ℕ) (acc : ZMod p) :
        Executes factor count
          (evaluating ⟨height, start, split⟩
            (⟨height, start, degree, split, acc, none⟩ :: stack))
          (returning ⟨height + 1, start, degree⟩ (sumLoop term (split + 1) acc) stack) := by
      induction split generalizing acc with
      | zero =>
        refine (ih start 0 _).trans ?_
        refine .cons rfl ?_
        refine (ih (start + 2 ^ height) (degree - 0) _).trans ?_
        exact Executes.single rfl
      | succ split loop_ih =>
        refine (ih start (split + 1) _).trans ?_
        refine .cons rfl ?_
        refine (ih (start + 2 ^ height) (degree - (split + 1)) _).trans ?_
        exact .cons rfl (loop_ih (term (split + 1) + acc))
    exact .cons rfl (loop degree 0)

/-- Executable finite-step driver. A halted state remains unchanged. -/
def run (factor : Factors p) (count : ℕ) : ℕ → State p → State p
  | 0, state => state
  | steps + 1, state =>
      match step factor count state with
      | none => state
      | some next => run factor count steps next

theorem Executes.run {factor : Factors p} {count : ℕ} {first last : State p}
    (execution : Executes factor count first last) :
    ∃ steps, run factor count steps first = last := by
  induction execution with
  | refl => exact ⟨0, rfl⟩
  | cons next rest ih =>
    obtain ⟨steps, done⟩ := ih
    exact ⟨steps + 1, by simp only [CoefficientStack.run, next]; exact done⟩

/-- Every coefficient query reaches its scalar answer with an empty stack. -/
theorem terminates (factor : Factors p) (count height start degree : ℕ) :
    ∃ steps, run factor count steps (evaluating ⟨height, start, degree⟩ []) =
      returning ⟨height, start, degree⟩ (coefficient factor count height start degree) [] :=
  (evaluates_coefficient factor count height start degree []).run

omit [Fact p.Prime] in
theorem Continuation.child_relation (frame : Continuation p) (bounded : frame.split ≤ frame.degree) :
    Child frame.parent frame.child := by
  cases saved : frame.savedLeft with
  | none =>
    simpa only [Continuation.parent, Continuation.child, saved] using
      (Child.left frame.height frame.start frame.degree frame.split bounded)
  | some value =>
    simpa only [Continuation.parent, Continuation.child, saved] using
      (Child.right frame.height frame.start frame.degree frame.split bounded)

/-- The stored continuations are exactly the ancestors of the current request.
This invariant refers to the operational stack, including return states. -/
inductive Chain (root : Request) : Request → List (Continuation p) → Prop
  | root : Chain root root []
  | push {frame : Continuation p} {rest : List (Continuation p)}
      (bounded : frame.split ≤ frame.degree)
      (ancestors : Chain root frame.parent rest) :
      Chain root frame.child (frame :: rest)

omit [Fact p.Prime] in
theorem Chain.height_eq {root current : Request} {stack : List (Continuation p)}
    (chain : Chain root current stack) : current.height + stack.length = root.height := by
  induction chain with
  | root => simp
  | @push frame rest bounded ancestors ih =>
    have decrease := (frame.child_relation bounded).bounds.1
    simp only [List.length_cons]
    omega

omit [Fact p.Prime] in
theorem Chain.request_bounds {root current : Request} {stack : List (Continuation p)}
    (chain : Chain root current stack) :
    current.height ≤ root.height ∧ root.start ≤ current.start ∧
      current.start + 2 ^ current.height ≤ root.start + 2 ^ root.height ∧
      current.degree ≤ root.degree := by
  induction chain with
  | root => simp
  | @push frame rest bounded ancestors ih =>
    obtain ⟨height, start, finish, degree⟩ := (frame.child_relation bounded).bounds
    exact ⟨by omega, ih.2.1.trans start, finish.trans ih.2.2.1, degree.trans ih.2.2.2⟩

omit [Fact p.Prime] in
theorem Chain.frame_bounds {root current : Request} {stack : List (Continuation p)}
    (chain : Chain root current stack) (frame : Continuation p) (member : frame ∈ stack) :
    frame.height < root.height ∧ frame.start < root.start + 2 ^ root.height ∧
      frame.degree ≤ root.degree ∧ frame.split ≤ frame.degree := by
  induction chain with
  | root => simp at member
  | @push top rest bounded ancestors ih =>
    rcases List.mem_cons.mp member with same | member
    · subst frame
      obtain ⟨height, _, finish, degree⟩ := ancestors.request_bounds
      have positive := Nat.two_pow_pos top.parent.height
      change top.height + 1 ≤ root.height at height
      change top.start + 2 ^ top.parent.height ≤ _ at finish
      exact ⟨by omega, by omega, degree, bounded⟩
    · exact ih member

/-- Every transition preserves the exact continuation ancestry invariant. -/
theorem step_preserves_chain (factor : Factors p) (count : ℕ)
    {root : Request} {before after : State p}
    (chain : Chain root before.request before.stack)
    (next : step factor count before = some after) : Chain root after.request after.stack := by
  rcases before with ⟨request, result, stack⟩
  cases result with
  | none =>
    rcases request with ⟨height, start, degree⟩
    cases height with
    | zero =>
      have same := Option.some.inj next
      cases same
      exact chain
    | succ height =>
      have same := Option.some.inj next
      cases same
      exact .push (frame := ⟨height, start, degree, degree, 0, none⟩) le_rfl chain
  | some value =>
    cases stack with
    | nil => simp [step] at next
    | cons frame rest =>
      cases chain with
      | push bounded ancestors =>
        rcases frame with ⟨height, start, degree, split, acc, saved⟩
        cases saved with
        | none =>
          have same := Option.some.inj next
          cases same
          exact .push (frame := ⟨height, start, degree, split, acc, some value⟩) bounded ancestors
        | some left =>
          cases split with
          | zero =>
            have same := Option.some.inj next
            cases same
            exact ancestors
          | succ split =>
            have same := Option.some.inj next
            cases same
            exact .push (frame := ⟨height, start, degree, split, left * value + acc, none⟩)
              (by dsimp at bounded ⊢; omega) ancestors

theorem Executes.preserves_chain {factor : Factors p} {count : ℕ}
    {root : Request} {first last : State p}
    (execution : Executes factor count first last)
    (chain : Chain root first.request first.stack) : Chain root last.request last.stack := by
  induction execution with
  | refl => exact chain
  | cons next rest ih => exact ih (step_preserves_chain factor count chain next)

/-- The actual stack at every finite execution prefix has at most the root
height entries, and its current request and all saved fields stay bounded. -/
theorem reachable_bounds (factor : Factors p) (count : ℕ) (root : Request) (state : State p)
    (reachable : Executes factor count (evaluating root []) state) :
    state.stack.length ≤ root.height ∧
      (state.request.height ≤ root.height ∧ root.start ≤ state.request.start ∧
        state.request.start + 2 ^ state.request.height ≤ root.start + 2 ^ root.height ∧
        state.request.degree ≤ root.degree) ∧
      ∀ frame ∈ state.stack,
        frame.height < root.height ∧ frame.start < root.start + 2 ^ root.height ∧
          frame.degree ≤ root.degree ∧ frame.split ≤ frame.degree := by
  have chain := reachable.preserves_chain (.root : Chain root root [])
  have length := chain.height_eq
  exact ⟨by omega, chain.request_bounds, chain.frame_bounds⟩

/-- Each finite-step driver prefix is an execution prefix, including when its
fuel exceeds the number of transitions needed to halt. -/
theorem run_executes (factor : Factors p) (count steps : ℕ) (state : State p) :
    Executes factor count state (run factor count steps state) := by
  induction steps generalizing state with
  | zero => exact .refl state
  | succ steps ih =>
    cases next : step factor count state with
    | none => simpa only [run, next] using Executes.refl (factor := factor) (count := count) state
    | some nextState => simpa only [run, next] using Executes.cons next (ih nextState)

theorem run_stack_length_le (factor : Factors p) (count steps : ℕ) (root : Request) :
    (run factor count steps (evaluating root [])).stack.length ≤ root.height :=
  (reachable_bounds factor count root _ (run_executes factor count steps _)).1

abbrev EncodedContinuation (height capacity order p : ℕ) :=
  Fin height × Fin capacity × Fin order × Fin order × ZMod p × Option (ZMod p)

def decodeContinuation {height capacity order : ℕ}
    (frame : EncodedContinuation height capacity order p) : Continuation p :=
  ⟨frame.1.val, frame.2.1.val, frame.2.2.1.val, frame.2.2.2.1.val,
    frame.2.2.2.2.1, frame.2.2.2.2.2⟩

def encodeContinuation {height capacity order : ℕ} (frame : Continuation p)
    (bounds : frame.height < height ∧ frame.start < capacity ∧
      frame.degree < order ∧ frame.split ≤ frame.degree) :
    EncodedContinuation height capacity order p :=
  (⟨frame.height, bounds.1⟩, ⟨frame.start, bounds.2.1⟩, ⟨frame.degree, bounds.2.2.1⟩,
    ⟨frame.split, bounds.2.2.2.trans_lt bounds.2.2.1⟩, frame.accumulator, frame.savedLeft)

omit [Fact p.Prime] in
theorem decode_encodeContinuation {height capacity order : ℕ} (frame : Continuation p)
    (bounds : frame.height < height ∧ frame.start < capacity ∧
      frame.degree < order ∧ frame.split ≤ frame.degree) :
    decodeContinuation (encodeContinuation frame bounds) = frame := rfl

theorem encodedContinuation_card (height capacity order : ℕ) :
    Fintype.card (EncodedContinuation height capacity order p) =
      height * capacity * order ^ 2 * p * (p + 1) := by
  simp only [EncodedContinuation, Fintype.card_prod, Fintype.card_fin,
    ZMod.card, Fintype.card_option]
  ring

/-- The actual reachable stack has a bounded-length, exact finite-register
encoding. This includes both the accumulator and the pending left result. -/
theorem reachable_stack_encodable (factor : Factors p) (count : ℕ) (root : Request)
    (state : State p) (reachable : Executes factor count (evaluating root []) state)
    (order : ℕ) (below : root.degree < order) :
    ∃ encoded : List (EncodedContinuation root.height (root.start + 2 ^ root.height) order p),
      encoded.map decodeContinuation = state.stack ∧ encoded.length ≤ root.height := by
  obtain ⟨length, _, frames⟩ := reachable_bounds factor count root state reachable
  let encode := fun frame : { frame // frame ∈ state.stack } =>
    encodeContinuation frame.val
      ⟨(frames frame.val frame.property).1, (frames frame.val frame.property).2.1,
        (frames frame.val frame.property).2.2.1.trans_lt below,
        (frames frame.val frame.property).2.2.2⟩
  refine ⟨state.stack.attach.map encode, ?_, ?_⟩
  · simp only [List.map_map, Function.comp_def, encode, decode_encodeContinuation]
    simp
  · simpa only [List.length_map, List.length_attach] using length

abbrev EncodedRequest (height capacity order : ℕ) :=
  Fin (height + 1) × Fin capacity × Fin order

def decodeRequest {height capacity order : ℕ} (request : EncodedRequest height capacity order) :
    Request := ⟨request.1.val, request.2.1.val, request.2.2.val⟩

/-- A bounded register representation of the entire evaluator state. This is
an arithmetic representation, not an allocation policy for a work tape. -/
structure EncodedState (height capacity order p : ℕ) where
  request : EncodedRequest height capacity order
  result : Option (ZMod p)
  stack : List (EncodedContinuation height capacity order p)
  stackLength : stack.length ≤ height

def decodeState {height capacity order : ℕ} (state : EncodedState height capacity order p) : State p :=
  ⟨decodeRequest state.request, state.result, state.stack.map decodeContinuation⟩

theorem reachable_encodable (factor : Factors p) (count : ℕ) (root : Request)
    (state : State p) (reachable : Executes factor count (evaluating root []) state)
    (order : ℕ) (below : root.degree < order) :
    ∃ encoded : EncodedState root.height (root.start + 2 ^ root.height) order p,
      decodeState encoded = state := by
  obtain ⟨_, ⟨height, _, finish, degree⟩, _⟩ := reachable_bounds factor count root state reachable
  obtain ⟨stack, same, length⟩ := reachable_stack_encodable factor count root state reachable order below
  have positive := Nat.two_pow_pos state.request.height
  let request : EncodedRequest root.height (root.start + 2 ^ root.height) order :=
    (⟨state.request.height, by omega⟩, ⟨state.request.start, by omega⟩,
      ⟨state.request.degree, degree.trans_lt below⟩)
  refine ⟨⟨request, state.result, stack, length⟩, ?_⟩
  change State.mk state.request state.result (stack.map decodeContinuation) = state
  rw [same]

end NtimeDspace.CoefficientStack
