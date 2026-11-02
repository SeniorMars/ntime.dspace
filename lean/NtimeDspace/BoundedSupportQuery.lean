import NtimeDspace.BoundedSupportPayloadSpace
import NtimeDspace.InitializedQueryCompiler

/-!
A bounded support validator querying an immutable encoded payload. Its
small header contains the universe bound and support capacity. The stored
state contains only these parameters, the payload offset, and the scalar
support-parser state. No decoded support or source suffix is retained.
-/

namespace NtimeDspace.BoundedSupportQuery

open Turing Turing.MultiTapeTM

abbrev Header := ℕ × ℕ
abbrev Packet := Header × List Bool

def encHeader : Header ↪ List Bool := encPair encNat encNat
def encPacket : Packet ↪ List Bool := encPair encHeader encBits
def encOutput : Option ℕ ↪ List Bool := encOption encNat

def payloadOffset (header : Header) : ℕ := 2 * (encHeader header).length + 1

@[ext]
structure State where
  bound : ℕ
  capacity : ℕ
  payloadOffset : ℕ
  parser : BoundedSupportPayload.State
  deriving DecidableEq

abbrev StateData := ℕ × ℕ × ℕ × BoundedSupportPayload.State

def stateData : State ↪ StateData :=
  ⟨fun state => (state.bound, state.capacity, state.payloadOffset, state.parser), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, State.mk.injEq] using same⟩

def encStateData : StateData ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat BoundedSupportPayloadSpace.encState))

def encState : State ↪ List Bool := stateData.trans encStateData

def initialHeader (header : Header) : State :=
  ⟨header.1, header.2, payloadOffset header, BoundedSupportPayload.initial header.1⟩

def initial (packet : Packet) : State := initialHeader packet.1

def query (state : State) : ℕ := state.payloadOffset + state.parser.parser.cursor

def next (argument : State × Option Bool) : State :=
  { argument.1 with
    parser := BoundedSupportPayload.next argument.1.bound argument.1.capacity
      (argument.1.parser, argument.2) }

def halted (state : State) : Bool := BoundedSupportPayload.halted state.parser

def output (state : State) : Option ℕ := BoundedSupportPayload.output state.parser

def finish (state : State) : List Bool := encOutput (output state)

/-- The fixed fallback is replaced by the certified header initializer. -/
def machine : QueryMachine State where
  init := initialHeader (0, 0)
  query := query
  next := next
  emit := fun _ => []
  halted := halted
  finish := finish

def initialized (packet : Packet) : QueryMachine State :=
  InitializedQueryCompiler.withInitial machine (initial packet)

def run (packet : Packet) (fuel : ℕ) : State :=
  (initialized packet).run (encPacket packet) fuel

/-- This whole-payload validation function occurs only in the specification. -/
def read (packet : Packet) : Option ℕ :=
  BoundedSupportPayload.read packet.1.1 packet.1.2 packet.2

theorem encHeader_length (header : Header) :
    (encHeader header).length =
      2 * (encNat header.1).length + (encNat header.2).length + 1 := by
  simp only [encHeader, length_encPair]
  omega

theorem encPacket_length (packet : Packet) :
    (encPacket packet).length = payloadOffset packet.1 + packet.2.length := by
  simp only [encPacket, length_encPair, payloadOffset]
  rfl

theorem payload_query (packet : Packet) (index : ℕ) :
    (encPacket packet)[payloadOffset packet.1 + index]? = packet.2[index]? := by
  change (frame (encHeader packet.1) ++ packet.2)[payloadOffset packet.1 + index]? = _
  rw [List.getElem?_append_right (by simp [payloadOffset])]
  simp [payloadOffset]

theorem run_refines (packet : Packet) (fuel : ℕ) :
    run packet fuel =
      ⟨packet.1.1, packet.1.2, payloadOffset packet.1,
        BoundedSupportPayload.run packet.1.1 packet.1.2 packet.2 fuel⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [show run packet (fuel + 1) =
      (initialized packet).step (encPacket packet) (run packet fuel) from
        QueryMachine.run_succ _ _ _]
    rw [ih, show BoundedSupportPayload.run packet.1.1 packet.1.2 packet.2 (fuel + 1) =
      BoundedSupportPayload.step packet.1.1 packet.1.2 packet.2
        (BoundedSupportPayload.run packet.1.1 packet.1.2 packet.2 fuel) from
          Function.iterate_succ_apply' _ _ _]
    simp only [QueryMachine.step, initialized, InitializedQueryCompiler.withInitial,
      machine, halted, QueryMachine.read, query, payload_query, BoundedSupportPayload.step,
      BoundedSupportPayload.query]
    split_ifs <;> rfl

theorem run_bound (packet : Packet) (fuel : ℕ) : (run packet fuel).bound = packet.1.1 := by
  rw [run_refines]

theorem run_capacity (packet : Packet) (fuel : ℕ) : (run packet fuel).capacity = packet.1.2 := by
  rw [run_refines]

theorem run_payloadOffset (packet : Packet) (fuel : ℕ) :
    (run packet fuel).payloadOffset = payloadOffset packet.1 := by
  rw [run_refines]

theorem run_parser (packet : Packet) (fuel : ℕ) :
    (run packet fuel).parser =
      BoundedSupportPayload.run packet.1.1 packet.1.2 packet.2 fuel := by
  rw [run_refines]

theorem halts_by_length (packet : Packet) :
    halted (run packet (packet.2.length + 1)) = true := by
  simpa only [halted, run_parser] using
    BoundedSupportPayload.halts_by_length packet.1.1 packet.1.2 packet.2

theorem terminates (packet : Packet) : ∃ fuel, halted (run packet fuel) = true :=
  ⟨packet.2.length + 1, halts_by_length packet⟩

/-- The first-halting clock is used only in the proof of compilation. -/
def stopTime (packet : Packet) : ℕ := Nat.find (terminates packet)

theorem stopTime_halts (packet : Packet) : halted (run packet (stopTime packet)) = true :=
  Nat.find_spec (terminates packet)

theorem before_stopTime (packet : Packet) (fuel : ℕ) (before : fuel < stopTime packet) :
    halted (run packet fuel) = false :=
  Bool.eq_false_iff.mpr (Nat.find_min (terminates packet) before)

theorem stopTime_le (packet : Packet) : stopTime packet ≤ packet.2.length + 1 :=
  Nat.find_min' (terminates packet) (halts_by_length packet)

theorem halted_output (packet : Packet) (fuel : ℕ)
    (done : halted (run packet fuel) = true) : output (run packet fuel) = read packet := by
  have terminal := halts_by_length packet
  have same₁ := (initialized packet).run_eq_of_le (encPacket packet) done
    (show fuel ≤ max fuel (packet.2.length + 1) from le_max_left _ _)
  have same₂ := (initialized packet).run_eq_of_le (encPacket packet) terminal
    (show packet.2.length + 1 ≤ max fuel (packet.2.length + 1) from le_max_right _ _)
  have same : run packet fuel = run packet (packet.2.length + 1) := same₁.symm.trans same₂
  rw [same]
  simp only [output, run_parser, read, BoundedSupportPayload.read]

theorem output_correct (packet : Packet) :
    (initialized packet).output (encPacket packet) (stopTime packet) = encOutput (read packet) := by
  rw [(initialized packet).output_eq_of_not_halted (encPacket packet)
    (before_stopTime packet)]
  have empty : ∀ state bit, (initialized packet).emit (state, bit) = [] := fun _ _ => rfl
  simp only [empty, List.map_const', List.length_range,
    List.flatten_replicate_nil, List.nil_append]
  change encOutput (output (run packet (stopTime packet))) = _
  rw [halted_output packet _ (stopTime_halts packet)]

theorem read_correct (packet : Packet) :
    read packet = (SupportCardinality.count packet.1.1 packet.1.2 packet.2).map Fin.val :=
  BoundedSupportPayload.read_correct packet.1.1 packet.1.2 packet.2

/-- The witness support is specification-only. Successful validation returns
its actual length, not the supplied capacity, and consumes the entire code. -/
theorem read_some_iff (packet : Packet) (width : ℕ) :
    read packet = some width ↔
      ∃ support : List (Fin packet.1.1), ∃ _valid : SupportAssignment.Valid packet.1.2 support,
        packet.2 = SupportAssignment.encode support ∧ width = support.length := by
  rw [read_correct]
  constructor
  · intro accepted
    cases parsed : SupportCardinality.count packet.1.1 packet.1.2 packet.2 with
    | none => simp [parsed] at accepted
    | some result =>
      have same : result.val = width := by simpa [parsed] using accepted
      obtain ⟨support, valid, code, length⟩ :=
        (SupportCardinality.count_some_iff packet.2 result).mp parsed
      exact ⟨support, valid, code, same.symm.trans length⟩
  · rintro ⟨support, valid, code, rfl⟩
    rw [code, SupportCardinality.count_encode support valid]
    rfl

theorem read_output_bound (packet : Packet) (width : ℕ)
    (accepted : read packet = some width) : width ≤ packet.1.2 := by
  obtain ⟨support, valid, _, same⟩ := (read_some_iff packet width).mp accepted
  simpa only [same] using valid.2

theorem encState_length (state : State) :
    (encState state).length = 2 * (encNat state.bound).length +
      2 * (encNat state.capacity).length + 2 * (encNat state.payloadOffset).length +
      (BoundedSupportPayloadSpace.encState state.parser).length + 3 := by
  change (encPair encNat (encPair encNat (encPair encNat BoundedSupportPayloadSpace.encState))
    (state.bound, state.capacity, state.payloadOffset, state.parser)).length = _
  simp only [length_encPair]
  omega

end NtimeDspace.BoundedSupportQuery
