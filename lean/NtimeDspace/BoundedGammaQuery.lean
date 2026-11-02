import NtimeDspace.BoundedGammaPayloadSpace
import NtimeDspace.InitializedQueryCompiler

/-!
An input-dependent bounded gamma query reader. The input packet consists of a
framed `(bound, start)` header followed by the unchanged payload bits. The
stored state contains only the bound, the payload's absolute offset, and the
six scalar parser registers. No payload, input suffix, or decoded list is
retained. Compilation of the header bootstrap and callbacks is separate.
-/

namespace NtimeDspace.BoundedGammaQuery

open Turing Turing.MultiTapeTM

abbrev Header := ℕ × ℕ
abbrev Packet := Header × List Bool

def encHeader : Header ↪ List Bool := encPair encNat encNat
def encPacket : Packet ↪ List Bool := encPair encHeader encBits
abbrev encOutput := BoundedGammaPayloadSpace.encOutput

def payloadOffset (header : Header) : ℕ := 2 * (encHeader header).length + 1

@[ext]
structure State where
  bound : ℕ
  payloadOffset : ℕ
  parser : BoundedGammaPayload.State
  deriving DecidableEq

abbrev StateData := ℕ × ℕ × BoundedGammaPayload.State

def stateData : State ↪ StateData :=
  ⟨fun state => (state.bound, state.payloadOffset, state.parser), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, State.mk.injEq] using same⟩

def encStateData : StateData ↪ List Bool :=
  encPair encNat (encPair encNat BoundedGammaPayloadSpace.encState)

def encState : State ↪ List Bool := stateData.trans encStateData

def initialHeader (header : Header) : State :=
  ⟨header.1, payloadOffset header, BoundedGammaPayload.initial header.1 header.2⟩

def initial (packet : Packet) : State := initialHeader packet.1

def query (state : State) : ℕ := state.payloadOffset + state.parser.cursor

def next (argument : State × Option Bool) : State :=
  { argument.1 with
    parser := BoundedGammaPayload.next argument.1.bound (argument.1.parser, argument.2) }

def halted (state : State) : Bool := BoundedGammaPayload.halted state.parser

def output (state : State) : Option (ℕ × ℕ) := BoundedGammaPayload.output state.parser

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

/-- The finite list reader occurs only in this specification. -/
def read (packet : Packet) : Option (ℕ × ℕ) :=
  BoundedGammaPayload.read packet.1.1 packet.2 packet.1.2

theorem encHeader_length (header : Header) :
    (encHeader header).length =
      2 * (encNat header.1).length + (encNat header.2).length + 1 := by
  simp only [encHeader, length_encPair]
  omega

theorem encPacket_length (packet : Packet) :
    (encPacket packet).length = payloadOffset packet.1 + packet.2.length := by
  simp only [encPacket, length_encPair, payloadOffset]
  rfl

/-- Absolute queries beyond the framed header are exactly relative payload
queries, including positions beyond the end of either word. -/
theorem payload_query (packet : Packet) (index : ℕ) :
    (encPacket packet)[payloadOffset packet.1 + index]? = packet.2[index]? := by
  change (frame (encHeader packet.1) ++ packet.2)[payloadOffset packet.1 + index]? = _
  rw [List.getElem?_append_right (by simp [payloadOffset])]
  simp [payloadOffset]

theorem run_refines (packet : Packet) (fuel : ℕ) :
    run packet fuel =
      ⟨packet.1.1, payloadOffset packet.1,
        BoundedGammaPayload.run packet.1.1 packet.2 packet.1.2 fuel⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [show run packet (fuel + 1) =
      (initialized packet).step (encPacket packet) (run packet fuel) from
        QueryMachine.run_succ _ _ _]
    rw [ih, BoundedGammaPayload.run_succ]
    simp only [QueryMachine.step, initialized, InitializedQueryCompiler.withInitial,
      machine, halted, QueryMachine.read, query, payload_query, BoundedGammaPayload.step]
    split_ifs <;> rfl

theorem run_bound (packet : Packet) (fuel : ℕ) : (run packet fuel).bound = packet.1.1 := by
  rw [run_refines]

theorem run_payloadOffset (packet : Packet) (fuel : ℕ) :
    (run packet fuel).payloadOffset = payloadOffset packet.1 := by
  rw [run_refines]

theorem run_parser (packet : Packet) (fuel : ℕ) :
    (run packet fuel).parser =
      BoundedGammaPayload.run packet.1.1 packet.2 packet.1.2 fuel := by
  rw [run_refines]

theorem halts_by_length (packet : Packet) :
    halted (run packet (packet.2.length + 1)) = true := by
  simpa only [halted, run_parser] using
    BoundedGammaPayload.halts_by_length packet.1.1 packet.2 packet.1.2

theorem terminates (packet : Packet) : ∃ fuel, halted (run packet fuel) = true :=
  ⟨packet.2.length + 1, halts_by_length packet⟩

/-- This first-halting clock is proof-side and is never an executing register. -/
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
  simp only [output, run_parser, read, BoundedGammaPayload.read]

theorem output_correct (packet : Packet) :
    (initialized packet).output (encPacket packet) (stopTime packet) = encOutput (read packet) := by
  rw [(initialized packet).output_eq_of_not_halted (encPacket packet)
    (before_stopTime packet)]
  have empty : ∀ state bit, (initialized packet).emit (state, bit) = [] := fun _ _ => rfl
  simp only [empty, List.map_const', List.length_range,
    List.flatten_replicate_nil, List.nil_append]
  change encOutput (output (run packet (stopTime packet))) = _
  rw [halted_output packet _ (stopTime_halts packet)]

theorem run_register_bounds (packet : Packet) (fuel : ℕ) :
    let parser := (run packet fuel).parser
    packet.1.2 ≤ parser.cursor ∧ parser.cursor ≤ max packet.1.2 packet.2.length ∧
      parser.zeros ≤ packet.1.1.log2 ∧ parser.remaining ≤ packet.1.1.log2 ∧
      parser.accumulator ≤ packet.1.1 ∧ parser.room ≤ packet.1.1 := by
  simpa only [run_parser] using
    BoundedGammaPayload.run_register_bounds packet.1.1 packet.2 packet.1.2 fuel

theorem encState_length (state : State) :
    (encState state).length = 2 * (encNat state.bound).length +
      2 * (encNat state.payloadOffset).length +
      (BoundedGammaPayloadSpace.encState state.parser).length + 2 := by
  change (encPair encNat (encPair encNat BoundedGammaPayloadSpace.encState)
    (state.bound, state.payloadOffset, state.parser)).length = _
  simp only [length_encPair]
  omega

theorem run_encoding_length (packet : Packet) (fuel : ℕ) :
    (encState (run packet fuel)).length ≤
      2 * (packet.1.1.log2 + 1) + 2 * ((payloadOffset packet.1).log2 + 1) +
      9 * ((packet.1.1.log2 + 1) + ((max packet.1.2 packet.2.length).log2 + 1)) + 2 := by
  have bound := length_encNat_le_log2 (Nat.le_refl packet.1.1)
  have offset := length_encNat_le_log2 (Nat.le_refl (payloadOffset packet.1))
  have parser := BoundedGammaPayloadSpace.run_encoding_length
    packet.1.1 packet.2 packet.1.2 fuel
  rw [encState_length, run_bound, run_payloadOffset, run_parser]
  omega

end NtimeDspace.BoundedGammaQuery
