import NtimeDspace.SupportOrdinalPayloadSpace
import NtimeDspace.InitializedQueryCompiler

/-!
An indexed-input support ordinal query. Its header contains the universe
bound, capacity, and queried natural index. Validation scans the immutable
payload, retaining only scalar parameters and parser registers. Successful
output is the actual width and a one-based ordinal; zero denotes absence.
-/

namespace NtimeDspace.SupportOrdinalQuery

open Turing Turing.MultiTapeTM

abbrev Header := ℕ × ℕ × ℕ
abbrev Packet := Header × List Bool

def encHeader : Header ↪ List Bool := encPair encNat (encPair encNat encNat)
def encPacket : Packet ↪ List Bool := encPair encHeader encBits
def encOutput : Option (ℕ × ℕ) ↪ List Bool := encOption (encPair encNat encNat)

def payloadOffset (header : Header) : ℕ := 2 * (encHeader header).length + 1

@[ext]
structure State where
  bound : ℕ
  capacity : ℕ
  target : ℕ
  payloadOffset : ℕ
  parser : SupportOrdinalPayload.State
  deriving DecidableEq

abbrev StateData := ℕ × ℕ × ℕ × ℕ × SupportOrdinalPayload.State

def stateData : State ↪ StateData :=
  ⟨fun state => (state.bound, state.capacity, state.target, state.payloadOffset, state.parser), by
    intro a b same
    cases a
    cases b
    simpa only [Prod.mk.injEq, State.mk.injEq] using same⟩

def encStateData : StateData ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat SupportOrdinalPayloadSpace.encState)))

def encState : State ↪ List Bool := stateData.trans encStateData

def initialHeader (header : Header) : State :=
  ⟨header.1, header.2.1, header.2.2, payloadOffset header, SupportOrdinalPayload.initial header.1⟩

def initial (packet : Packet) : State := initialHeader packet.1

def query (state : State) : ℕ := state.payloadOffset + SupportOrdinalPayload.query state.parser

def next (argument : State × Option Bool) : State :=
  { argument.1 with
    parser := SupportOrdinalPayload.next argument.1.bound argument.1.capacity argument.1.target
      (argument.1.parser, argument.2) }

def halted (state : State) : Bool := SupportOrdinalPayload.halted state.parser

def output (state : State) : Option (ℕ × ℕ) := SupportOrdinalPayload.output state.parser

def finish (state : State) : List Bool := encOutput (output state)

def machine : QueryMachine State where
  init := initialHeader (0, 0, 0)
  query := query
  next := next
  emit := fun _ => []
  halted := halted
  finish := finish

def initialized (packet : Packet) : QueryMachine State :=
  InitializedQueryCompiler.withInitial machine (initial packet)

def run (packet : Packet) (fuel : ℕ) : State :=
  (initialized packet).run (encPacket packet) fuel

/-- The finite whole-input parser is a semantic specification. -/
def read (packet : Packet) : Option (ℕ × ℕ) :=
  SupportOrdinalPayload.read packet.1.1 packet.1.2.1 packet.1.2.2 packet.2

theorem encHeader_length (header : Header) :
    (encHeader header).length = 2 * (encNat header.1).length +
      2 * (encNat header.2.1).length + (encNat header.2.2).length + 2 := by
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
      ⟨packet.1.1, packet.1.2.1, packet.1.2.2, payloadOffset packet.1,
        SupportOrdinalPayload.run packet.1.1 packet.1.2.1 packet.1.2.2 packet.2 fuel⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [show run packet (fuel + 1) =
      (initialized packet).step (encPacket packet) (run packet fuel) from
        QueryMachine.run_succ _ _ _]
    rw [ih, show SupportOrdinalPayload.run packet.1.1 packet.1.2.1 packet.1.2.2 packet.2
        (fuel + 1) = SupportOrdinalPayload.step packet.1.1 packet.1.2.1 packet.1.2.2 packet.2
          (SupportOrdinalPayload.run packet.1.1 packet.1.2.1 packet.1.2.2 packet.2 fuel) from
            Function.iterate_succ_apply' _ _ _]
    simp only [QueryMachine.step, initialized, InitializedQueryCompiler.withInitial,
      machine, halted, QueryMachine.read, query, payload_query, SupportOrdinalPayload.step]
    split_ifs <;> rfl

theorem run_bound (packet : Packet) (fuel : ℕ) : (run packet fuel).bound = packet.1.1 := by
  rw [run_refines]

theorem run_capacity (packet : Packet) (fuel : ℕ) :
    (run packet fuel).capacity = packet.1.2.1 := by
  rw [run_refines]

theorem run_target (packet : Packet) (fuel : ℕ) :
    (run packet fuel).target = packet.1.2.2 := by
  rw [run_refines]

theorem run_payloadOffset (packet : Packet) (fuel : ℕ) :
    (run packet fuel).payloadOffset = payloadOffset packet.1 := by
  rw [run_refines]

theorem run_parser (packet : Packet) (fuel : ℕ) :
    (run packet fuel).parser =
      SupportOrdinalPayload.run packet.1.1 packet.1.2.1 packet.1.2.2 packet.2 fuel := by
  rw [run_refines]

theorem halts_by_length (packet : Packet) :
    halted (run packet (packet.2.length + 1)) = true := by
  simpa only [halted, run_parser] using
    SupportOrdinalPayload.halts_by_length packet.1.1 packet.1.2.1 packet.1.2.2 packet.2

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
  simp only [output, run_parser, read, SupportOrdinalPayload.read]

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
    read packet =
      SupportOrdinalScan.read packet.1.1 packet.1.2.1 packet.1.2.2 packet.2 :=
  SupportOrdinalPayload.read_correct packet.1.1 packet.1.2.1 packet.1.2.2 packet.2

/-- The canonical support and list search occur only in the specification.
A present target returns its one-based position; an absent target returns zero.
Both cases require validation of the entire encoded support. -/
theorem read_some_iff (packet : Packet) (width ordinal : ℕ) :
    read packet = some (width, ordinal) ↔
      ∃ support : List (Fin packet.1.1), ∃ _valid : SupportAssignment.Valid packet.1.2.1 support,
        packet.2 = SupportAssignment.encode support ∧ width = support.length ∧
          ordinal = if packet.1.2.2 ∈ SupportAssignment.positiveSupport support then
            (SupportAssignment.positiveSupport support).idxOf packet.1.2.2 + 1 else 0 := by
  rw [read_correct]
  exact SupportOrdinalScan.read_some_iff _ _ _ _ _ _

theorem read_output_bounds (packet : Packet) (width ordinal : ℕ)
    (accepted : read packet = some (width, ordinal)) :
    ordinal ≤ width ∧ width ≤ packet.1.2.1 :=
  SupportOrdinalPayload.read_output_bounds _ _ _ _ _ _ accepted

theorem encState_length (state : State) :
    (encState state).length = 2 * (encNat state.bound).length +
      2 * (encNat state.capacity).length + 2 * (encNat state.target).length +
      2 * (encNat state.payloadOffset).length +
      (SupportOrdinalPayloadSpace.encState state.parser).length + 4 := by
  change (encPair encNat (encPair encNat (encPair encNat (encPair encNat
    SupportOrdinalPayloadSpace.encState)))
    (state.bound, state.capacity, state.target, state.payloadOffset, state.parser)).length = _
  simp only [length_encPair]
  omega

end NtimeDspace.SupportOrdinalQuery
