import NtimeDspace.SupportOrdinalQuerySpace
import NtimeDspace.SupportOrdinalQueryBudget
import NtimeDspace.ComplexityReuse

/-!
One uniform machine validates a support and returns its actual width and the
queried entry's one-based position. Zero denotes absence. A match never ends
validation early. Lists of support entries occur only in correctness proofs.
-/

namespace NtimeDspace.SupportOrdinalQueryMachine

open Turing Turing.MultiTapeTM SupportOrdinalQuery SupportOrdinalQueryBudget

theorem read_computes :
    ∃ time C, ComputableInTimeAndSpace read encPacket encOutput time
      (fun packet => C * spaceBudget packet) := by
  apply InitializedQueryCompiler.computableInSpace machine initial
    SupportOrdinalQuerySpace.query_inSpace SupportOrdinalQuerySpace.next_inSpace
    SupportOrdinalQuerySpace.emit_inSpace SupportOrdinalQuerySpace.halted_inSpace
    SupportOrdinalQuerySpace.finish_inSpace stopTime
  · exact stopTime_halts
  · exact before_stopTime
  · exact fun packet => (output_correct packet).symm
  · exact SupportOrdinalQuerySpace.initial_inSpace.mono_le init_budget
  · exact logarithmic
  · obtain ⟨C, bounded⟩ := reachable_state_bound
    exact ⟨C, fun packet fuel _ => bounded packet fuel⟩

/-- Joint bounds on the same machine, including the runtime query width and
the original input's scan counter. -/
theorem read_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace read encPacket encOutput
      (fun packet => 2 ^ (C * bitBudget packet)) (fun packet => C * bitBudget packet) := by
  obtain ⟨_, c, computed⟩ := read_computes
  obtain ⟨C, counted⟩ := ComplexityReuse.exists_exponential_time_of_linear_space
    c computed logarithmic
  refine ⟨C * 6, counted.mono (fun packet => ?_) (fun packet => ?_)⟩
  · apply Nat.pow_le_pow_right (by norm_num)
    simpa only [mul_assoc] using Nat.mul_le_mul_left C (spaceBudget_le_bits packet)
  · simpa only [mul_assoc] using Nat.mul_le_mul_left C (spaceBudget_le_bits packet)

theorem read_output_length (packet : Packet) :
    (encOutput (read packet)).length ≤ 3 * bitBudget packet := by
  cases parsed : read packet with
  | none => simp [encOutput]
  | some pair =>
    rcases pair with ⟨width, ordinal⟩
    have bounded := read_output_bounds packet width ordinal parsed
    have widthBits := length_encNat_le_log2 bounded.2
    have ordinalBits := length_encNat_le_log2 (bounded.1.trans bounded.2)
    simp only [encOutput, encOption_some, List.length_cons, length_encPair]
    unfold bitBudget
    omega

/-- Output-aware certificate for subsequent scalar machine composition. -/
theorem read_inSpace : ComputableInSpace read encPacket encOutput bitBudget := by
  obtain ⟨C, computed⟩ := read_simultaneous_bounds
  refine ⟨_, C + 3, computed.mono (fun _ => le_rfl) (fun packet => ?_), fun packet => ?_⟩
  · nlinarith [bitBudget_pos packet]
  · have bounded := read_output_length packet
    nlinarith [bitBudget_pos packet]

/-- The resource theorem computes the full-validation ordinal specification. -/
theorem ordinal_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace
      (fun packet : Packet =>
        SupportOrdinalScan.read packet.1.1 packet.1.2.1 packet.1.2.2 packet.2)
      encPacket encOutput (fun packet => 2 ^ (C * bitBudget packet))
      (fun packet => C * bitBudget packet) := by
  have same : read = (fun packet : Packet =>
      SupportOrdinalScan.read packet.1.1 packet.1.2.1 packet.1.2.2 packet.2) :=
    funext read_correct
  rw [← same]
  exact read_simultaneous_bounds

theorem read_sound_unique (packet : Packet) (width ordinal : ℕ)
    (accepted : read packet = some (width, ordinal)) :
    ∃! support : List (Fin packet.1.1), ∃ _valid : SupportAssignment.Valid packet.1.2.1 support,
      packet.2 = SupportAssignment.encode support ∧ width = support.length ∧
        ordinal = if packet.1.2.2 ∈ SupportAssignment.positiveSupport support then
          (SupportAssignment.positiveSupport support).idxOf packet.1.2.2 + 1 else 0 := by
  obtain ⟨support, valid, encoded, length, position⟩ := (read_some_iff packet width ordinal).mp accepted
  refine ⟨support, ⟨valid, encoded, length, position⟩, ?_⟩
  rintro other ⟨otherValid, otherEncoded, _, _⟩
  exact SupportAssignment.encode_injective otherValid valid (otherEncoded.symm.trans encoded)

end NtimeDspace.SupportOrdinalQueryMachine
