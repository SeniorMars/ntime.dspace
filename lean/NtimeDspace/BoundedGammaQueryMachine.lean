import NtimeDspace.BoundedGammaQuerySpace
import NtimeDspace.BoundedGammaQueryBudget
import NtimeDspace.ComplexityReuse

/-!
A complete bounded gamma reader with runtime bound and starting cursor.
The initializer extracts only the small header; queries continue to read the
original packet. The compiled machine stores neither the payload nor a clock.
The output is either rejection or the decoded value and next relative cursor.
-/

namespace NtimeDspace.BoundedGammaQueryMachine

open Turing Turing.MultiTapeTM BoundedGammaQuery BoundedGammaQueryBudget

/-- All initialization, query scanning, callbacks, and retained state are
charged to the same actual machine's visited work cells. -/
theorem read_computes :
    ∃ time C, ComputableInTimeAndSpace read encPacket encOutput time
      (fun packet => C * spaceBudget packet) := by
  apply InitializedQueryCompiler.computableInSpace machine initial
    BoundedGammaQuerySpace.query_inSpace BoundedGammaQuerySpace.next_inSpace
    BoundedGammaQuerySpace.emit_inSpace BoundedGammaQuerySpace.halted_inSpace
    BoundedGammaQuerySpace.finish_inSpace stopTime
  · exact stopTime_halts
  · exact before_stopTime
  · exact fun packet => (output_correct packet).symm
  · exact BoundedGammaQuerySpace.initial_inSpace.mono_le init_budget
  · exact logarithmic
  · exact ⟨22, fun packet fuel _ => run_state_bound packet fuel⟩

/-- Joint bounds for one uniform machine. The budget is the sum of the bit
widths of the value bound and of `max(start, payload.length)`. -/
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

/-- Successful output contains only a bounded value and a bounded cursor. -/
theorem read_output_length (packet : Packet) :
    (encOutput (read packet)).length ≤ 3 * bitBudget packet := by
  have positive := bitBudget_pos packet
  cases parsed : read packet with
  | none => simp [encOutput, BoundedGammaPayloadSpace.encOutput]
  | some pair =>
    rcases pair with ⟨value, cursor⟩
    have sound := BoundedGammaPayload.read_sound packet.1.1 packet.2 packet.1.2
      value cursor parsed
    have cursorBound := BoundedGammaPayload.read_cursor_bounds packet.1.1 packet.2
      packet.1.2 value cursor parsed
    have valueBits := length_encNat_le_log2 sound.2.1
    have cursorBits := length_encNat_le_log2 cursorBound.2
    simp only [encOutput, BoundedGammaPayloadSpace.encOutput,
      encOption_some, List.length_cons, length_encPair]
    unfold bitBudget
    omega

/-- An output-size-aware certificate suitable for subsequent composition. -/
theorem read_inSpace : ComputableInSpace read encPacket encOutput bitBudget := by
  obtain ⟨C, computed⟩ := read_simultaneous_bounds
  refine ⟨_, C + 3, computed.mono (fun _ => le_rfl) (fun packet => ?_), fun packet => ?_⟩
  · nlinarith [bitBudget_pos packet]
  · have bounded := read_output_length packet
    nlinarith [bitBudget_pos packet]

end NtimeDspace.BoundedGammaQueryMachine
