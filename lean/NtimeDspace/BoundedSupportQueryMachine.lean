import NtimeDspace.BoundedSupportQuerySpace
import NtimeDspace.BoundedSupportQueryBudget
import NtimeDspace.ComplexityReuse

/-!
A complete support-validation and cardinality machine. Runtime bound and
capacity are extracted once; repeated gamma reads share the original input.
The endpoint returns the actual support width only after full validation.
All source lists in the correctness statements are specification witnesses,
not machine registers or intermediate decoded outputs.
-/

namespace NtimeDspace.BoundedSupportQueryMachine

open Turing Turing.MultiTapeTM BoundedSupportQuery BoundedSupportQueryBudget

theorem read_computes :
    ∃ time C, ComputableInTimeAndSpace read encPacket encOutput time
      (fun packet => C * spaceBudget packet) := by
  apply InitializedQueryCompiler.computableInSpace machine initial
    BoundedSupportQuerySpace.query_inSpace BoundedSupportQuerySpace.next_inSpace
    BoundedSupportQuerySpace.emit_inSpace BoundedSupportQuerySpace.halted_inSpace
    BoundedSupportQuerySpace.finish_inSpace stopTime
  · exact stopTime_halts
  · exact before_stopTime
  · exact fun packet => (output_correct packet).symm
  · exact BoundedSupportQuerySpace.initial_inSpace.mono_le init_budget
  · exact logarithmic
  · obtain ⟨C, bounded⟩ := reachable_state_bound
    exact ⟨C, fun packet fuel _ => bounded packet fuel⟩

/-- One machine validates the full support code with logarithmic workspace
in the universe bound, capacity and payload length, and joint time bound. -/
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
    (encOutput (read packet)).length ≤ bitBudget packet := by
  have positive := bitBudget_pos packet
  cases parsed : read packet with
  | none => simp [encOutput]
  | some width =>
    have widthBits := length_encNat_le_log2 (read_output_bound packet width parsed)
    simp only [encOutput, encOption_some, List.length_cons]
    unfold bitBudget
    omega

/-- Output size is included, so the scalar result may be used in a later
machine composition without hiding a decoded support list. -/
theorem read_inSpace : ComputableInSpace read encPacket encOutput bitBudget := by
  obtain ⟨C, computed⟩ := read_simultaneous_bounds
  refine ⟨_, C + 1, computed.mono (fun _ => le_rfl) (fun packet => ?_), fun packet => ?_⟩
  · nlinarith [bitBudget_pos packet]
  · have bounded := read_output_length packet
    nlinarith [bitBudget_pos packet]

/-- The resource endpoint computes the original full-validation cardinality
specification, not merely a count of successfully read prefixes. -/
theorem cardinality_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace
      (fun packet : Packet =>
        (SupportCardinality.count packet.1.1 packet.1.2 packet.2).map Fin.val)
      encPacket encOutput (fun packet => 2 ^ (C * bitBudget packet))
      (fun packet => C * bitBudget packet) := by
  have same : read = (fun packet : Packet =>
      (SupportCardinality.count packet.1.1 packet.1.2 packet.2).map Fin.val) :=
    funext read_correct
  rw [← same]
  exact read_simultaneous_bounds

theorem read_sound_unique (packet : Packet) (width : ℕ)
    (accepted : read packet = some width) :
    ∃! support : List (Fin packet.1.1), ∃ _valid : SupportAssignment.Valid packet.1.2 support,
      packet.2 = SupportAssignment.encode support ∧ width = support.length := by
  obtain ⟨support, valid, encoded, length⟩ := (read_some_iff packet width).mp accepted
  refine ⟨support, ⟨valid, encoded, length⟩, ?_⟩
  rintro other ⟨otherValid, otherEncoded, _⟩
  exact SupportAssignment.encode_injective otherValid valid (otherEncoded.symm.trans encoded)

end NtimeDspace.BoundedSupportQueryMachine
