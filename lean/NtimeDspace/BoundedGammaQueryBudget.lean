import NtimeDspace.BoundedGammaQuery

/-!
# Complete logarithmic budgets for the initialized bounded gamma reader

The budget includes the encoded header, the binary position counter needed
to scan the complete packet, and every live parser register. The source
payload itself stays on the read-only input tape. All bounds hold for every
packet and execution prefix, including zero bounds and out-of-range cursors.
-/

namespace NtimeDspace.BoundedGammaQueryBudget

open Turing Turing.MultiTapeTM BoundedGammaQuery

def bitBudget (packet : Packet) : ℕ :=
  (packet.1.1.log2 + 1) + ((max packet.1.2 packet.2.length).log2 + 1)

def spaceBudget (packet : Packet) : ℕ :=
  (encHeader packet.1).length + ((encPacket packet).length.log2 + 1) + bitBudget packet

theorem init_budget (packet : Packet) : (encHeader packet.1).length ≤ spaceBudget packet := by
  unfold spaceBudget
  omega

theorem logarithmic (packet : Packet) :
    (encPacket packet).length.log2 + 1 ≤ spaceBudget packet := by
  unfold spaceBudget
  omega

theorem bitBudget_le_spaceBudget (packet : Packet) : bitBudget packet ≤ spaceBudget packet :=
  Nat.le_add_left _ _

theorem bitBudget_pos (packet : Packet) : 2 ≤ bitBudget packet := by
  unfold bitBudget
  omega

theorem header_length_le_bits (packet : Packet) :
    (encHeader packet.1).length ≤ 2 * bitBudget packet := by
  have bound := length_encNat_le_log2 (Nat.le_refl packet.1.1)
  have start := length_encNat_le_log2 (le_max_left packet.1.2 packet.2.length)
  rw [encHeader_length]
  unfold bitBudget
  omega

theorem payloadOffset_le_bits (packet : Packet) :
    payloadOffset packet.1 ≤ 4 * bitBudget packet + 1 := by
  have header := header_length_le_bits packet
  unfold payloadOffset
  omega

/-- The complete packet may be long, but its logarithmic scan counter is
controlled by the header widths and the payload length's binary width. -/
theorem packet_length_lt_pow (packet : Packet) :
    (encPacket packet).length < 2 ^ (bitBudget packet + 3) := by
  have offset := payloadOffset_le_bits packet
  have smallBudget := Nat.lt_two_pow_self (n := bitBudget packet)
  have smallPayload : packet.2.length < 2 ^ bitBudget packet := by
    apply ((le_max_right packet.1.2 packet.2.length).trans_lt
      (Nat.lt_log2_self (n := max packet.1.2 packet.2.length))).trans_le
    apply Nat.pow_le_pow_right (by decide)
    unfold bitBudget
    omega
  have packetBound : (encPacket packet).length ≤
      4 * bitBudget packet + 1 + packet.2.length := by
    rw [encPacket_length]
    omega
  rw [pow_add]
  norm_num
  omega

theorem packet_logarithm_le_bits (packet : Packet) :
    (encPacket packet).length.log2 + 1 ≤ 3 * bitBudget packet := by
  have positive : 0 < (encPacket packet).length := by
    rw [encPacket_length]
    unfold payloadOffset
    omega
  have logarithm := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr (packet_length_lt_pow packet)
  have bits := bitBudget_pos packet
  omega

theorem spaceBudget_le_bits (packet : Packet) : spaceBudget packet ≤ 6 * bitBudget packet := by
  have header := header_length_le_bits packet
  have logarithm := packet_logarithm_le_bits packet
  unfold spaceBudget
  omega

theorem spaceBudget_succ_le_bits (packet : Packet) :
    spaceBudget packet + 1 ≤ 7 * bitBudget packet := by
  have bounded := spaceBudget_le_bits packet
  have positive := bitBudget_pos packet
  omega

theorem offset_logarithm_le_bits (packet : Packet) :
    (payloadOffset packet.1).log2 + 1 ≤ 5 * bitBudget packet := by
  have offset := payloadOffset_le_bits packet
  have logarithm := Nat.log2_le_self (payloadOffset packet.1)
  have positive := bitBudget_pos packet
  omega

theorem run_state_le_bits (packet : Packet) (fuel : ℕ) :
    (encState (run packet fuel)).length ≤ 22 * bitBudget packet := by
  have state := run_encoding_length packet fuel
  have offset := offset_logarithm_le_bits packet
  have positive := bitBudget_pos packet
  have boundBits : packet.1.1.log2 + 1 ≤ bitBudget packet := by
    unfold bitBudget
    omega
  change (encState (run packet fuel)).length ≤
    2 * (packet.1.1.log2 + 1) + 2 * ((payloadOffset packet.1).log2 + 1) +
      9 * bitBudget packet + 2 at state
  omega

/-- The exact all-prefix state bound expected by the initialized query
compiler, including prefixes after the reader has halted. -/
theorem run_state_bound (packet : Packet) (fuel : ℕ) :
    (encState (run packet fuel)).length ≤ 22 * spaceBudget packet :=
  (run_state_le_bits packet fuel).trans
    (Nat.mul_le_mul_left 22 (bitBudget_le_spaceBudget packet))

theorem reachable_state_bound : ∃ C, ∀ (packet : Packet) (fuel : ℕ),
    (encState (run packet fuel)).length ≤ C * spaceBudget packet :=
  ⟨22, run_state_bound⟩

end NtimeDspace.BoundedGammaQueryBudget
