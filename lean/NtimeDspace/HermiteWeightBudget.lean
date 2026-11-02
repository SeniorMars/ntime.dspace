import NtimeDspace.HermiteWeightLoop

/-!
# Complete budgets for the scalar Hermite-weight loop

The header contains all five scalar parameters. Its encoding and both loop
registers are charged explicitly. A transition also pays for the coefficient
machine's quadratic-bit workspace, even though the outer state is smaller.
These are encoded-size bounds; the machine composition uses the separately
proved callback certificates.
-/

namespace NtimeDspace.HermiteWeightBudget

open Turing Turing.MultiTapeTM HermiteWeightLoop

def bitBudget (header : Header) : ℕ := ((modulus header).log2 + 1) ^ 2

def inputBudget (header : Header) : ℕ := (encHeader header).length + bitBudget header

def stepBudget (state : State) : ℕ := (encState state).length + bitBudget state.header

theorem input_length_le (header : Header) : (encHeader header).length ≤ inputBudget header :=
  Nat.le_add_right _ _

theorem coefficient_bitBudget (state : State) :
    HermiteCoefficientMachine.bitBudget (coefficientInput state) = bitBudget state.header := rfl

theorem coefficient_bitBudget_le_stepBudget (state : State) :
    HermiteCoefficientMachine.bitBudget (coefficientInput state) ≤ stepBudget state := by
  rw [coefficient_bitBudget]
  exact Nat.le_add_left _ _

theorem encHeader_length (header : Header) :
    (encHeader header).length =
      2 * ((encNat (modulus header)).length + (encNat (count header)).length +
        (encNat (node header)).length + (encNat (order header)).length) +
      (encNat (point header)).length + 4 :=
  HermiteFactorSpace.encInput_length header.val

theorem encHeader_length_le (header : Header) :
    (encHeader header).length ≤ 9 * ((modulus header).log2 + 1) + 4 := by
  exact HermiteFactorSpace.encInput_length_le _ _ _ _ _ (modulus header)
    le_rfl (count_lt_modulus header).le
    ((node_lt_count header).le.trans (count_lt_modulus header).le)
    (order_le_modulus header) (point_lt_modulus header).le

/-- Even an arbitrary outer state supplies a bounded five-parameter argument
to the coefficient machine: the queried index is explicitly reduced. -/
theorem coefficient_input_length_le (state : State) :
    (HermiteCoefficientMachine.encBoundedInput (coefficientInput state)).length ≤
      9 * ((modulus state.header).log2 + 1) + 4 := by
  exact HermiteFactorSpace.encInput_length_le _ _ _ _ _ (modulus state.header)
    le_rfl (count_lt_modulus state.header).le
    ((node_lt_count state.header).le.trans (count_lt_modulus state.header).le)
    (order_le_modulus state.header)
    (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _)))

theorem encState_length (state : State) :
    (encState state).length = 2 * (encHeader state.header).length +
      2 * (encNat state.remaining).length + (encNat state.accumulator).length + 2 := by
  change (encPair encHeader (encPair encNat encNat)
    (state.header, state.remaining, state.accumulator)).length = _
  simp only [length_encPair]
  omega

/-- Reachable-state register bounds imply a linear encoded state, including
the complete retained header. This also applies to any other bounded state. -/
theorem encState_length_le (state : State)
    (remaining : state.remaining ≤ modulus state.header)
    (accumulator : state.accumulator ≤ modulus state.header) :
    (encState state).length ≤ 31 * ((modulus state.header).log2 + 1) := by
  have header := encHeader_length_le state.header
  have remainingBits := length_encNat_le_log2 remaining
  have accumulatorBits := length_encNat_le_log2 accumulator
  rw [encState_length]
  omega

theorem bits_le_bitBudget (header : Header) :
    (modulus header).log2 + 1 ≤ bitBudget header := by
  unfold bitBudget
  nlinarith [Nat.zero_le (modulus header).log2]

theorem bitBudget_pos (header : Header) : 1 ≤ bitBudget header := by
  have bound := bits_le_bitBudget header
  omega

theorem inputBudget_succ_le_bits (header : Header) :
    inputBudget header + 1 ≤ 15 * bitBudget header := by
  have headerBound := encHeader_length_le header
  have bits := bits_le_bitBudget header
  have positive := bitBudget_pos header
  unfold inputBudget
  omega

/-- The coefficient callee's budget and the live outer state fit one common
quadratic-bit envelope. No coefficient table is retained in the state. -/
theorem state_stepBudget_le_bits (state : State)
    (remaining : state.remaining ≤ modulus state.header)
    (accumulator : state.accumulator ≤ modulus state.header) :
    (encState state).length + stepBudget state ≤ 63 * bitBudget state.header := by
  have stateBound := encState_length_le state remaining accumulator
  have bits := bits_le_bitBudget state.header
  unfold stepBudget
  omega

theorem run_encoding_length (header : Header) (fuel : ℕ) :
    (encState (run header fuel)).length ≤ 31 * ((modulus header).log2 + 1) := by
  have bounded := encState_length_le (run header fuel)
    (by rw [run_header]; exact (run_remaining_le_order header fuel).trans (order_le_modulus header))
    (by rw [run_header]; exact (run_accumulator_lt header fuel).le)
  simpa only [run_header] using bounded

theorem run_stepBudget_le_bits (header : Header) (fuel : ℕ) :
    (encState (run header fuel)).length + stepBudget (run header fuel) ≤
      63 * bitBudget header := by
  have bounded := state_stepBudget_le_bits (run header fuel)
    (by rw [run_header]; exact (run_remaining_le_order header fuel).trans (order_le_modulus header))
    (by rw [run_header]; exact (run_accumulator_lt header fuel).le)
  simpa only [run_header] using bounded

/-- The complete reachable round budget, in the exact form consumed by the
halting-budget compiler. It holds before and after termination. -/
theorem run_budget_bound (header : Header) (fuel : ℕ) :
    (encState (run header fuel)).length + stepBudget (run header fuel) ≤
      63 * (inputBudget header + 1) := by
  apply (run_stepBudget_le_bits header fuel).trans
  apply Nat.mul_le_mul_left 63
  unfold inputBudget
  omega

theorem reachable_budget : ∃ C, ∀ (header : Header) (fuel : ℕ),
    (encState (run header fuel)).length + stepBudget (run header fuel) ≤
      C * (inputBudget header + 1) :=
  ⟨63, run_budget_bound⟩

end NtimeDspace.HermiteWeightBudget
