import NtimeDspace.HermiteWeightSpace
import NtimeDspace.HaltingBudgetCompiler

/-!
One uniform finite-control machine evaluates the entire Hermite recovery
weight. Its state stores a scalar header, a descending index and a reduced
accumulator; coefficient values are recomputed by the already certified
machine. The resource proof charges that callee's scratch space as well as
the retained state. No list of coefficients or runtime clock is assumed.
-/

namespace NtimeDspace.HermiteWeightMachine

open Turing Turing.MultiTapeTM HermiteWeightLoop HermiteWeightBudget

/-- Complete weight evaluation from the five runtime scalar parameters. -/
theorem weight_inSpace : ComputableInSpace weight encHeader encNat inputBudget := by
  apply HaltingBudgetCompiler.of_termination (initial fallbackHeader) initial
    HermiteWeightLoop.step halted output weight inputBudget stepBudget
  · exact HermiteWeightSpace.initial_inSpace.mono_le input_length_le
  · exact HermiteWeightSpace.step_inSpace
  · exact HermiteWeightSpace.halted_inSpace
  · exact HermiteWeightSpace.output_inSpace
  · exact terminates
  · exact output_correct
  · exact reachable_budget

theorem weight_inSpace_bits : ComputableInSpace weight encHeader encNat bitBudget := by
  apply weight_inSpace.weaken
  refine ⟨15, fun header => ?_⟩
  exact (Nat.le_succ _).trans ((inputBudget_succ_le_bits header).trans (by omega))

/-- Configuration counting preserves the same machine and gives joint time
and workspace bounds, independently of the loop's iteration count. -/
theorem weight_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace weight encHeader encNat
      (fun header => 2 ^ (C * bitBudget header)) (fun header => C * bitBudget header) := by
  obtain ⟨_, c, machine, _⟩ := weight_inSpace
  have logarithmic (header : Header) :
      (encHeader header).length.log2 + 1 ≤ inputBudget header + 1 := by
    have bound := input_length_le header
    have logarithm := Nat.log2_le_self (encHeader header).length
    omega
  obtain ⟨C, counted⟩ := ComplexityReuse.exists_exponential_time_of_linear_space c machine logarithmic
  refine ⟨C * 15, counted.mono (fun header => ?_) (fun header => ?_)⟩
  · apply Nat.pow_le_pow_right (by norm_num)
    simpa only [mul_assoc] using Nat.mul_le_mul_left C (inputBudget_succ_le_bits header)
  · simpa only [mul_assoc] using Nat.mul_le_mul_left C (inputBudget_succ_le_bits header)

abbrev PositiveHeader := {header : Header // 0 < order header}

def encPositiveHeader : PositiveHeader ↪ List Bool :=
  (⟨Subtype.val, Subtype.val_injective⟩ : PositiveHeader ↪ Header).trans encHeader

/-- Equality of encoded outputs transports the compiled evaluator to the
actual polynomial used in the scalar Hermite recovery identity. -/
theorem polynomialWeight_inSpace :
    ComputableInSpace (fun header : PositiveHeader => polynomialWeight header.val)
      encPositiveHeader encNat (fun header => bitBudget header.val) := by
  have computed := weight_inSpace_bits.of_encIn_eq
    (encIn' := encPositiveHeader) (fun header : PositiveHeader => header.val) (fun _ => rfl)
  apply computed.of_enc_eq
  intro header
  rw [weight_eq_nodeWeight header.val header.property]

/-- The same machine evaluates the full Hermite-weight polynomial with
`2^O((log₂ p+1)²)` time and `O((log₂ p+1)²)` visited work cells. -/
theorem polynomialWeight_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace (fun header : PositiveHeader => polynomialWeight header.val)
      encPositiveHeader encNat (fun header => 2 ^ (C * bitBudget header.val))
      (fun header => C * bitBudget header.val) := by
  obtain ⟨C, k, State, finiteState, machine, correct⟩ := weight_simultaneous_bounds
  refine ⟨C, k, State, finiteState, machine, ?_⟩
  intro header
  have computation := correct header.val
  rw [weight_eq_nodeWeight header.val header.property] at computation
  exact computation

end NtimeDspace.HermiteWeightMachine
