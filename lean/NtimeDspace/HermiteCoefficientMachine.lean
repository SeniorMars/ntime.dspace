import NtimeDspace.HermiteCoefficientSpace
import NtimeDspace.HermiteCoefficientBudget
import NtimeDspace.HaltingStateCompiler
import NtimeDspace.ComplexityReuse

/-!
A complete machine computes one Hermite-weight coefficient from five binary
scalar inputs. The prime and valid-node conditions restrict its input domain;
they supply no runtime oracle or encoded proof. Initialization, factor access,
reciprocal leaves, continuation transitions, and the halting loop are compiled.

The specification is the total modular coefficient program. Its interpretation
as a reciprocal power-series coefficient still uses the algebraic hypotheses
of the existing recovery theorems. This is a component of the counting machine,
not the full formula-counting workspace theorem.
-/

namespace NtimeDspace.HermiteCoefficientMachine

open Turing Turing.MultiTapeTM

def Valid (input : HermiteCoefficientLoop.Input) : Prop :=
  input.1.Prime ∧ input.2.2.1 < input.2.1

abbrev Input := {input : HermiteCoefficientLoop.Input // Valid input}

def encInput : Input ↪ List Bool :=
  (⟨Subtype.val, Subtype.val_injective⟩ : Input ↪ HermiteCoefficientLoop.Input).trans
    HermiteCoefficientLoop.encInput

noncomputable def coefficient (input : Input) : ℕ :=
  letI : Fact input.val.1.Prime := ⟨input.property.1⟩
  (IntervalCoefficients.allCoefficient
    (HermiteCoefficientLoop.factors input.val.1 input.val.2.1
      ⟨input.val.2.2.1, input.property.2⟩ input.val.2.2.2.1)
    input.val.2.1 input.val.2.2.2.2).val

def budget (input : Input) : ℕ := HermiteCoefficientLoop.spaceBound input.val

/-- One actual machine computes the complete coefficient, with every live
parameter and continuation charged to the explicit budget. -/
theorem coefficient_inSpace :
    ComputableInSpace coefficient encInput encNat budget := by
  apply HaltingStateCompiler.of_termination
    (HermiteCoefficientLoop.initial (0, 0, 0, 0, 0))
    (fun input : Input => HermiteCoefficientLoop.initial input.val)
    HermiteCoefficientLoop.step HermiteCoefficientLoop.halted HermiteCoefficientLoop.output
    coefficient budget
  · exact (HermiteCoefficientSpace.initial_inSpace.of_encIn_eq Subtype.val
      (fun _ => rfl)).mono_le (fun input =>
        HermiteCoefficientLoop.input_length_le_spaceBound input.val)
  · exact HermiteCoefficientSpace.step_inSpace
  · exact HermiteCoefficientSpace.halted_inSpace
  · exact HermiteCoefficientSpace.output_inSpace
  · intro input
    let : Fact input.val.1.Prime := ⟨input.property.1⟩
    obtain ⟨fuel, done, _⟩ := HermiteCoefficientLoop.terminates input.val.1 input.val.2.1
      ⟨input.val.2.2.1, input.property.2⟩ input.val.2.2.2.1 input.val.2.2.2.2
    exact ⟨fuel, done⟩
  · intro input fuel done
    let : Fact input.val.1.Prime := ⟨input.property.1⟩
    exact HermiteCoefficientLoop.output_correct input.val.1 input.val.2.1
      ⟨input.val.2.2.1, input.property.2⟩ input.val.2.2.2.1 input.val.2.2.2.2 fuel done
  · refine ⟨1, ?_⟩
    intro input fuel
    let : Fact input.val.1.Prime := ⟨input.property.1⟩
    have bounded := HermiteCoefficientLoop.run_encoding_length input.val.1 input.val.2.1
      ⟨input.val.2.2.1, input.property.2⟩ input.val.2.2.2.1 input.val.2.2.2.2 fuel
    change (HermiteCoefficientLoop.encState (HermiteCoefficientLoop.run input.val fuel)).length ≤
      1 * (budget input + 1)
    exact bounded.trans (by simp [budget])

/-- Configuration counting gives simultaneous bounds for the same halting
machine; no runtime clock is added to its workspace. -/
theorem coefficient_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace coefficient encInput encNat
      (fun input => 2 ^ (C * (budget input + 1)))
      (fun input => C * (budget input + 1)) := by
  obtain ⟨_, c, machine, _⟩ := coefficient_inSpace
  apply ComplexityReuse.exists_exponential_time_of_linear_space c machine
  intro input
  have inputLength := HermiteCoefficientLoop.input_length_le_spaceBound input.val
  have logarithm := Nat.log2_le_self (encInput input).length
  change (encInput input).length.log2 + 1 ≤ HermiteCoefficientLoop.spaceBound input.val + 1
  change (encInput input).length ≤ HermiteCoefficientLoop.spaceBound input.val at inputLength
  omega

def Bounded (input : Input) : Prop :=
  input.val.2.1 ≤ input.val.1 ∧ input.val.2.2.2.1 ≤ input.val.1 ∧
    input.val.2.2.2.2 ≤ input.val.1

abbrev BoundedInput := {input : Input // Bounded input}

def encBoundedInput : BoundedInput ↪ List Bool :=
  (⟨Subtype.val, Subtype.val_injective⟩ : BoundedInput ↪ Input).trans encInput

def bitBudget (input : BoundedInput) : ℕ := (input.val.val.1.log2 + 1) ^ 2

theorem budget_le_bits (input : BoundedInput) : budget input.val ≤ 256 * bitBudget input := by
  exact HermiteCoefficientBudget.spaceBound_le _ _ _ _ _ input.val.property.1.pos
    input.property.1 (input.val.property.2.le.trans input.property.1)
    input.property.2.1 input.property.2.2

/-- In the bounded scalar range, the complete coefficient evaluator uses
`O((log₂ p + 1)²)` visited work cells. -/
theorem coefficient_inSpace_bits :
    ComputableInSpace (fun input : BoundedInput => coefficient input.val)
      encBoundedInput encNat bitBudget := by
  apply (coefficient_inSpace.of_encIn_eq Subtype.val (fun _ => rfl)).weaken
  exact ⟨256, fun input => (budget_le_bits input).trans (by omega)⟩

/-- Simultaneous exponential time and quadratic-bit workspace for one machine.
This endpoint is uniform in all five encoded scalar inputs. -/
theorem coefficient_simultaneous_bits :
    ∃ C, ComputableInTimeAndSpace (fun input : BoundedInput => coefficient input.val)
      encBoundedInput encNat (fun input => 2 ^ (C * bitBudget input))
      (fun input => C * bitBudget input) := by
  obtain ⟨C, machine⟩ := coefficient_simultaneous_bounds
  have restricted : ComputableInTimeAndSpace (fun input : BoundedInput => coefficient input.val)
      encBoundedInput encNat (fun input => 2 ^ (C * (budget input.val + 1)))
      (fun input => C * (budget input.val + 1)) := by
    obtain ⟨k, State, finiteState, tm, correct⟩ := machine
    exact ⟨k, State, finiteState, tm, fun input => correct input.val⟩
  have budgetBound (input : BoundedInput) : budget input.val + 1 ≤ 257 * bitBudget input := by
    have bounded := budget_le_bits input
    have positive : 1 ≤ bitBudget input := by
      unfold bitBudget
      nlinarith [Nat.zero_le input.val.val.1.log2]
    omega
  refine ⟨C * 257, restricted.mono (fun input => ?_) (fun input => ?_)⟩
  · apply Nat.pow_le_pow_right (by norm_num)
    simpa only [mul_assoc] using Nat.mul_le_mul_left C (budgetBound input)
  · simpa only [mul_assoc] using Nat.mul_le_mul_left C (budgetBound input)

end NtimeDspace.HermiteCoefficientMachine
