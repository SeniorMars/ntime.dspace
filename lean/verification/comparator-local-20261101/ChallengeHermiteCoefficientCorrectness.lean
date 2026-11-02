-- Frozen source-based contract. The sorry is an intentional challenge hole.
import NtimeDspace.HermiteCoefficientMachine
import NtimeDspace.SelectedCounter

namespace NtimeDspace.HermiteCoefficientCorrectness
open Turing Turing.MultiTapeTM HermiteRecovery

noncomputable def weightPolynomial (input : HermiteCoefficientMachine.Input) :
    Polynomial (ZMod input.val.1) := by
  let : Fact input.val.1.Prime := ⟨input.property.1⟩
  exact nodeWeight
    (Finset.univ.image (SelectedCounter.nodeValue (p := input.val.1) (nodes := input.val.2.1)))
    (SelectedCounter.nodeValue (p := input.val.1)
      (⟨input.val.2.2.1, input.property.2⟩ : Fin input.val.2.1)) input.val.2.2.2.1

def WeightValid (input : HermiteCoefficientMachine.BoundedInput) : Prop :=
  input.val.val.2.1 < input.val.val.1 ∧ 0 < input.val.val.2.2.2.1 ∧
    input.val.val.2.2.2.2 < input.val.val.2.2.2.1

abbrev WeightInput := {input : HermiteCoefficientMachine.BoundedInput // WeightValid input}

def encWeightInput : WeightInput ↪ List Bool :=
  (⟨Subtype.val, Subtype.val_injective⟩ : WeightInput ↪ HermiteCoefficientMachine.BoundedInput).trans
    HermiteCoefficientMachine.encBoundedInput

noncomputable def weightCoefficient (input : WeightInput) : ℕ :=
  ((weightPolynomial input.val.val).coeff input.val.val.val.2.2.2.2).val

theorem weightCoefficient_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace weightCoefficient encWeightInput encNat
      (fun input => 2 ^ (C * HermiteCoefficientMachine.bitBudget input.val))
      (fun input => C * HermiteCoefficientMachine.bitBudget input.val) := by
  sorry
end NtimeDspace.HermiteCoefficientCorrectness
