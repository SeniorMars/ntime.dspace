import NtimeDspace.FormulaInput
import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
The resource theorem's interface. This file declares a proposition to prove,
not a theorem claiming that the counter already satisfies it.

The encodings and resource functions are parameters until canonical encoders
and the concrete machine have been implemented. In particular, choosing an
encoding that already contains the answer would not discharge our obligation.
The exponent must also be instantiated nonvacuously: for `c₀ ≤ 2`, the displayed
modulus interval has no inputs. An eventual theorem must fix an exponent above
two and prove the required prime availability for all sufficiently large sizes.
-/

namespace NtimeDspace

/-- Inputs to the manuscript's modular counting theorem, at a fixed exponent. -/
structure ModularInput (c₀ : ℕ) where
  variableCount : ℕ
  formula : Formula variableCount
  bounded : formula.BoundedOccurrence
  modulus : ℕ
  prime : modulus.Prime
  lower : 4 * variableCount ^ 2 < modulus
  upper : modulus ≤ variableCount ^ c₀

def modularSpecification {c₀ : ℕ} (input : ModularInput c₀) : ℕ :=
  satisfyingCount input.formula % input.modulus

/-- One finite-state binary machine must meet both bounds on every input.
CSLib counts cells visited along every computation prefix, including scratch
tapes, rather than the size of a returned object or the nonzero tape cells. -/
def ModularCounterResourceClaim (c₀ : ℕ)
    (encodeInput : ModularInput c₀ ↪ List Bool)
    (encodeOutput : ℕ ↪ List Bool)
    (timeBound spaceBound : ModularInput c₀ → ℕ) : Prop :=
  Turing.MultiTapeTM.ComputableInTimeAndSpace modularSpecification
    encodeInput encodeOutput timeBound spaceBound

end NtimeDspace
