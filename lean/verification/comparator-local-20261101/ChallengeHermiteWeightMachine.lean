-- Frozen source-based contract. The sorry is an intentional challenge hole.
import NtimeDspace.HermiteWeightSpace

namespace NtimeDspace.HermiteWeightMachine
open Turing Turing.MultiTapeTM HermiteWeightLoop HermiteWeightBudget

abbrev PositiveHeader := {header : Header // 0 < order header}

def encPositiveHeader : PositiveHeader ↪ List Bool :=
  (⟨Subtype.val, Subtype.val_injective⟩ : PositiveHeader ↪ Header).trans encHeader

theorem polynomialWeight_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace (fun header : PositiveHeader => polynomialWeight header.val)
      encPositiveHeader encNat (fun header => 2 ^ (C * bitBudget header.val))
      (fun header => C * bitBudget header.val) := by
  sorry
end NtimeDspace.HermiteWeightMachine
