/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.ComplexityReuse
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Compose

-- upstream: local-only (presentation bridge for the weighted counting application)

/-!
# Computing through a virtual presentation

`simultaneous_bounds` composes an ordinary presentation-generating machine with
an ordinary machine acting on that presentation. The imported composition
simulator recomputes intermediate input symbols without storing the entire
presentation. The workspace premise charges both machines and the binary
counters for the original and intermediate input lengths.

Configuration counting gives simultaneous bounds for the same composed machine.
The generator and consumer machine theorems remain explicit hypotheses; this
module does not establish either machine for weighted counting.
-/

namespace NtimeDspace.WeightedPresentation

open Turing Turing.MultiTapeTM

/-- Compose through a virtual intermediate word, then count configurations of
that composed machine. The original time bounds need no quantitative estimates;
they certify termination. All workspace and length-counter charges are explicit. -/
theorem simultaneous_bounds {α β γ : Type} {encIn : α ↪ List Bool}
    {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool} {f : α → β} {g : β → γ}
    {tf sf : α → ℕ} {tg sg : β → ℕ}
    (hf : ComputableInTimeAndSpace f encIn encMid tf sf)
    (hg : ComputableInTimeAndSpace g encMid encOut tg sg)
    (budget : α → ℕ) (K : ℕ)
    (logarithmic : ∀ a, (encIn a).length.log2 + 1 ≤ budget a)
    (workspace : ∀ a,
      sf a + sg (f a) + (encNat ((encIn a).length + 1)).length +
        (encNat ((encMid (f a)).length + 1)).length + 1 ≤ K * budget a) :
    ∃ C, ComputableInTimeAndSpace (g ∘ f) encIn encOut
      (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  obtain ⟨c, composed⟩ := hf.comp_space hg
  apply ComplexityReuse.exists_exponential_time_of_linear_space (c * K)
    (logarithmic := logarithmic)
  refine composed.mono (fun _ => le_rfl) fun a => ?_
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c (workspace a)

end NtimeDspace.WeightedPresentation
