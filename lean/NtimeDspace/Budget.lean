import NtimeDspace.DeciderValues
import NtimeDspace.TailParameters

/-!
# The space budget

`L k s c C0 n` is the number of bits allowed for every value of the decider at
input length `n`: polylogarithmic terms in `N` (and the block length), the
support budget, the measurement tuples, the group sizes and the schedules.
`C0` bounds the machine's constants. Each value the decider computes is below
`2^L`; `L = o(n)` is proved in `BudgetAsymptotics`.
-/

namespace NtimeDspace.Budget

open Parameters Cslib.Complexity.CountingSimulation ProgTerm

variable (k s c C0 : ℕ)

/-- The clock, the number of edges and the selected parameter at length `n`. -/
abbrev tN (n : ℕ) : ℕ := clk c n
abbrev NN (n : ℕ) : ℕ := edgesN k s (tN c n)
abbrev kN (n : ℕ) : ℕ := ParameterChoice.choose (NN k s c n)
abbrev lgN (n : ℕ) : ℕ := (NN k s c n).log2
abbrev bN (n : ℕ) : ℕ := blockLength (tN c n)

/-- The number of measurement-tuple coordinates: `r · copies · badCount`. -/
noncomputable def tupleWidth (n : ℕ) : ℕ :=
  Parameters.s (kN k s c n) * (2 * (2 * NN k s c n) / D (kN k s c n)) * TailParameters.badCount (kN k s c n)

/-- Polylogarithmic terms. -/
def polyPart (n : ℕ) : ℕ :=
  (C0 + 8) * (lgN k s c n + 3) ^ 3 + 8 * (bN c n + 1) * (C0 + 1) * (lgN k s c n + C0 + 3)

/-- **The budget.** -/
noncomputable def L (n : ℕ) : ℕ :=
  polyPart k s c C0 n + (SupportBudget.limit (NN k s c n) (kN k s c n) + 1) +
    tupleWidth k s c n * ((2 * D (kN k s c n) + 1).log2 + 1) +
    (2 * NN k s c n / Parameters.s (kN k s c n) + 1) + 2 * (k + 1) * numBlocks (tN c n) + C0 + 8

end NtimeDspace.Budget
