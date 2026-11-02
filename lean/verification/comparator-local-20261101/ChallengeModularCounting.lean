-- Frozen source-based contract. The sorry is an intentional challenge hole.
import NtimeDspace.UniformCountingLoop

namespace NtimeDspace.ModularCounting
variable {n : ℕ}

def fallback (p : ℕ) (formula : Formula n) : ZMod p :=
  AssignmentLoop.sumAssignments n (fun assignment =>
    if formula.eval assignment then (1 : ZMod p) else 0) 0

def countModP (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) : ZMod p :=
  if eligible : ParameterChoice.cost 6 ≤ n.log2 ∧ 4 * n ^ 2 < p then
    UniformCountingLoop.countModP p formula bounded eligible.1
  else fallback p formula

theorem countModP_correct (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) :
    countModP p formula bounded = (satisfyingCount formula : ZMod p) := by
  sorry
end NtimeDspace.ModularCounting
