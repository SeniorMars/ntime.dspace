import NtimeDspace.UniformCountingLoop

/-!
A total scalar modular-counting entry point for bounded-occurrence formulas.
The uniform grouped construction is selected when its explicit input-size and
prime bounds hold. Otherwise an explicit binary-mask loop sums assignment
contributions; it never materializes the assignment list.

Bounded occurrence is a caller-supplied proposition, erased at execution. This
entry point does not run a hidden validation procedure. The fallback has no
sublinear-workspace claim, and neither branch has yet been compiled into the
full resource-bounded counting machine.
-/

namespace NtimeDspace.ModularCounting

open scoped BigOperators

variable {n : ℕ}

/-- An ordinary binary assignment counter with a field-valued accumulator. -/
def fallback (p : ℕ) (formula : Formula n) : ZMod p :=
  AssignmentLoop.sumAssignments n (fun assignment =>
    if formula.eval assignment then (1 : ZMod p) else 0) 0

/-- The one empty assignment at `n = 0` is included by the same scalar loop. -/
theorem fallback_correct (p : ℕ) (formula : Formula n) :
    fallback p formula = (satisfyingCount formula : ZMod p) := by
  simp only [fallback, AssignmentLoop.sumAssignments_correct, add_zero,
    satisfyingCount_eq_sum, Nat.cast_sum, Formula.contribution, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- The grouped branch is used exactly when its two numerical preconditions
hold. All other inputs use the explicit scalar assignment loop. -/
def countModP (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) : ZMod p :=
  if eligible : ParameterChoice.cost 6 ≤ n.log2 ∧ 4 * n ^ 2 < p then
    UniformCountingLoop.countModP p formula bounded eligible.1
  else fallback p formula

/-- All bounded-occurrence formulas and all prime moduli are covered, with no
large-input or prime-size hypothesis in the total correctness theorem. -/
theorem countModP_correct (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) :
    countModP p formula bounded = (satisfyingCount formula : ZMod p) := by
  unfold countModP
  split_ifs with eligible
  · exact UniformCountingLoop.countModP_correct p formula bounded eligible.1 eligible.2
  · exact fallback_correct p formula

/-- Resource refinements for the large-input construction can use this exact
branch equation, rather than a claim about the unrestricted fallback. -/
theorem countModP_eq_uniform (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (large : ParameterChoice.cost 6 ≤ n.log2)
    (prime_lower : 4 * n ^ 2 < p) :
    countModP p formula bounded = UniformCountingLoop.countModP p formula bounded large := by
  simp only [countModP, large, prime_lower, and_self, ↓reduceDIte]

theorem countModP_eq_fallback (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence)
    (ineligible : ¬ (ParameterChoice.cost 6 ≤ n.log2 ∧ 4 * n ^ 2 < p)) :
    countModP p formula bounded = fallback p formula := by
  simp only [countModP, ineligible, ↓reduceDIte]

end NtimeDspace.ModularCounting
