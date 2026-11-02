import NtimeDspace.SchedulePlacement

/-!
# The large-input grouped counting identity with selected parameters

This module fixes the bounded-search parameter, the consecutive nonzero field
nodes, the floor-centered parity window, and the Taylor order. The only
arithmetic assumptions in the final existence theorem are the manuscript's
large-input threshold and prime lower bound. Placement, grouping compatibility,
node conditions, interpolation capacity, and absence of aliasing are derived.

The result remains an identity of noncomputable finite algebraic expressions.
It does not construct a counting machine or bound work-tape space or time.
-/

namespace NtimeDspace.SelectedCounter

noncomputable section

open Parameters

/-- Consecutive nodes `1, …, Q`, reduced into the coefficient field. -/
def nodeValue {p nodes : ℕ} (node : Fin nodes) : ZMod p :=
  ((node.val + 1 : ℕ) : ZMod p)

theorem nodeValue_injective {p nodes : ℕ} (below_prime : nodes < p) :
    Function.Injective (nodeValue (p := p) (nodes := nodes)) := by
  intro first second same
  have first_small : first.val + 1 < p := (Nat.succ_le_of_lt first.isLt).trans_lt below_prime
  have second_small : second.val + 1 < p := (Nat.succ_le_of_lt second.isLt).trans_lt below_prime
  have values := congrArg ZMod.val same
  change (((first.val + 1 : ℕ) : ZMod p).val) =
    (((second.val + 1 : ℕ) : ZMod p).val) at values
  rw [ZMod.val_natCast_of_lt first_small, ZMod.val_natCast_of_lt second_small] at values
  apply Fin.ext
  omega

theorem nodeValue_nonzero {p nodes : ℕ} (below_prime : nodes < p) (node : Fin nodes) :
    nodeValue (p := p) node ≠ 0 := by
  intro zero
  have small : node.val + 1 < p := (Nat.succ_le_of_lt node.isLt).trans_lt below_prime
  have values := congrArg ZMod.val zero
  change (((node.val + 1 : ℕ) : ZMod p).val) = (0 : ZMod p).val at values
  rw [ZMod.val_natCast_of_lt small, ZMod.val_zero] at values
  omega

theorem two_nonzero {p : ℕ} (large : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro zero
  have divides := (ZMod.natCast_eq_zero_iff 2 p).mp zero
  have := Nat.le_of_dvd (by decide : 0 < 2) divides
  omega

theorem input_positive {n : ℕ} (large : ParameterChoice.cost 6 ≤ n.log2) : 0 < n := by
  by_contra not_positive
  have zero : n = 0 := by omega
  subst n
  norm_num [ParameterChoice.cost, s] at large

abbrev Seed {n : ℕ} (formula : Formula n) :=
  SchedulePlacement.Seed formula (Fin (Q (ParameterChoice.choose n))) (ParameterChoice.choose n)

abbrev Balanced {n : ℕ} (formula : Formula n) (seed : Seed formula) :=
  SchedulePlacement.Balanced formula (ParameterChoice.choose n) seed

/-- The actual grouped expression, with all numerical parameters fixed. -/
def expression {n p : ℕ} [Fact p.Prime] (formula : Formula n) (positive : 0 < n)
    (seed : Seed formula) (balanced : Balanced formula seed) : ZMod p :=
  GroupedCounter.groupedScalarExpression formula ⟨0, positive⟩
    (SchedulePlacement.literalCopy formula (ParameterChoice.choose n) seed balanced)
    (SchedulePlacement.literalLabel formula (ParameterChoice.choose n) seed)
    (SchedulePlacement.variableGroup formula (ParameterChoice.choose n) seed)
    (SchedulePlacement.clauseGroup formula (ParameterChoice.choose n) seed)
    nodeValue
    (CenteredWindow.start (TailParameters.center (ParameterChoice.choose n))
      (R (ParameterChoice.choose n)))
    (R (ParameterChoice.choose n)) (q n (ParameterChoice.choose n) + 1)

/-- Functional correctness for every balanced selected seed. Every scalar
recovery side condition is a consequence of the displayed input hypotheses. -/
theorem expression_correct {n p : ℕ} [Fact p.Prime]
    (formula : Formula n) (bounded : formula.BoundedOccurrence)
    (large : ParameterChoice.cost 6 ≤ n.log2) (prime_lower : 4 * n ^ 2 < p)
    (seed : Seed formula) (balanced : Balanced formula seed) :
    expression (p := p) formula (input_positive large) seed balanced =
      (satisfyingCount formula : ZMod p) := by
  have positive := input_positive large
  have six_le := ParameterChoice.six_le_selected n large
  have selected_positive : 0 < ParameterChoice.choose n := by omega
  have budget := ParameterChoice.admissible n
  obtain ⟨nodes_small, width_small, order_small, degree_small⟩ :=
    scalar_parameter_bounds n (ParameterChoice.choose n) p six_le positive budget prime_lower
  have prime_large : 2 < p := by nlinarith
  have incidences : FormulaCounter.incidenceCount formula ≤ 3 * n :=
    (FormulaIncidences.literalCount_le_population formula).trans
      (FormulaIncidences.population_le_three_variables formula bounded)
  have degree : FormulaCounter.incidenceCount formula * (R (ParameterChoice.choose n) - 1) ≤
      3 * n * R (ParameterChoice.choose n) :=
    Nat.mul_le_mul incidences (Nat.sub_le _ _)
  have capacity := degree.trans_lt (degree_below_QJ n (ParameterChoice.choose n) selected_positive)
  unfold expression
  exact SchedulePlacement.grouped_counter_correct formula ⟨0, positive⟩
    (ParameterChoice.choose n) seed balanced (two_nonzero prime_large)
    nodeValue (nodeValue_injective nodes_small) (nodeValue_nonzero nodes_small)
    (CenteredWindow.start (TailParameters.center (ParameterChoice.choose n))
      (R (ParameterChoice.choose n)))
    (R (ParameterChoice.choose n)) (q n (ParameterChoice.choose n) + 1)
    width_small (Nat.succ_pos _) order_small
    (by simpa only [Fintype.card_fin] using capacity) (degree.trans degree_small)

/-- Large-input finite-algebra counting correctness with no supplied seed,
placement, node, degree, or local-representation hypotheses. -/
theorem exists_correct_expression {n p : ℕ} [Fact p.Prime]
    (formula : Formula n) (bounded : formula.BoundedOccurrence)
    (large : ParameterChoice.cost 6 ≤ n.log2) (prime_lower : 4 * n ^ 2 < p) :
    ∃ seed : Seed formula, ∃ balanced : Balanced formula seed,
      expression (p := p) formula (input_positive large) seed balanced =
        (satisfyingCount formula : ZMod p) := by
  obtain ⟨seed, balanced⟩ := SchedulePlacement.exists_selected_schedule
    formula bounded (input_positive large) large
  exact ⟨seed, balanced, expression_correct formula bounded large prime_lower seed balanced⟩

/-- The same selected construction has the proved finite measurement-row
cardinality bound. This is not a work-tape-space statement. -/
theorem measurementRow_scaled {n : ℕ} (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (large : ParameterChoice.cost 6 ≤ n.log2) :
    Fintype.card (TailParameters.MeasurementRow (ParameterChoice.choose n)
      (SchedulePlacement.copyCount formula (Fin (Q (ParameterChoice.choose n)))
        (ParameterChoice.choose n))) * s (ParameterChoice.choose n) ^ 4 ≤ 2 * n := by
  have positive : 0 < ParameterChoice.choose n := by
    have := ParameterChoice.six_le_selected n large
    omega
  exact SchedulePlacement.measurementRow_scaled formula bounded (ParameterChoice.choose n) positive

end

end NtimeDspace.SelectedCounter
