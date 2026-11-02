import NtimeDspace.Counting

/-! Formula input predicates independent of the machine-model dependency. -/

namespace NtimeDspace

/-- Number of literal occurrences of a declared variable. -/
def Formula.occurrences {n : ℕ} (formula : Formula n) (v : Fin n) : ℕ :=
  ((formula.clauses.map fun clause =>
    (clause.literals.filter fun literal => literal.index == v).length)).sum

/-- Canonical bounded occurrence: no repeated variable within a clause,
at most one empty clause, and at most three occurrences of each variable. -/
def Formula.BoundedOccurrence {n : ℕ} (formula : Formula n) : Prop :=
  (∀ clause ∈ formula.clauses, (clause.literals.map Literal.index).Nodup) ∧
  (formula.clauses.filter fun clause => clause.literals.isEmpty).length ≤ 1 ∧
  ∀ v, formula.occurrences v ≤ 3

end NtimeDspace
