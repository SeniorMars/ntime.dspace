import NtimeDspace.IncidenceEvaluation
import NtimeDspace.FormulaIncidences
import NtimeDspace.InputEncoding

/-!
Scalar access to the complete incidence population: literal positions plus
one dummy incidence for each unused declared variable. Occurrence counts are
computed by clause/literal scans. A declared-variable scan tests those scalar
counts and supplies unused-variable witnesses only in erased proofs. No list
of unused variables or of all incidences is constructed at runtime.

Explicit factor and incidence identifiers preserve the original input order,
with gaps permitted. Their injectivity supports later predecessor-rank scans;
they do not require a chosen finite-type enumeration or an inverse table.
These are arithmetic interfaces, not machine-resource bounds.
-/

namespace NtimeDspace.PopulationAccess

open scoped BigOperators
open GroupedAssignmentEvaluation

variable {n : ℕ}

/-- Compute occurrences without constructing any filtered literal list. -/
def occurrences (formula : Formula n) (v : Fin n) : ℕ :=
  IncidenceEvaluation.scanIncidences formula (fun inc =>
    if IncidenceEvaluation.variableOf formula inc = v then 1 else 0) 0

theorem occurrences_correct (formula : Formula n) (v : Fin n) :
    occurrences formula v = formula.occurrences v := by
  rw [occurrences, IncidenceEvaluation.scanIncidences_correct, add_zero]
  exact FormulaIncidences.literal_variable_degree formula v

/-- Scan the declared variables, emitting a dummy only after its scalar
occurrence count is zero. The subtype proof has no runtime representation. -/
def scanUnused {R : Type*} [AddMonoid R] (formula : Formula n)
    (term : FormulaIncidences.UnusedVariable formula → R) (accumulator : R) : R :=
  scanSum (fun v : Fin n =>
    if unused : occurrences formula v = 0 then
      term ⟨v, by rw [← occurrences_correct]; exact unused⟩ else 0) accumulator

theorem scanUnused_correct {R : Type*} [AddCommMonoid R] (formula : Formula n)
    (term : FormulaIncidences.UnusedVariable formula → R) (accumulator : R) :
    scanUnused formula term accumulator =
      (∑ unused : FormulaIncidences.UnusedVariable formula, term unused) + accumulator := by
  rw [scanUnused, scanSum_correct]
  congr 1
  simp_rw [occurrences_correct]
  rw [Finset.sum_dite]
  simp
  apply Finset.sum_bij (fun index _ =>
    (⟨index.val, by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using index.property⟩ :
      FormulaIncidences.UnusedVariable formula))
  · intro index _
    exact Finset.mem_univ _
  · intro first _ second _ same
    apply Subtype.ext
    exact congrArg (fun unused : FormulaIncidences.UnusedVariable formula => unused.val) same
  · intro unused _
    refine ⟨⟨unused.val, by simp [unused.property]⟩, ?_, ?_⟩
    · exact Finset.mem_attach _ _
    · rfl
  · intro index _
    rfl

/-- Iterate literal positions and unused-variable dummies using scalar scans.
The callback sees one incidence at a time, never a materialized population. -/
def scanPopulation {R : Type*} [AddMonoid R] (formula : Formula n)
    (term : FormulaIncidences.Incidence formula → R) (accumulator : R) : R :=
  scanUnused formula (fun unused => term (Sum.inr unused))
    (IncidenceEvaluation.scanIncidences formula (fun literal => term (Sum.inl literal)) accumulator)

theorem scanPopulation_correct {R : Type*} [AddCommMonoid R] (formula : Formula n)
    (term : FormulaIncidences.Incidence formula → R) (accumulator : R) :
    scanPopulation formula term accumulator =
      (∑ inc : FormulaIncidences.Incidence formula, term inc) + accumulator := by
  rw [scanPopulation, scanUnused_correct, IncidenceEvaluation.scanIncidences_correct,
    Fintype.sum_sum_type]
  ac_rfl

def populationCount (formula : Formula n) : ℕ := scanPopulation formula (fun _ => 1) 0

theorem populationCount_correct (formula : Formula n) :
    populationCount formula = FormulaIncidences.population formula := by
  simp [populationCount, scanPopulation_correct, FormulaIncidences.population]

/-- Clause identifiers precede declared-variable identifiers. Gaps correspond
to variables that are used and therefore have no dummy factor. -/
def factorNumber (formula : Formula n) :
    FormulaIncidences.Factor formula → Fin (formula.clauses.length + n)
  | Sum.inl clause => ⟨clause.val, by have := clause.isLt; omega⟩
  | Sum.inr unused => ⟨formula.clauses.length + unused.val.val, by have := unused.val.isLt; omega⟩

theorem factorNumber_injective (formula : Formula n) : Function.Injective (factorNumber formula) := by
  intro first second same
  have numbers := congrArg Fin.val same
  cases first with
  | inl first =>
    cases second with
    | inl second => exact congrArg Sum.inl (Fin.ext numbers)
    | inr second =>
      change first.val = formula.clauses.length + second.val.val at numbers
      have := first.isLt
      omega
  | inr first =>
    cases second with
    | inl second =>
      change formula.clauses.length + first.val.val = second.val at numbers
      have := second.isLt
      omega
    | inr second =>
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Fin.ext
      change formula.clauses.length + first.val.val = formula.clauses.length + second.val.val at numbers
      omega

/-- Three slots per clause preserve literal positions; unused-variable
dummies follow them. Empty or short clauses merely leave unused slots. -/
def incidenceNumber (formula : Formula n) :
    FormulaIncidences.Incidence formula → Fin (3 * formula.clauses.length + n)
  | Sum.inl literal => ⟨3 * literal.1.val + literal.2.val, by
      have clause_bound := literal.1.isLt
      have literal_bound := literal.2.isLt
      have width := formula.clauses[literal.1].width_le_three
      omega⟩
  | Sum.inr unused => ⟨3 * formula.clauses.length + unused.val.val, by
      have := unused.val.isLt
      omega⟩

theorem incidenceNumber_injective (formula : Formula n) :
    Function.Injective (incidenceNumber formula) := by
  intro first second same
  have numbers := congrArg Fin.val same
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      obtain ⟨clause, literal⟩ := first
      obtain ⟨otherClause, otherLiteral⟩ := second
      change 3 * clause.val + literal.val = 3 * otherClause.val + otherLiteral.val at numbers
      have left_width := formula.clauses[clause].width_le_three
      have right_width := formula.clauses[otherClause].width_le_three
      have left_bound := literal.isLt
      have right_bound := otherLiteral.isLt
      have same_clause : clause = otherClause := Fin.ext (by omega)
      subst otherClause
      have same_literal : literal = otherLiteral := Fin.ext (by omega)
      subst otherLiteral
      rfl
    | inr second =>
      change 3 * first.1.val + first.2.val = 3 * formula.clauses.length + second.val.val at numbers
      have clause_bound := first.1.isLt
      have literal_bound := first.2.isLt
      have width := formula.clauses[first.1].width_le_three
      omega
  | inr first =>
    cases second with
    | inl second =>
      change 3 * formula.clauses.length + first.val.val = 3 * second.1.val + second.2.val at numbers
      have clause_bound := second.1.isLt
      have literal_bound := second.2.isLt
      have width := formula.clauses[second.1].width_le_three
      omega
    | inr second =>
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Fin.ext
      change 3 * formula.clauses.length + first.val.val =
        3 * formula.clauses.length + second.val.val at numbers
      omega

/-- The common width for declared-variable and explicit factor identifiers. -/
def inputBits (formula : Formula n) : ℕ := (formula.clauses.length + n).log2 + 1

theorem clause_count_le (formula : Formula n) (bounded : formula.BoundedOccurrence) :
    formula.clauses.length ≤ 3 * n + 1 := InputEncoding.bounded_clause_count formula bounded

theorem inputBits_le (formula : Formula n) (bounded : formula.BoundedOccurrence) :
    inputBits formula ≤ (4 * n + 1).log2 + 1 := by
  have clauses := clause_count_le formula bounded
  have total : formula.clauses.length + n ≤ 4 * n + 1 := by omega
  apply Nat.add_le_add_right
  apply (Nat.le_log2 (by omega : 4 * n + 1 ≠ 0)).mpr
  by_cases zero : formula.clauses.length + n = 0
  · rw [zero]
    simp
  · exact (Nat.log2_self_le zero).trans total

end NtimeDspace.PopulationAccess
