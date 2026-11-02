import NtimeDspace.FormulaInput
import NtimeDspace.FormulaCounter
import NtimeDspace.HashVariance

/-!
The manuscript's incidence population contains the actual literal occurrences
and one dummy incidence for every unused declared variable. The dummy factor is
distinct from all clause factors. Empty clauses remain legal and have degree
zero. Bounds concern this finite population, not enumeration workspace.
-/

namespace NtimeDspace.FormulaIncidences

open scoped BigOperators

abbrev LiteralIncidence {n : ℕ} (formula : Formula n) := FormulaCounter.Incidence formula

abbrev UnusedVariable {n : ℕ} (formula : Formula n) :=
  {v : Fin n // formula.occurrences v = 0}

/-- Clause factors and a separate constant-one factor for each unused variable. -/
abbrev Factor {n : ℕ} (formula : Formula n) :=
  Fin formula.clauses.length ⊕ UnusedVariable formula

abbrev Incidence {n : ℕ} (formula : Formula n) :=
  LiteralIncidence formula ⊕ UnusedVariable formula

def literalVariable {n : ℕ} (formula : Formula n) (inc : LiteralIncidence formula) : Fin n :=
  (formula.clauses[inc.1].literals[inc.2]).index

def variableOf {n : ℕ} (formula : Formula n) : Incidence formula → Fin n
  | Sum.inl literal => literalVariable formula literal
  | Sum.inr unused => unused.val

def factorOf {n : ℕ} (formula : Formula n) : Incidence formula → Factor formula
  | Sum.inl literal => Sum.inl literal.1
  | Sum.inr unused => Sum.inr unused

def variableDegree {n : ℕ} (formula : Formula n) (v : Fin n) : ℕ :=
  ∑ inc : Incidence formula, if variableOf formula inc = v then 1 else 0

def factorDegree {n : ℕ} (formula : Formula n) (factor : Factor formula) : ℕ :=
  ∑ inc : Incidence formula, if factorOf formula inc = factor then 1 else 0

def population {n : ℕ} (formula : Formula n) : ℕ := Fintype.card (Incidence formula)

theorem sum_positions_eq_list {α : Type*} (values : List α) (weight : α → ℕ) :
    (∑ position : Fin values.length, weight values[position]) =
      (values.map weight).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (fun position : Fin values.length => weight values[(position : ℕ)])).sum = _
  rw [List.ofFn_getElem_eq_map]

theorem sum_literal_indicator {n : ℕ} (literals : List (Literal n)) (v : Fin n) :
    (literals.map fun literal => if literal.index = v then 1 else 0).sum =
      (literals.filter fun literal => literal.index == v).length := by
  induction literals with
  | nil => simp
  | cons literal literals ih =>
    by_cases h : literal.index = v <;> simp [h, ih, Nat.add_comm]

theorem literal_variable_degree {n : ℕ} (formula : Formula n) (v : Fin n) :
    (∑ inc : LiteralIncidence formula, if literalVariable formula inc = v then 1 else 0) =
      formula.occurrences v := by
  rw [Fintype.sum_sigma]
  change (∑ clause : Fin formula.clauses.length,
    ∑ literal : Fin formula.clauses[clause].literals.length,
      if formula.clauses[clause].literals[literal].index = v then 1 else 0) = _
  have hclause (clause : Fin formula.clauses.length) :
      (∑ literal : Fin formula.clauses[clause].literals.length,
        if formula.clauses[clause].literals[literal].index = v then 1 else 0) =
        (formula.clauses[clause].literals.filter fun literal => literal.index == v).length := by
    calc
      _ = (formula.clauses[clause].literals.map
          fun literal => if literal.index = v then 1 else 0).sum :=
        sum_positions_eq_list _ (fun literal : Literal n => if literal.index = v then 1 else 0)
      _ = _ := sum_literal_indicator _ v
  simp_rw [hclause]
  exact sum_positions_eq_list formula.clauses
    (fun clause => (clause.literals.filter fun literal => literal.index == v).length)

theorem unused_variable_degree {n : ℕ} (formula : Formula n) (v : Fin n) :
    (∑ unused : UnusedVariable formula, if unused.val = v then 1 else 0) =
      if formula.occurrences v = 0 then 1 else 0 := by
  classical
  by_cases h : formula.occurrences v = 0
  · rw [if_pos h]
    have heq (unused : UnusedVariable formula) :
        unused.val = v ↔ unused = ⟨v, h⟩ := by
      constructor
      · intro hv; apply Subtype.ext; exact hv
      · intro heq; exact congrArg Subtype.val heq
    simp_rw [heq]
    simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro unused _
    have hv : unused.val ≠ v := by
      intro heq
      exact h (heq ▸ unused.property)
    simp [hv]

theorem variableDegree_eq {n : ℕ} (formula : Formula n) (v : Fin n) :
    variableDegree formula v = formula.occurrences v +
      if formula.occurrences v = 0 then 1 else 0 := by
  unfold variableDegree
  rw [Fintype.sum_sum_type]
  exact congrArg₂ Nat.add (literal_variable_degree formula v) (unused_variable_degree formula v)

theorem variableDegree_pos {n : ℕ} (formula : Formula n) (v : Fin n) :
    1 ≤ variableDegree formula v := by
  rw [variableDegree_eq]
  split_ifs <;> omega

theorem variableDegree_le_three {n : ℕ} (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (v : Fin n) :
    variableDegree formula v ≤ 3 := by
  rw [variableDegree_eq]
  have h := bounded.2.2 v
  split_ifs <;> omega

theorem factorDegree_clause {n : ℕ} (formula : Formula n)
    (clause : Fin formula.clauses.length) :
    factorDegree formula (Sum.inl clause) = formula.clauses[clause].literals.length := by
  unfold factorDegree
  rw [Fintype.sum_sum_type]
  simp only [factorOf, Sum.inl.injEq, Sum.inr_ne_inl, if_false,
    Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_sigma]
  change (∑ c : Fin formula.clauses.length,
    ∑ _literal : Fin formula.clauses[c].literals.length,
      if c = clause then 1 else 0) = _
  have hc (c : Fin formula.clauses.length) :
      (∑ _literal : Fin formula.clauses[c].literals.length,
        if c = clause then 1 else 0) =
        if c = clause then formula.clauses[c].literals.length else 0 := by
    by_cases h : c = clause <;> simp [h]
  simp_rw [hc]
  simp

theorem factorDegree_dummy {n : ℕ} (formula : Formula n) (unused : UnusedVariable formula) :
    factorDegree formula (Sum.inr unused) = 1 := by
  unfold factorDegree
  rw [Fintype.sum_sum_type]
  simp [factorOf]

theorem factorDegree_le_three {n : ℕ} (formula : Formula n) (factor : Factor formula) :
    factorDegree formula factor ≤ 3 := by
  cases factor with
  | inl clause => simpa [factorDegree_clause] using formula.clauses[clause].width_le_three
  | inr unused => simp [factorDegree_dummy]

theorem sum_variableDegree {n : ℕ} (formula : Formula n) :
    (∑ v : Fin n, variableDegree formula v) = population formula := by
  unfold variableDegree population
  rw [Finset.sum_comm]
  simp

theorem variables_le_population {n : ℕ} (formula : Formula n) :
    n ≤ population formula := by
  calc
    n = ∑ _v : Fin n, 1 := by simp
    _ ≤ ∑ v : Fin n, variableDegree formula v :=
      Finset.sum_le_sum (fun v _ => variableDegree_pos formula v)
    _ = _ := sum_variableDegree formula

theorem population_le_three_variables {n : ℕ} (formula : Formula n)
    (bounded : formula.BoundedOccurrence) : population formula ≤ 3 * n := by
  rw [← sum_variableDegree]
  calc
    _ ≤ ∑ _v : Fin n, 3 :=
      Finset.sum_le_sum (fun v _ => variableDegree_le_three formula bounded v)
    _ = _ := by simp [Nat.mul_comm]

theorem literal_card_eq {n : ℕ} (formula : Formula n) :
    Fintype.card (LiteralIncidence formula) = FormulaCounter.incidenceCount formula := by
  simp [LiteralIncidence, FormulaCounter.Incidence, FormulaCounter.incidenceCount,
    Fintype.card_sigma]

theorem population_eq_literals_add_unused {n : ℕ} (formula : Formula n) :
    population formula = FormulaCounter.incidenceCount formula +
      Fintype.card (UnusedVariable formula) := by
  simp only [population, Fintype.card_sum, literal_card_eq]

theorem literalCount_le_population {n : ℕ} (formula : Formula n) :
    FormulaCounter.incidenceCount formula ≤ population formula := by
  rw [population_eq_literals_add_unused]
  omega

theorem variable_bucketCount_eq {n : ℕ} (formula : Formula n) (v : Fin n) :
    HashVariance.bucketCount (variableOf formula) v = (variableDegree formula v : ℚ) := by
  simp only [HashVariance.bucketCount, variableDegree, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem factor_bucketCount_eq {n : ℕ} (formula : Formula n) (factor : Factor formula) :
    HashVariance.bucketCount (factorOf formula) factor = (factorDegree formula factor : ℚ) := by
  simp only [HashVariance.bucketCount, factorDegree, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem variable_bucketCount_le_three {n : ℕ} (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (v : Fin n) :
    HashVariance.bucketCount (variableOf formula) v ≤ 3 := by
  rw [variable_bucketCount_eq]
  exact_mod_cast variableDegree_le_three formula bounded v

theorem factor_bucketCount_le_three {n : ℕ} (formula : Formula n) (factor : Factor formula) :
    HashVariance.bucketCount (factorOf formula) factor ≤ 3 := by
  rw [factor_bucketCount_eq]
  exact_mod_cast factorDegree_le_three formula factor

/-- Under the no-repeated-variable condition, positions really are distinct
factor-variable incidences rather than multiplicities at the same pair. -/
theorem literal_endpoints_injective {n : ℕ} (formula : Formula n)
    (bounded : formula.BoundedOccurrence) :
    Function.Injective (fun inc : LiteralIncidence formula =>
      (inc.1, literalVariable formula inc)) := by
  rintro ⟨clause, literal⟩ ⟨otherClause, otherLiteral⟩ heq
  have hc : clause = otherClause := congrArg Prod.fst heq
  subst otherClause
  have hv : formula.clauses[clause].literals[literal].index =
      formula.clauses[clause].literals[otherLiteral].index := congrArg Prod.snd heq
  have hn := bounded.1 formula.clauses[clause] (List.getElem_mem _)
  have hli : (literal : ℕ) < (formula.clauses[clause].literals.map Literal.index).length :=
    by simpa only [List.length_map] using literal.isLt
  have hri : (otherLiteral : ℕ) < (formula.clauses[clause].literals.map Literal.index).length :=
    by simpa only [List.length_map] using otherLiteral.isLt
  have hindex : (literal : ℕ) = otherLiteral :=
    hn.getElem_inj_iff.mp (show
      (formula.clauses[clause].literals.map Literal.index)[literal.val] =
      (formula.clauses[clause].literals.map Literal.index)[otherLiteral.val] from by simpa using hv)
  have hl : literal = otherLiteral := Fin.ext hindex
  subst otherLiteral
  rfl

theorem endpoints_injective {n : ℕ} (formula : Formula n)
    (bounded : formula.BoundedOccurrence) :
    Function.Injective (fun inc : Incidence formula =>
      (factorOf formula inc, variableOf formula inc)) := by
  intro first second heq
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      have hf : first.1 = second.1 := Sum.inl.inj (congrArg Prod.fst heq)
      have hv : literalVariable formula first = literalVariable formula second :=
        congrArg Prod.snd heq
      exact congrArg Sum.inl (literal_endpoints_injective formula bounded (Prod.ext hf hv))
    | inr second =>
      have hf : (Sum.inl first.1 : Factor formula) = Sum.inr second := congrArg Prod.fst heq
      cases hf
  | inr first =>
    cases second with
    | inl second =>
      have hf : (Sum.inr first : Factor formula) = Sum.inl second.1 := congrArg Prod.fst heq
      cases hf
    | inr second => exact congrArg Sum.inr (Sum.inr.inj (congrArg Prod.fst heq))

end NtimeDspace.FormulaIncidences
