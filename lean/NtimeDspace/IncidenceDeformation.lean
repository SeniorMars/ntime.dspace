import NtimeDspace.PolynomialFacts
import NtimeDspace.FormulaCounter

/-!
# From label coefficients to concrete formula coefficients

An incidence occupies its label in one copy, with no two incidences occupying
the same `(copy,label)` pair. Its coefficient of a declared variable is the
sum of the label-to-label coefficients of incidences carrying that variable
in its copy. This is the paper's substitution of the occupied-position vector.

The origin and polynomial degree properties are proved for this explicit
finite sum and transferred to the concrete formula scalar-counting theorem.
Placement construction and machine resources remain separate obligations.
-/

namespace NtimeDspace.IncidenceDeformation

noncomputable section

open scoped BigOperators

section Incidences

variable {Inc Var Copy Label K : Type*}
variable [Fintype Inc] [DecidableEq Copy] [DecidableEq Var] [DecidableEq Label]
variable [CommRing K]

/-- Explicitly substitute the variable carried by every occupied position
in the chosen incidence's copy. Repeated occurrences are kept distinct. -/
def incidenceCoefficient (variableOf : Inc → Var) (copy : Inc → Copy) (label : Inc → Label)
    (coefficient : Label → Label → Polynomial K) (inc : Inc) (v : Var) : Polynomial K :=
  ∑ other, if copy other = copy inc ∧ variableOf other = v
    then coefficient (label inc) (label other) else 0

/-- Injective placement plus the label Kronecker identity gives the actual
variable Kronecker identity, even when several incidences carry one variable. -/
theorem incidenceCoefficient_origin (variableOf : Inc → Var) (copy : Inc → Copy)
    (label : Inc → Label) (coefficient : Label → Label → Polynomial K)
    (placement : Function.Injective (fun inc => (copy inc, label inc)))
    (origin : ∀ first second, (coefficient first second).eval 0 =
      if first = second then 1 else 0) (inc : Inc) (v : Var) :
    (incidenceCoefficient variableOf copy label coefficient inc v).eval 0 =
      if variableOf inc = v then 1 else 0 := by
  classical
  simp only [incidenceCoefficient, NtimeDspace.PolynomialFacts.eval_finset_sum, apply_ite,
    Polynomial.eval_zero, origin]
  rw [Finset.sum_eq_single inc]
  · by_cases h : variableOf inc = v <;> simp [h]
  · intro other _ different
    by_cases h : copy other = copy inc ∧ variableOf other = v
    · have labels_differ : label inc ≠ label other := by
        intro heq
        apply different
        exact placement (Prod.ext h.1 heq.symm)
      simp [h, labels_differ]
    · simp [h]
  · simp

omit [DecidableEq Label] in
/-- Summing by declared variable is exactly substitution of all occupied
positions, without merging or dropping repeated incidences. -/
theorem incidenceCoefficient_weighted_sum [Fintype Var]
    (variableOf : Inc → Var) (copy : Inc → Copy) (label : Inc → Label)
    (coefficient : Label → Label → Polynomial K) (inc : Inc) (weight : Var → Polynomial K) :
    (∑ v, incidenceCoefficient variableOf copy label coefficient inc v * weight v) =
      ∑ other, if copy other = copy inc then
        coefficient (label inc) (label other) * weight (variableOf other) else 0 := by
  simp only [incidenceCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro other _
  by_cases hcopy : copy other = copy inc
  · simp [hcopy, eq_comm]
  · simp [hcopy]

omit [DecidableEq Label] in
theorem incidenceCoefficient_degree (variableOf : Inc → Var) (copy : Inc → Copy)
    (label : Inc → Label) (coefficient : Label → Label → Polynomial K) (bound : ℕ)
    (degree_bound : ∀ first second, (coefficient first second).natDegree ≤ bound)
    (inc : Inc) (v : Var) :
    (incidenceCoefficient variableOf copy label coefficient inc v).natDegree ≤ bound := by
  unfold incidenceCoefficient
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro other _
  split_ifs
  · exact degree_bound (label inc) (label other)
  · simp

end Incidences

section Formula

variable {n : ℕ} {Copy Label K : Type*}
variable [DecidableEq Copy] [DecidableEq Label] [CommRing K]

def incidenceVariable (formula : Formula n) (inc : FormulaCounter.Incidence formula) : Fin n :=
  (formula.clauses[inc.1].literals[inc.2]).index

/-- FormulaCounter's clause/literal indexing of the occupied-position sum. -/
def formulaCoefficients (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → Label)
    (coefficient : Label → Label → Polynomial K) : CountingPolynomial.Coefficients formula K :=
  fun clause literal v =>
    incidenceCoefficient (incidenceVariable formula) copy label coefficient ⟨clause, literal⟩ v

omit [DecidableEq Label] in
theorem formula_incidenceForm_eq_occupied_sum (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → Label)
    (coefficient : Label → Label → Polynomial K)
    (inc : FormulaCounter.Incidence formula) (assignment : Assignment n) :
    CountingPolynomial.incidenceForm formula (formulaCoefficients formula copy label coefficient)
        inc.1 inc.2 assignment =
      ∑ other, if copy other = copy inc then
        coefficient (label inc) (label other) *
          Polynomial.C (CountingPolynomial.boolValue (assignment (incidenceVariable formula other)))
        else 0 := by
  exact incidenceCoefficient_weighted_sum (incidenceVariable formula) copy label coefficient inc
    (fun v => Polynomial.C (CountingPolynomial.boolValue (assignment v)))

theorem formulaCoefficients_origin (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → Label)
    (coefficient : Label → Label → Polynomial K)
    (placement : Function.Injective (fun inc => (copy inc, label inc)))
    (origin : ∀ first second, (coefficient first second).eval 0 =
      if first = second then 1 else 0) :
    CountingPolynomial.OriginCondition formula (formulaCoefficients formula copy label coefficient) := by
  intro clause literal v
  change (incidenceCoefficient (incidenceVariable formula) copy label coefficient ⟨clause, literal⟩ v).eval 0 = _
  rw [incidenceCoefficient_origin (incidenceVariable formula) copy label coefficient placement origin]
  simp only [incidenceVariable, eq_comm]

omit [DecidableEq Label] in
theorem formulaCoefficients_degree (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → Label)
    (coefficient : Label → Label → Polynomial K) (bound : ℕ)
    (degree_bound : ∀ first second, (coefficient first second).natDegree ≤ bound)
    (clause : Fin formula.clauses.length)
    (literal : Fin (formula.clauses[clause]).literals.length) (v : Fin n) :
    (formulaCoefficients formula copy label coefficient clause literal v).natDegree ≤ bound :=
  incidenceCoefficient_degree (incidenceVariable formula) copy label coefficient bound degree_bound
    ⟨clause, literal⟩ v

end Formula

section ScalarCounter

variable {n p : ℕ} [Fact p.Prime] {Copy Label : Type*}
variable [DecidableEq Copy] [DecidableEq Label]

/-- Concrete label coefficients and injective placement suffice for the actual
CNF scalar expression to recover the count. Both formula-level coefficient
hypotheses are discharged by the explicit construction above. -/
theorem scalarFormulaExpression_correct (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → Label)
    (coefficient : Label → Label → Polynomial (ZMod p))
    (placement : Function.Injective (fun inc => (copy inc, label inc)))
    (origin : ∀ first second, (coefficient first second).eval 0 =
      if first = second then 1 else 0)
    (nodes : Finset (ZMod p)) (order bound : ℕ)
    (positive : 0 < order) (below_prime : order < p)
    (nonzero_nodes : ∀ node ∈ nodes, node ≠ 0)
    (degree_bound : ∀ first second, (coefficient first second).natDegree ≤ bound)
    (interpolation_capacity : FormulaCounter.incidenceCount formula * bound < nodes.card * order)
    (no_alias : FormulaCounter.incidenceCount formula * bound ≤ p - 2) :
    FormulaCounter.scalarFormulaExpression formula
        (formulaCoefficients formula copy label coefficient) nodes order =
      (satisfyingCount formula : ZMod p) := by
  exact FormulaCounter.scalarFormulaExpression_correct_of_incidence_budget formula
    (formulaCoefficients formula copy label coefficient)
    (formulaCoefficients_origin formula copy label coefficient placement origin)
    nodes order bound positive below_prime nonzero_nodes
    (formulaCoefficients_degree formula copy label coefficient bound degree_bound)
    interpolation_capacity no_alias

end ScalarCounter

end

end NtimeDspace.IncidenceDeformation
