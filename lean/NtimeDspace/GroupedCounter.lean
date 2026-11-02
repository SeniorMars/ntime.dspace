import NtimeDspace.ConcreteGroupedDeformation

/-!
# Correctness of the concrete grouped scalar expression

The expression defined here sums the actual grouped Taylor-data polynomials,
weighted by the concrete truncated reciprocal, over the deformation nodes and
nonzero field elements. It is not defined as the earlier ungrouped scalar
expression. Their equality is proved from the concrete local representation.

The final theorem recovers the independently defined satisfying-assignment
count modulo `p`, with placement, schedule compatibility, and interpolation
parameter hypotheses explicit. The fallback variable requires a nonempty
declared-variable set and is used only at unoccupied label positions.

Everything here is noncomputable finite algebra. No machine implementation,
running-time bound, or sublinear workspace claim is made.
-/

namespace NtimeDspace.GroupedCounter

noncomputable section

open scoped BigOperators
open ConcreteGroupedDeformation

variable {n r p : ℕ} [Fact p.Prime]
variable {Node Copy : Type*} [Fintype Node] [DecidableEq Node]
variable [Fintype Copy] [DecidableEq Copy]

/-- The explicitly grouped Taylor polynomial at one node, using constructed
occupied positions, integer measurement rows, and local clause factors. -/
def groupedNodePolynomial (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (variableGroup : Node → Fin n → Fin r)
    (clauseGroup : Node → Fin formula.clauses.length → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width order : ℕ) (node : Node) :
    Polynomial (ZMod p) :=
  let occupied := occupiedPositions copyOf labelOf
  let variableAt := storedVariable fallback (IncidenceDeformation.incidenceVariable formula) copyOf labelOf
  GroupedDeformation.groupedTaylorData formula
    (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width) (nodeValue node)
    (variableGroup node) (clauseGroup node) (r ^ (2 * Fintype.card Node))
    (measurementRow occupied variableAt (variableGroup node) start width)
    (measurementRow_norm occupied variableAt (variableGroup node) start width)
    (formulaLocalCoefficient formula copyOf labelOf occupied variableAt nodeValue start width node)
    (formulaMeasurementCoefficient formula copyOf labelOf start width) order

set_option maxHeartbeats 1000000 in
theorem groupedNodePolynomial_eq_taylorData (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (variableGroup : Node → Fin n → Fin r)
    (clauseGroup : Node → Fin formula.clauses.length → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width order : ℕ) (node : Node)
    (nonzero : nodeValue node ≠ 0)
    (variables_match : ∀ inc,
      variableGroup node (IncidenceDeformation.incidenceVariable formula inc) = (labelOf inc node).1)
    (clauses_match : ∀ inc, (labelOf inc node).2 = clauseGroup node inc.1) :
    groupedNodePolynomial formula fallback copyOf labelOf variableGroup clauseGroup
      nodeValue start width order node =
    TaylorTruncation.taylorData Finset.univ
      (DeformationTaylor.expandedPolynomial Finset.univ (FormulaCounter.factorPolynomial formula)
        (FormulaCounter.coefficients formula
          (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)) (nodeValue node))
      Polynomial.X order := by
  symm
  unfold groupedNodePolynomial
  apply GroupedDeformation.taylorData_eq_groupedTaylorData
  exact formula_localRepresentation_of_placement formula fallback copyOf labelOf placement
    (variableGroup node) (clauseGroup node) nodeValue start width node nonzero
    variables_match clauses_match

/-- The grouped scalar counter, with the node loop, nonzero-field loop,
reciprocal weight, and grouped Taylor polynomial all explicit. -/
def groupedScalarExpression (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (variableGroup : Node → Fin n → Fin r)
    (clauseGroup : Node → Fin formula.clauses.length → Fin r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width order : ℕ) : ZMod p :=
  (HermiteRecovery.nodeProduct (Finset.univ.image nodeValue) order).eval 0 *
    ∑ node : Node, ∑ z : (ZMod p)ˣ,
      (z : ZMod p) ^ (p - order) *
        (HermiteRecovery.nodeWeight (Finset.univ.image nodeValue) (nodeValue node) order).eval (z : ZMod p) *
        (groupedNodePolynomial formula fallback copyOf labelOf variableGroup clauseGroup
          nodeValue start width order node).eval (z : ZMod p)

set_option maxHeartbeats 1000000 in
/-- Grouping changes the finite expression exactly, without a congruence or
an assumed D4 identity. Distinctness converts the indexed node loop into the
node-set loop used by scalar recovery. -/
theorem groupedScalarExpression_eq_scalarFormulaExpression (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (variableGroup : Node → Fin n → Fin r)
    (clauseGroup : Node → Fin formula.clauses.length → Fin r)
    (nodeValue : Node → ZMod p)
    (distinct_nodes : Function.Injective nodeValue) (nonzero_nodes : ∀ node, nodeValue node ≠ 0)
    (start : ℤ) (width order : ℕ)
    (variables_match : ∀ node inc,
      variableGroup node (IncidenceDeformation.incidenceVariable formula inc) = (labelOf inc node).1)
    (clauses_match : ∀ node inc, (labelOf inc node).2 = clauseGroup node inc.1) :
    groupedScalarExpression formula fallback copyOf labelOf variableGroup clauseGroup
        nodeValue start width order =
      FormulaCounter.scalarFormulaExpression formula
        (FiniteFieldCounter.coefficients formula copyOf labelOf nodeValue start width)
        (Finset.univ.image nodeValue) order := by
  unfold groupedScalarExpression FormulaCounter.scalarFormulaExpression AlgebraicCounter.scalarExpression
  rw [Finset.sum_image (fun _ _ _ _ h => distinct_nodes h)]
  apply congrArg (fun value : ZMod p =>
    (HermiteRecovery.nodeProduct (Finset.univ.image nodeValue) order).eval 0 * value)
  apply Finset.sum_congr rfl
  intro node _
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg (fun polynomial : Polynomial (ZMod p) =>
    (z : ZMod p) ^ (p - order) *
      (HermiteRecovery.nodeWeight (Finset.univ.image nodeValue) (nodeValue node) order).eval (z : ZMod p) *
      polynomial.eval (z : ZMod p))
    (groupedNodePolynomial_eq_taylorData formula fallback copyOf labelOf placement
      variableGroup clauseGroup nodeValue start width order node (nonzero_nodes node)
      (variables_match node) (clauses_match node))

set_option maxHeartbeats 1000000 in
/-- Functional correctness of the actual grouped scalar counter.

No spectral residual, origin, degree, D4, measurement-norm, Taylor-congruence,
or Hermite-recovery identity is assumed. These are all discharged by the
preceding checked constructions and their composition.
-/
theorem groupedScalarExpression_correct (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → Label Node r)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (variableGroup : Node → Fin n → Fin r)
    (clauseGroup : Node → Fin formula.clauses.length → Fin r)
    (nodeValue : Node → ZMod p)
    (distinct_nodes : Function.Injective nodeValue) (nonzero_nodes : ∀ node, nodeValue node ≠ 0)
    (start : ℤ) (width order : ℕ)
    (variables_match : ∀ node inc,
      variableGroup node (IncidenceDeformation.incidenceVariable formula inc) = (labelOf inc node).1)
    (clauses_match : ∀ node inc, (labelOf inc node).2 = clauseGroup node inc.1)
    (two_nonzero : (2 : ZMod p) ≠ 0) (small : width < p)
    (positive : 0 < order) (below_prime : order < p)
    (interpolation_capacity :
      FormulaCounter.incidenceCount formula * (width - 1) < Fintype.card Node * order)
    (no_alias : FormulaCounter.incidenceCount formula * (width - 1) ≤ p - 2) :
    groupedScalarExpression formula fallback copyOf labelOf variableGroup clauseGroup
        nodeValue start width order =
      (satisfyingCount formula : ZMod p) := by
  rw [groupedScalarExpression_eq_scalarFormulaExpression formula fallback copyOf labelOf placement
    variableGroup clauseGroup nodeValue distinct_nodes nonzero_nodes start width order
    variables_match clauses_match]
  exact FiniteFieldCounter.scalarFormulaExpression_correct_at_nodes formula copyOf labelOf placement
    two_nonzero nodeValue distinct_nodes nonzero_nodes start width small order positive below_prime
    interpolation_capacity no_alias

end

end NtimeDspace.GroupedCounter
