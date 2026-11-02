import NtimeDspace.CompressedRecoveryLoop
import NtimeDspace.GroupedAccessorEvaluation

/-!
# Concrete arithmetic modular counting

`countModP` composes explicit scalar loops for support codes, subset masks,
measurements, groups, local assignments, field residues, and Hermite recovery.
Its tensor, parity, deformation, incidence, and grouped coefficient accessors
are concrete arithmetic procedures. No polynomial-evaluation callback or
accessor-correctness hypothesis remains in the final counting theorem.

The formula and copy/label/group/node maps are supplied inputs. Their uniform
construction, input access implementation, and simultaneous machine time and
work-space bounds remain separate. The fallback variable is proof-side only;
the executing counter does not use a chosen placement inverse or occupied set.
-/

namespace NtimeDspace.ConcreteCountingLoop

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime] {n r Q copies : ℕ}

/-- Scalar modular counter with concrete indexed rows and coefficient access.
The actual support length, rather than its capacity, controls subset masks. -/
def countModP (positive : 0 < r) (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Fin copies)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (variableGroup : Fin Q → Fin n → Fin r)
    (clauseGroup : Fin Q → Fin formula.clauses.length → Fin r)
    (nodeValue : Fin Q → ZMod p) (k : ℕ) (start : ℤ) (width : ℕ) : ZMod p :=
  CompressedRecoveryLoop.evaluate formula variableGroup clauseGroup
    (fun _node => SpectralIndexing.rowAt r Q positive copies start width)
    (fun _node => SpectralIndexing.measurementRowNumber r Q positive copies start width)
    (r ^ (2 * Q)) k nodeValue
    (fun node => GroupedAccessorEvaluation.measurement formula copyOf labelOf
      (variableGroup node) start width)
    (fun node => GroupedAccessorEvaluation.localCoefficient p positive formula copyOf labelOf
      nodeValue start width node)
    (fun _node => GroupedAccessorEvaluation.measurementCoefficient p formula copyOf labelOf start width)
    (IncidenceEvaluation.finiteField p positive formula copyOf labelOf nodeValue start width)

set_option maxHeartbeats 1500000 in
/-- All scalar accessor contracts and row bijections are discharged here.
The result is the concrete grouped expression, not an assumed counter value. -/
theorem countModP_eq_groupedScalarExpression
    (positive : 0 < r) (two_nonzero : (2 : ZMod p) ≠ 0)
    (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Fin copies)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (variableGroup : Fin Q → Fin n → Fin r)
    (clauseGroup : Fin Q → Fin formula.clauses.length → Fin r)
    (nodeValue : Fin Q → ZMod p)
    (distinct : Function.Injective nodeValue) (nonzero : ∀ node, nodeValue node ≠ 0)
    (k : ℕ) (large : 6 ≤ k) (start : ℤ) (width : ℕ) (small : width < p)
    (within : Parameters.q n k + 1 ≤ p) :
    countModP p positive formula copyOf labelOf variableGroup clauseGroup nodeValue k start width =
      GroupedCounter.groupedScalarExpression formula fallback copyOf labelOf variableGroup
        clauseGroup nodeValue start width (Parameters.q n k + 1) := by
  unfold countModP
  refine CompressedRecoveryLoop.evaluate_eq_groupedScalarExpression formula fallback copyOf labelOf
    variableGroup clauseGroup _ (fun _node => ?_) _ (fun _node => ?_) k large
    nodeValue distinct nonzero within _ ?_ _ ?_ _ ?_ _ ?_
  · exact (SpectralIndexing.rowEquiv r Q positive copies start width).symm.bijective
  · exact SpectralIndexing.measurementRowNumber_bijective r Q positive copies start width
  · intro node group row v
    exact GroupedAccessorEvaluation.measurement_correct formula fallback copyOf labelOf placement
      (variableGroup node) start width group row v
  · intro node inc v
    exact GroupedAccessorEvaluation.localCoefficient_correct p positive two_nonzero formula fallback
      copyOf labelOf placement nodeValue start width small node inc v
  · intro _node inc group row
    exact GroupedAccessorEvaluation.measurementCoefficient_correct p formula copyOf labelOf
      start width inc group row
  · intro inc v point
    exact IncidenceEvaluation.finiteField_correct p positive two_nonzero formula copyOf labelOf
      nodeValue start width small inc v point

set_option maxHeartbeats 1500000 in
/-- Functional modular-counting correctness for the actual scalar procedure.
No residual, interpolation, Taylor, counting, or accessor identity is assumed.
Placement and schedule compatibility, and the explicit scalar parameter
inequalities, describe the supplied input maps and remain visible premises. -/
theorem countModP_correct
    (positive : 0 < r) (two_nonzero : (2 : ZMod p) ≠ 0)
    (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Fin copies)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (variableGroup : Fin Q → Fin n → Fin r)
    (clauseGroup : Fin Q → Fin formula.clauses.length → Fin r)
    (nodeValue : Fin Q → ZMod p)
    (distinct : Function.Injective nodeValue) (nonzero : ∀ node, nodeValue node ≠ 0)
    (k : ℕ) (large : 6 ≤ k) (start : ℤ) (width : ℕ) (small : width < p)
    (below_prime : Parameters.q n k + 1 < p)
    (variables_match : ∀ node inc,
      variableGroup node (IncidenceEvaluation.variableOf formula inc) = (labelOf inc node).1)
    (clauses_match : ∀ node inc, (labelOf inc node).2 = clauseGroup node inc.1)
    (interpolation_capacity :
      FormulaCounter.incidenceCount formula * (width - 1) < Q * (Parameters.q n k + 1))
    (no_alias : FormulaCounter.incidenceCount formula * (width - 1) ≤ p - 2) :
    countModP p positive formula copyOf labelOf variableGroup clauseGroup nodeValue k start width =
      (satisfyingCount formula : ZMod p) := by
  rw [countModP_eq_groupedScalarExpression p positive two_nonzero formula fallback copyOf labelOf
    placement variableGroup clauseGroup nodeValue distinct nonzero k large start width small
    below_prime.le]
  apply GroupedCounter.groupedScalarExpression_correct formula fallback copyOf labelOf placement
    variableGroup clauseGroup nodeValue distinct nonzero start width (Parameters.q n k + 1)
    variables_match clauses_match two_nonzero small (Nat.succ_pos _) below_prime
  · simpa only [Fintype.card_fin] using interpolation_capacity
  · exact no_alias

end NtimeDspace.ConcreteCountingLoop
