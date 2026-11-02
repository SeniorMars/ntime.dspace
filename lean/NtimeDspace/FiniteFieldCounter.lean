import NtimeDspace.FiniteFieldDeformation
import NtimeDspace.IncidenceDeformation

/-!
# Concrete finite-field deformation and formula counting

The label polynomial is the actual tensor-spectral construction with the
finite-field parity interpolant. Occupied-position substitution then produces
the formula coefficients. Neither their origin identity nor their degree
bound is assumed in the final counting theorem.

The resulting scalar expression remains a finite algebraic specification.
An injective placement and the explicit interpolation capacity inequalities
are still required; no machine-space claim is made.
-/

namespace NtimeDspace.FiniteFieldCounter

noncomputable section

variable {n r p : ℕ} [Fact p.Prime]
variable {Node Copy : Type*} [Fintype Node] [DecidableEq Node] [DecidableEq Copy]

def coefficients (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → FiniteFieldDeformation.Label Node r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) :
    CountingPolynomial.Coefficients formula (ZMod p) :=
  IncidenceDeformation.formulaCoefficients formula copy label
    (FiniteFieldDeformation.coefficient nodeValue start width)

theorem coefficients_origin (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → FiniteFieldDeformation.Label Node r)
    (placement : Function.Injective (fun inc => (copy inc, label inc)))
    (two_nonzero : (2 : ZMod p) ≠ 0)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (small : width < p) :
    CountingPolynomial.OriginCondition formula (coefficients formula copy label nodeValue start width) :=
  IncidenceDeformation.formulaCoefficients_origin formula copy label
    (FiniteFieldDeformation.coefficient nodeValue start width) placement
    (FiniteFieldDeformation.coefficient_origin two_nonzero nodeValue start width small)

theorem coefficients_degree (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → FiniteFieldDeformation.Label Node r)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (small : width < p)
    (clause : Fin formula.clauses.length)
    (literal : Fin (formula.clauses[clause]).literals.length) (v : Fin n) :
    (coefficients formula copy label nodeValue start width clause literal v).natDegree ≤ width - 1 :=
  IncidenceDeformation.formulaCoefficients_degree formula copy label
    (FiniteFieldDeformation.coefficient nodeValue start width) (width - 1)
    (FiniteFieldDeformation.coefficient_degree nodeValue start width small) clause literal v

/-- Exact formula counting for the constructed spectral deformation. The
spectral residual, interpolation, matrix locality, origin, and degree claims
have all been proved upstream and are not premises of this theorem. -/
theorem scalarFormulaExpression_correct (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → FiniteFieldDeformation.Label Node r)
    (placement : Function.Injective (fun inc => (copy inc, label inc)))
    (two_nonzero : (2 : ZMod p) ≠ 0)
    (nodeValue : Node → ZMod p) (start : ℤ) (width : ℕ) (small : width < p)
    (nodes : Finset (ZMod p)) (order : ℕ)
    (positive : 0 < order) (below_prime : order < p)
    (nonzero_nodes : ∀ node ∈ nodes, node ≠ 0)
    (interpolation_capacity : FormulaCounter.incidenceCount formula * (width - 1) < nodes.card * order)
    (no_alias : FormulaCounter.incidenceCount formula * (width - 1) ≤ p - 2) :
    FormulaCounter.scalarFormulaExpression formula
        (coefficients formula copy label nodeValue start width) nodes order =
      (satisfyingCount formula : ZMod p) := by
  exact IncidenceDeformation.scalarFormulaExpression_correct formula copy label
    (FiniteFieldDeformation.coefficient nodeValue start width) placement
    (FiniteFieldDeformation.coefficient_origin two_nonzero nodeValue start width small)
    nodes order (width - 1) positive below_prime nonzero_nodes
    (FiniteFieldDeformation.coefficient_degree nodeValue start width small)
    interpolation_capacity no_alias

/-- Specialization to the actual deformation nodes. Their injectivity gives
the precise node count in the interpolation-capacity inequality. -/
theorem scalarFormulaExpression_correct_at_nodes (formula : Formula n)
    (copy : FormulaCounter.Incidence formula → Copy)
    (label : FormulaCounter.Incidence formula → FiniteFieldDeformation.Label Node r)
    (placement : Function.Injective (fun inc => (copy inc, label inc)))
    (two_nonzero : (2 : ZMod p) ≠ 0)
    (nodeValue : Node → ZMod p)
    (distinct_nodes : Function.Injective nodeValue) (nonzero_nodes : ∀ node, nodeValue node ≠ 0)
    (start : ℤ) (width : ℕ) (small : width < p) (order : ℕ)
    (positive : 0 < order) (below_prime : order < p)
    (interpolation_capacity :
      FormulaCounter.incidenceCount formula * (width - 1) < Fintype.card Node * order)
    (no_alias : FormulaCounter.incidenceCount formula * (width - 1) ≤ p - 2) :
    FormulaCounter.scalarFormulaExpression formula
        (coefficients formula copy label nodeValue start width) (Finset.univ.image nodeValue) order =
      (satisfyingCount formula : ZMod p) := by
  apply scalarFormulaExpression_correct formula copy label placement two_nonzero nodeValue start width
    small (Finset.univ.image nodeValue) order positive below_prime
  · intro value included
    obtain ⟨node, _, rfl⟩ := Finset.mem_image.mp included
    exact nonzero_nodes node
  · simpa only [Finset.card_image_of_injective _ distinct_nodes, Finset.card_univ] using
      interpolation_capacity
  · exact no_alias

end

end NtimeDspace.FiniteFieldCounter
