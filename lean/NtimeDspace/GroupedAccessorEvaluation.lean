import NtimeDspace.IncidenceEvaluation

/-!
Executable scalar accessors for the three remaining grouped-counting inputs.
Integer tensor signs are products of explicit pair signs. Measurement rows
and local coefficients scan the formula's original clause/literal positions,
retaining every repeated incidence. Measurement coefficients use a copy test
and the scalar spectral residual coefficient.

Occupied-position sets and the chosen stored-variable inverse occur only in
the correctness statements. Injective placement proves that the incidence
scans agree with those specifications. Runtime uses the supplied copy, label,
group, and node accessors, with no occupied set or inverse table. Their costs
and the arithmetic procedures' work-tape implementations remain separate.
-/

namespace NtimeDspace.GroupedAccessorEvaluation

open scoped BigOperators
open GroupedAssignmentEvaluation GroupedDeformation

variable {n r Q : ℕ} {Copy : Type*} [DecidableEq Copy]

/-- Integer basis entry, preserving the antisymmetric orientation. -/
def integerPairSign (index position : Fin r × Fin r) : ℤ :=
  if index.1 = index.2 then (if position = index then 1 else 0)
  else if index.1 < index.2 then
    (if position = index then 1 else 0) + (if position = index.swap then 1 else 0)
  else (if position = index then 1 else 0) - (if position = index.swap then 1 else 0)

theorem integerPairSign_correct (index position : Fin r × Fin r) :
    integerPairSign index position = RestrictedMeasurements.pairSign index position := by
  simp only [integerPairSign, RestrictedMeasurements.pairSign]
  by_cases diagonal : index.1 = index.2
  · simp [diagonal, Pi.single_apply, eq_comm]
  · by_cases ordered : index.1 < index.2
    · simp [diagonal, ordered, Pi.single_apply, eq_comm]
    · simp [diagonal, ordered, Pi.single_apply, eq_comm]

/-- One scalar product over node coordinates, rather than a tensor vector. -/
def integerTensorSign (index position : TensorEvaluation.Label r Q) : ℤ :=
  scanProduct (fun node => integerPairSign (index node) (position node)) 1

theorem integerTensorSign_correct (index position : TensorEvaluation.Label r Q) :
    integerTensorSign index position = RestrictedMeasurements.tensorSign index position := by
  simp only [integerTensorSign, scanProduct_correct, mul_one, integerPairSign_correct,
    RestrictedMeasurements.tensorSign]

theorem integerTensorSign_abs_le (index position : TensorEvaluation.Label r Q) :
    |integerTensorSign index position| ≤ 1 := by
  rw [integerTensorSign_correct]
  exact RestrictedMeasurements.tensorSign_abs_le index position

/-- Filter a scalar incidence scan by copy and declared variable. -/
def variableSum {A : Type*} [AddMonoid A] (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (copy : Copy) (targetVariable : Fin n) (weight : TensorEvaluation.Label r Q → A) : A :=
  IncidenceEvaluation.scanIncidences formula (fun inc =>
    if copyOf inc = copy ∧ IncidenceEvaluation.variableOf formula inc = targetVariable then
      weight (labelOf inc) else 0) 0

/-- Injective placement reindexes the scalar incidence scan as the occupied
positions carrying the requested variable. No inverse is executed by the scan. -/
theorem variableSum_eq_occupied {A : Type*} [AddCommMonoid A]
    (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (copy : Copy) (targetVariable : Fin n) (weight : TensorEvaluation.Label r Q → A) :
    variableSum formula copyOf labelOf copy targetVariable weight =
      ∑ position ∈ (ConcreteGroupedDeformation.occupiedPositions copyOf labelOf copy).filter
        (fun position => ConcreteGroupedDeformation.storedVariable fallback
          (IncidenceDeformation.incidenceVariable formula) copyOf labelOf copy position = targetVariable),
        weight position := by
  classical
  have occupied := ConcreteGroupedDeformation.incidence_sum_eq_occupied
    copyOf labelOf (IncidenceDeformation.incidenceVariable formula) placement
    (ConcreteGroupedDeformation.occupiedPositions copyOf labelOf) (fun _ => rfl)
    (ConcreteGroupedDeformation.storedVariable fallback
      (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
    (ConcreteGroupedDeformation.storedVariable_at fallback
      (IncidenceDeformation.incidenceVariable formula) copyOf labelOf placement)
    copy (fun position carried => if carried = targetVariable then weight position else 0)
  rw [variableSum, IncidenceEvaluation.scanIncidences_correct, add_zero, Finset.sum_filter]
  calc
    _ = ∑ inc : FormulaCounter.Incidence formula,
        if copyOf inc = copy then
          (if IncidenceDeformation.incidenceVariable formula inc = targetVariable then weight (labelOf inc)
            else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro inc _
      rw [IncidenceEvaluation.variableOf_eq]
      by_cases sameCopy : copyOf inc = copy <;> simp [sameCopy]
    _ = _ := occupied

/-- An integer measurement row sums the signs of all matching incidences.
Its group restriction is supplied by the variable's fiber type. -/
def measurement (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (groupOf : Fin n → Fin r) (start : ℤ) (width : ℕ) (group : Fin r)
    (row : ConcreteGroupedDeformation.Row (Fin Q) Copy r start width)
    (v : LocalVariable groupOf group) : ℤ :=
  variableSum formula copyOf labelOf row.1 v.val (integerTensorSign row.2.val)

theorem measurement_correct (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (groupOf : Fin n → Fin r) (start : ℤ) (width : ℕ) (group : Fin r)
    (row : ConcreteGroupedDeformation.Row (Fin Q) Copy r start width)
    (v : LocalVariable groupOf group) :
    measurement formula copyOf labelOf groupOf start width group row v =
      ConcreteGroupedDeformation.measurementRow
        (ConcreteGroupedDeformation.occupiedPositions copyOf labelOf)
        (ConcreteGroupedDeformation.storedVariable fallback
          (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
        groupOf start width group row v := by
  rw [measurement, variableSum_eq_occupied formula fallback copyOf labelOf placement]
  unfold ConcreteGroupedDeformation.measurementRow RestrictedMeasurements.coefficient
  refine Finset.sum_congr ?_ ?_
  · ext position
    simp
  · intro position _
    exact integerTensorSign_correct row.2.val position

section FiniteField

variable (p : ℕ) [Fact p.Prime]

/-- Evaluate the local term by an incidence scan of scalar matrix-entry and
mismatch-product values at the selected interpolation node. -/
def localCoefficient (positive : 0 < r) (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (nodeValue : Fin Q → ZMod p) (start : ℤ) (width : ℕ) (node : Fin Q)
    (inc : FormulaCounter.Incidence formula) (v : Fin n) : ZMod p :=
  variableSum formula copyOf labelOf (copyOf inc) v (fun position =>
    DeformationEvaluation.entry p positive start width (labelOf inc) position *
      TensorEvaluation.mismatchProduct nodeValue (labelOf inc) position (nodeValue node))

theorem localCoefficient_correct (positive : 0 < r) (two_nonzero : (2 : ZMod p) ≠ 0)
    (formula : Formula n) (fallback : Fin n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (placement : Function.Injective (fun inc => (copyOf inc, labelOf inc)))
    (nodeValue : Fin Q → ZMod p) (start : ℤ) (width : ℕ) (small : width < p)
    (node : Fin Q) (inc : FormulaCounter.Incidence formula) (v : Fin n) :
    localCoefficient p positive formula copyOf labelOf nodeValue start width node inc v =
      ConcreteGroupedDeformation.formulaLocalCoefficient formula copyOf labelOf
        (ConcreteGroupedDeformation.occupiedPositions copyOf labelOf)
        (ConcreteGroupedDeformation.storedVariable fallback
          (IncidenceDeformation.incidenceVariable formula) copyOf labelOf)
        nodeValue start width node inc v := by
  rw [localCoefficient, variableSum_eq_occupied formula fallback copyOf labelOf placement]
  unfold ConcreteGroupedDeformation.formulaLocalCoefficient ConcreteGroupedDeformation.localCoefficient
  refine Finset.sum_congr ?_ ?_
  · ext position
    simp
  · intro position _
    rw [DeformationEvaluation.entry_correct p positive two_nonzero start width small,
      TensorEvaluation.mismatchProduct_correct]
    rfl

/-- Only rows in the incidence's copy have a nonzero measurement coefficient.
The residual coefficient itself is the explicit scalar spectral evaluation. -/
def measurementCoefficient (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (start : ℤ) (width : ℕ) (inc : FormulaCounter.Incidence formula) (_group : Fin r)
    (row : ConcreteGroupedDeformation.Row (Fin Q) Copy r start width) : ZMod p :=
  if row.1 = copyOf inc then DeformationEvaluation.beta p start width (labelOf inc) row.2.val else 0

theorem measurementCoefficient_correct (formula : Formula n)
    (copyOf : FormulaCounter.Incidence formula → Copy)
    (labelOf : FormulaCounter.Incidence formula → TensorEvaluation.Label r Q)
    (start : ℤ) (width : ℕ) (inc : FormulaCounter.Incidence formula) (group : Fin r)
    (row : ConcreteGroupedDeformation.Row (Fin Q) Copy r start width) :
    measurementCoefficient p formula copyOf labelOf start width inc group row =
      ConcreteGroupedDeformation.formulaMeasurementCoefficient formula copyOf labelOf
        start width inc group row := by
  simp only [measurementCoefficient, ConcreteGroupedDeformation.formulaMeasurementCoefficient,
    ConcreteGroupedDeformation.measurementCoefficient, DeformationEvaluation.beta_correct]

end FiniteField

end NtimeDspace.GroupedAccessorEvaluation
