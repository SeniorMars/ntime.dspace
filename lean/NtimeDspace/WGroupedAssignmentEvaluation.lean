import NtimeDspace.WeightedSystem
import NtimeDspace.WSchedulePlacement
import NtimeDspace.LocalAssignmentLoop

/-!
Scalar scans for the grouped assignment loop. Variable contributions and clause
products are accumulated one index at a time. The executable layer receives
coefficient and incidence-value accessors; polynomial objects occur only in the
refinement theorems. Accessor implementations and tape-space costs remain
separate obligations.
-/

namespace NtimeDspace.WGroupedAssignmentEvaluation

open scoped BigOperators
open NtimeDspace.GroupedDeformation hiding LocalRepresentation clausePolynomial_eval_congr expandedPolynomial_formula_eval factorPolynomial_eq_product_groupFactor groupFactor groupedFormulaSum groupedTaylorData grouped_formula_identity localInputs support_subset_iff_assignment taylorCorrection taylorData_eq_groupedTaylorData taylor_inner_eq_groupedFormulaSum
open WGroupedDeformation

/-- A product loop retaining a scalar accumulator. -/
def productLoop {R : Type*} [Monoid R] (term : ℕ → R) : ℕ → R → R
  | 0, accumulator => accumulator
  | count + 1, accumulator => productLoop term count (term count * accumulator)

theorem productLoop_correct {R : Type*} [CommMonoid R]
    (term : ℕ → R) (count : ℕ) (accumulator : R) :
    productLoop term count accumulator =
      (∏ i ∈ Finset.range count, term i) * accumulator := by
  induction count generalizing accumulator with
  | zero => simp [productLoop]
  | succ count ih => simp [productLoop, ih, Finset.prod_range_succ, mul_assoc]

def scanSum {R : Type*} [AddMonoid R] {count : ℕ}
    (term : Fin count → R) (accumulator : R) : R :=
  sumLoop (fun i => if within : i < count then term ⟨i, within⟩ else 0)
    count accumulator

theorem scanSum_correct {R : Type*} [AddCommMonoid R] {count : ℕ}
    (term : Fin count → R) (accumulator : R) :
    scanSum term accumulator = (∑ i, term i) + accumulator := by
  rw [scanSum, sumLoop_correct, ← Finset.sum_fin_eq_sum_range]

def scanProduct {R : Type*} [Monoid R] {count : ℕ}
    (term : Fin count → R) (accumulator : R) : R :=
  productLoop (fun i => if within : i < count then term ⟨i, within⟩ else 1)
    count accumulator

theorem scanProduct_correct {R : Type*} [CommMonoid R] {count : ℕ}
    (term : Fin count → R) (accumulator : R) :
    scanProduct term accumulator = (∏ i, term i) * accumulator := by
  rw [scanProduct, productLoop_correct, ← Finset.prod_fin_eq_prod_range]

variable {n : ℕ} {Group : Type*} [DecidableEq Group]

/-- Recompute a variable's local rank when its contribution is requested. -/
def localSum {R : Type*} [AddMonoid R] (groupOf : Fin n → Group)
    (group : Group) (term : LocalVariable groupOf group → R) : R :=
  scanSum (fun v => if sameGroup : groupOf v = group then term ⟨v, sameGroup⟩ else 0) 0

theorem localSum_correct {R : Type*} [AddCommMonoid R]
    (groupOf : Fin n → Group) (group : Group)
    (term : LocalVariable groupOf group → R) :
    localSum groupOf group term = ∑ v, term v := by
  rw [localSum, scanSum_correct, add_zero, Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  exact (Equiv.subtypeEquivRight (by simp)).sum_comp term

def measurement (groupOf : Fin n → Group) (group : Group)
    (coefficient : LocalVariable groupOf group → ℤ) (mask : ℕ) : ℤ :=
  localSum groupOf group (fun v => coefficient v *
    CountingPolynomial.boolValue (LocalAssignmentLoop.assignment groupOf group mask v))

theorem measurement_correct (groupOf : Fin n → Group) (group : Group)
    (coefficient : LocalVariable groupOf group → ℤ) (mask : ℕ) :
    measurement groupOf group coefficient mask =
      integerMeasurement groupOf group coefficient
        (LocalAssignmentLoop.assignment groupOf group mask) :=
  localSum_correct _ _ _

theorem measurement_abs_le (groupOf : Fin n → Group) (group : Group)
    (coefficient : LocalVariable groupOf group → ℤ) (mask : ℕ) :
    |measurement groupOf group coefficient mask| ≤ ∑ v, |coefficient v| := by
  rw [measurement_correct]
  exact integerMeasurement_abs_le _ _ _ _

variable {K : Type*} [CommRing K]

/-- Evaluate a constraint's extension at incidence values: a sum over the
rows of its table of the weight times the product of the selectors. -/
def clauseValue (formula : WeightedSystem.System n)
    (value : WeightedSystem.Incidence formula → K)
    (clause : Fin formula.constraints.length) : K :=
  ∑ a : Fin (formula.constraints[clause]).scope.length → Bool,
    ((formula.constraints[clause]).weight a : K) *
      ∏ i, (if a i then value ⟨clause, i⟩ else 1 - value ⟨clause, i⟩)

theorem clauseValue_correct (formula : WeightedSystem.System n)
    (value : WeightedSystem.Incidence formula → K)
    (clause : Fin formula.constraints.length) :
    clauseValue formula value clause =
      (WeightedSystem.constraintPolynomial formula clause).eval₂ (RingHom.id K) value :=
  (WeightedSystem.constraintPolynomial_eval₂ formula clause value).symm

def groupValue (formula : WeightedSystem.System n)
    (clauseGroup : Fin formula.constraints.length → Group) (group : Group)
    (value : WeightedSystem.Incidence formula → K) : K :=
  scanProduct (fun clause =>
    if clauseGroup clause = group then clauseValue formula value clause else 1) 1

theorem groupValue_correct (formula : WeightedSystem.System n)
    (clauseGroup : Fin formula.constraints.length → Group) (group : Group)
    (value : WeightedSystem.Incidence formula → K) :
    groupValue formula clauseGroup group value =
      ∏ clause : {clause // clauseGroup clause = group},
        (WeightedSystem.constraintPolynomial formula clause.val).eval₂ (RingHom.id K) value := by
  simp only [groupValue, scanProduct_correct, mul_one, clauseValue_correct]
  simpa using (Fintype.prod_dite
    (fun clause (_ : clauseGroup clause = group) =>
      (WeightedSystem.constraintPolynomial formula clause).eval₂ (RingHom.id K) value)
    (fun _ _ => (1 : K)))

/-- Specialize scalar clause evaluation to the local polynomial inputs. The
algorithm takes their values; it does not construct these polynomials. -/
theorem groupValue_eq_groupFactor_eval
    {Row : Group → Type*} [Fintype Group] [∀ group, Fintype (Row group)]
    (formula : WeightedSystem.System n) (groupOf : Fin n → Group)
    (clauseGroup : Fin formula.constraints.length → Group) (bound : ℕ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → K)
    (measurementCoefficient : WeightedSystem.Incidence formula → ∀ group, Row group → K)
    (correction : WeightedSystem.Incidence formula → Polynomial K)
    (group : Group) (mask : ℕ) (measured : MeasurementTuple Row bound) (point : K) :
    groupValue formula clauseGroup group (fun inc =>
      localLinearValue groupOf bound localCoefficient measurementCoefficient group inc
        (LocalAssignmentLoop.assignment groupOf group mask) measured +
          (correction inc).eval point) =
      (groupFactor formula groupOf clauseGroup bound localCoefficient
        measurementCoefficient correction group
        (LocalAssignmentLoop.assignment groupOf group mask) measured).eval point := by
  rw [groupValue_correct]
  simp only [groupFactor, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro clause _
  rw [WeightedSystem.eval_eval₂_C]
  congr 1
  funext inc
  simp [localInputs]

end NtimeDspace.WGroupedAssignmentEvaluation
