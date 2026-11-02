import NtimeDspace.LocalAssignmentLoop

/-!
Scalar scans for the grouped assignment loop. Variable contributions and clause
products are accumulated one index at a time. The executable layer receives
coefficient and incidence-value accessors; polynomial objects occur only in the
refinement theorems. Accessor implementations and tape-space costs remain
separate obligations.
-/

namespace NtimeDspace.GroupedAssignmentEvaluation

open scoped BigOperators
open GroupedDeformation

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

/-- Evaluate a clause by scanning its literal occurrences, including the empty
clause and repeated literals. Incidence values are supplied on demand. -/
def clauseValue (formula : Formula n)
    (value : FormulaCounter.Incidence formula → K)
    (clause : Fin formula.clauses.length) : K :=
  1 - scanProduct (fun literal : Fin (formula.clauses[clause]).literals.length =>
    if (formula.clauses[clause].literals[literal]).positive then
      1 - value ⟨clause, literal⟩ else value ⟨clause, literal⟩) 1

theorem clauseValue_correct (formula : Formula n)
    (value : FormulaCounter.Incidence formula → K)
    (clause : Fin formula.clauses.length) :
    clauseValue formula value clause =
      (FormulaCounter.clausePolynomial formula clause).eval₂ (RingHom.id K) value := by
  simp only [clauseValue, scanProduct_correct, mul_one,
    FormulaCounter.clausePolynomial, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro literal _
  simp only [FormulaCounter.literalPolynomial]
  split_ifs <;> simp

def groupValue (formula : Formula n)
    (clauseGroup : Fin formula.clauses.length → Group) (group : Group)
    (value : FormulaCounter.Incidence formula → K) : K :=
  scanProduct (fun clause =>
    if clauseGroup clause = group then clauseValue formula value clause else 1) 1

theorem groupValue_correct (formula : Formula n)
    (clauseGroup : Fin formula.clauses.length → Group) (group : Group)
    (value : FormulaCounter.Incidence formula → K) :
    groupValue formula clauseGroup group value =
      ∏ clause : {clause // clauseGroup clause = group},
        (FormulaCounter.clausePolynomial formula clause.val).eval₂ (RingHom.id K) value := by
  simp only [groupValue, scanProduct_correct, mul_one, clauseValue_correct]
  simpa using (Fintype.prod_dite
    (fun clause (_ : clauseGroup clause = group) =>
      (FormulaCounter.clausePolynomial formula clause).eval₂ (RingHom.id K) value)
    (fun _ _ => (1 : K)))

/-- Specialize scalar clause evaluation to the local polynomial inputs. The
algorithm takes their values; it does not construct these polynomials. -/
theorem groupValue_eq_groupFactor_eval
    {Row : Group → Type*} [Fintype Group] [∀ group, Fintype (Row group)]
    (formula : Formula n) (groupOf : Fin n → Group)
    (clauseGroup : Fin formula.clauses.length → Group) (bound : ℕ)
    (localCoefficient : FormulaCounter.Incidence formula → Fin n → K)
    (measurementCoefficient : FormulaCounter.Incidence formula → ∀ group, Row group → K)
    (correction : FormulaCounter.Incidence formula → Polynomial K)
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
  simp only [FormulaCounter.clausePolynomial, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_prod, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro literal _
  simp only [FormulaCounter.literalPolynomial]
  split_ifs <;> simp [localInputs]

end NtimeDspace.GroupedAssignmentEvaluation
