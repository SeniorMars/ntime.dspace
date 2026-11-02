import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# A counting form of Hoeffding's inequality on finite product spaces

This module derives the two-sided tail bound from Mathlib's proved
sub-Gaussian theorem and converts uniform probability to cardinality.
-/

namespace NtimeDspace.FiniteProductTail

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Normalized counting measure, written directly so that the construction
does not depend on the changing uniform-PMF API. -/
def uniformMeasure (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] : Measure A :=
  (Fintype.card A : ℝ≥0∞)⁻¹ • Measure.count

instance uniformMeasure_probability : IsProbabilityMeasure (uniformMeasure A) := by
  constructor
  rw [uniformMeasure, Measure.smul_apply, smul_eq_mul, ← Finset.coe_univ,
    Measure.count_apply_finset, Finset.card_univ]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)

def average (X : A → ℝ) : ℝ := (∑ a, X a) / Fintype.card A

theorem integral_uniform (X : A → ℝ) : ∫ a, X a ∂uniformMeasure A = average X := by
  rw [uniformMeasure, integral_smul_measure, integral_count]
  simp [average, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem uniformMeasure_singleton (a : A) :
    uniformMeasure A {a} = (Fintype.card A : ℝ≥0∞)⁻¹ := by
  simp [uniformMeasure]

theorem product_uniform_eq :
    Measure.pi (fun _ : I => uniformMeasure A) = uniformMeasure (I → A) := by
  classical
  apply Measure.ext_of_singleton
  intro ω
  rw [← Set.univ_pi_singleton ω, Measure.pi_pi]
  simp only [uniformMeasure_singleton, Finset.prod_const, Finset.card_univ]
  rw [Set.univ_pi_singleton, uniformMeasure_singleton]
  simp [ENNReal.inv_pow]

theorem uniformMeasure_real_finset (s : Finset A) :
    (uniformMeasure A).real s = (s.card : ℝ) / Fintype.card A := by
  simp [measureReal_def, uniformMeasure, div_eq_mul_inv, mul_comm]

theorem centered_subgaussian (X : A → ℝ) (bounded : ∀ a, X a ∈ Set.Icc 0 1) :
    HasSubgaussianMGF (fun a => X a - average X) (1 / 4) (uniformMeasure A) := by
  have h := hasSubgaussianMGF_of_mem_Icc (X := X) (μ := uniformMeasure A)
    (measurable_of_countable X).aemeasurable (ae_of_all _ bounded)
  norm_num [integral_uniform] at h ⊢
  exact h

/-- The sum of independent centered coordinates has variance proxy `Q/4`. -/
theorem product_centered_subgaussian (X : A → ℝ) (bounded : ∀ a, X a ∈ Set.Icc 0 1) :
    HasSubgaussianMGF
      (fun ω : I → A => ∑ i, (X (ω i) - average X))
      (∑ _ : I, (1 / 4 : ℝ≥0)) (uniformMeasure (I → A)) := by
  rw [← product_uniform_eq]
  apply HasSubgaussianMGF.sum_of_iIndepFun
  · exact iIndepFun_pi (fun _ => (measurable_of_countable (fun a => X a - average X)).aemeasurable)
  · intro i _
    have h := centered_subgaussian X bounded
    have hm := (measurePreserving_eval (fun _ : I => uniformMeasure A) i).map_eq
    rw [← hm] at h
    exact HasSubgaussianMGF.of_map
      (μ := Measure.pi (fun _ : I => uniformMeasure A))
      (Y := fun ω : I → A => ω i) (X := fun a => X a - average X)
      (measurable_pi_apply i).aemeasurable h

/-- A fully proved two-sided concentration inequality on the uniform finite
product, before conversion to cardinality. -/
theorem product_tail_measure_le (X : A → ℝ) (bounded : ∀ a, X a ∈ Set.Icc 0 1)
    (ε : ℝ) (nonnegative : 0 ≤ ε) :
    (uniformMeasure (I → A)).real
      {ω | ε ≤ |(∑ i, X (ω i)) - Fintype.card I * average X|} ≤
      2 * Real.exp (-2 * ε ^ 2 / Fintype.card I) := by
  classical
  let Z : (I → A) → ℝ := fun ω => ∑ i, (X (ω i) - average X)
  have hZ := product_centered_subgaussian (I := I) X bounded
  have upper := hZ.measure_ge_le nonnegative
  have lower := hZ.neg.measure_ge_le nonnegative
  have event : {ω | ε ≤ |(∑ i, X (ω i)) - Fintype.card I * average X|} =
      {ω | ε ≤ Z ω} ∪ {ω | ε ≤ -Z ω} := by
    ext ω
    change (ε ≤ |(∑ i, X (ω i)) - Fintype.card I * average X|) ↔
      (ε ≤ Z ω ∨ ε ≤ -Z ω)
    simp only [Z, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact le_abs
  rw [event]
  have h := (measureReal_union_le (μ := uniformMeasure (I → A))
    {ω | ε ≤ Z ω} {ω | ε ≤ -Z ω}).trans (add_le_add upper lower)
  convert h using 1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  ring_nf

/-- Cardinality form: the number of exceptional tuples is at most the
two-sided Hoeffding probability times the exact size of the product. -/
theorem product_tail_card_le (X : A → ℝ) (bounded : ∀ a, X a ∈ Set.Icc 0 1)
    (ε : ℝ) (nonnegative : 0 ≤ ε) :
    ((Finset.univ.filter (fun ω : I → A =>
      ε ≤ |(∑ i, X (ω i)) - Fintype.card I * average X|)).card : ℝ) ≤
      2 * (Fintype.card A : ℝ) ^ Fintype.card I *
        Real.exp (-2 * ε ^ 2 / Fintype.card I) := by
  classical
  have h := product_tail_measure_le (I := I) X bounded ε nonnegative
  have hs : {ω : I → A | ε ≤ |(∑ i, X (ω i)) - Fintype.card I * average X|} =
      (Finset.univ.filter (fun ω : I → A =>
        ε ≤ |(∑ i, X (ω i)) - Fintype.card I * average X|) : Set (I → A)) := by
    ext ω
    simp
  rw [hs, uniformMeasure_real_finset] at h
  have hp : (0 : ℝ) < Fintype.card (I → A) := by exact_mod_cast Fintype.card_pos
  have h' := (div_le_iff₀ hp).mp h
  simpa [Fintype.card_fun, mul_comm, mul_left_comm, mul_assoc] using h'

end

end NtimeDspace.FiniteProductTail
