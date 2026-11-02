import NtimeDspace.SpectralDeformation
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic

/-!
# The concrete parity interpolant

The integer window may start below zero. Its rational Lagrange interpolant
takes the prescribed parity value at every window node and has degree at most
`width - 1`. Good eigenindices are exactly those whose natural antisymmetric
count belongs to this integer window.

No denominator-prime bound or reduction-modulo-prime theorem is asserted here.
Instead, a second construction interpolates directly in `ZMod p` when the
window width is below `p`, with distinctness of all nodes proved explicitly.
-/

namespace NtimeDspace.ParityInterpolation

noncomputable section

open scoped BigOperators

def integerWindow (start : ℤ) (width : ℕ) : Finset ℤ :=
  Finset.Ico start (start + width)

theorem mem_integerWindow (start : ℤ) (width : ℕ) (j : ℤ) :
    j ∈ integerWindow start width ↔ start ≤ j ∧ j < start + width := by
  simp [integerWindow]

theorem integerWindow_card (start : ℤ) (width : ℕ) :
    (integerWindow start width).card = width := by
  simp [integerWindow]

theorem integerWindow_difference_lt (start : ℤ) (width : ℕ) (i j : ℤ)
    (hi : i ∈ integerWindow start width) (hj : j ∈ integerWindow start width) :
    (i - j).natAbs < width := by
  rw [mem_integerWindow] at hi hj
  omega

/-- Integer powers also specify parity at negative interpolation nodes. -/
def parityPolynomial (start : ℤ) (width : ℕ) : Polynomial ℚ :=
  Lagrange.interpolate (integerWindow start width) (fun j : ℤ => (j : ℚ))
    (fun j => (-1 : ℚ) ^ j)

theorem parityPolynomial_eval_int (start : ℤ) (width : ℕ) (j : ℤ)
    (included : j ∈ integerWindow start width) :
    (parityPolynomial start width).eval (j : ℚ) = (-1 : ℚ) ^ j := by
  exact Lagrange.eval_interpolate_at_node _ Int.cast_injective.injOn included

theorem parityPolynomial_eval_nat (start : ℤ) (width j : ℕ)
    (included : (j : ℤ) ∈ integerWindow start width) :
    (parityPolynomial start width).eval (j : ℚ) = (-1 : ℚ) ^ j := by
  simpa only [Int.cast_natCast, zpow_natCast] using
    parityPolynomial_eval_int start width j included

theorem parityPolynomial_degree (start : ℤ) (width : ℕ) :
    (parityPolynomial start width).natDegree ≤ width - 1 := by
  apply Polynomial.natDegree_le_of_degree_le
  simpa only [parityPolynomial, integerWindow_card] using
    (Lagrange.degree_interpolate_le (fun j : ℤ => (-1 : ℚ) ^ j)
      (s := integerWindow start width) (v := fun j : ℤ => (j : ℚ)) Int.cast_injective.injOn)

theorem parityPolynomial_degree_lt (start : ℤ) (width : ℕ) :
    (parityPolynomial start width).degree < width := by
  simpa only [parityPolynomial, integerWindow_card] using
    (Lagrange.degree_interpolate_lt (fun j : ℤ => (-1 : ℚ) ^ j)
      (s := integerWindow start width) (v := fun j : ℤ => (j : ℚ)) Int.cast_injective.injOn)

/-- The bad eigenindices are defined from counts and the actual integer window. -/
def badIndices {Index : Type*} [Fintype Index]
    (count : Index → ℕ) (start : ℤ) (width : ℕ) : Finset Index :=
  Finset.univ.filter (fun i => (count i : ℤ) ∉ integerWindow start width)

theorem not_mem_badIndices {Index : Type*} [Fintype Index]
    (count : Index → ℕ) (start : ℤ) (width : ℕ) (i : Index) :
    i ∉ badIndices count start width ↔ (count i : ℤ) ∈ integerWindow start width := by
  simp [badIndices]

theorem parityPolynomial_good {Index : Type*} [Fintype Index]
    (count : Index → ℕ) (start : ℤ) (width : ℕ) (i : Index)
    (good : i ∉ badIndices count start width) :
    (parityPolynomial start width).eval (count i : ℚ) = (-1 : ℚ) ^ count i :=
  parityPolynomial_eval_nat start width (count i)
    ((not_mem_badIndices count start width i).mp good)

/-- The spectral residual theorem with its interpolation premise discharged
by the concrete parity polynomial and the concrete set of bad indices. -/
theorem parity_filtered_residual {B Index : Type*} [Fintype B] [Fintype Index]
    [DecidableEq B] [DecidableEq Index]
    (basis : Module.Basis Index ℚ (B → ℚ))
    (orthogonal : ∀ i j, i ≠ j → dotProduct (basis i) (basis j) = 0)
    (norm_nonzero : ∀ i, dotProduct (basis i) (basis i) ≠ 0)
    (V W : Module.End ℚ (B → ℚ)) (count : Index → ℕ) (start : ℤ) (width : ℕ)
    (swap_eigen : ∀ i, V (basis i) = (-1 : ℚ) ^ count i • basis i)
    (count_eigen : ∀ i, W (basis i) = (count i : ℚ) • basis i) (u w : B) :
    (∑ i ∈ badIndices count start width,
      ((1 - (-1 : ℚ) ^ count i * (parityPolynomial start width).eval (count i : ℚ)) *
        basis i u / dotProduct (basis i) (basis i)) * basis i w) +
      SpectralDeformation.operatorEntry
        (SpectralDeformation.filteredOperator V W (parityPolynomial start width)) u w =
      if u = w then 1 else 0 := by
  exact SpectralDeformation.filtered_residual_add_entry basis orthogonal norm_nonzero V W
    (parityPolynomial start width) count swap_eigen count_eigen (badIndices count start width)
    (parityPolynomial_good count start width) u w

/-- Casting an integer window into residues loses no distinct nodes when its
width is smaller than the modulus. The window's starting point is unrestricted. -/
theorem integerWindow_cast_injective (modulus : ℕ) (start : ℤ) (width : ℕ)
    (small : width < modulus) :
    Set.InjOn (fun j : ℤ => (j : ZMod modulus)) (integerWindow start width) := by
  intro i hi j hj heq
  have hdiv : (modulus : ℤ) ∣ j - i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub i j modulus).mp heq
  have hlt : (j - i).natAbs < (modulus : ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using
      (integerWindow_difference_lt start width j i hj hi).trans small
  exact (sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hlt)).symm

section FiniteField

variable (p : ℕ) [Fact p.Prime]

/-- A direct finite-field parity interpolant; no map from all rationals is used. -/
def parityPolynomialMod (start : ℤ) (width : ℕ) : Polynomial (ZMod p) :=
  Lagrange.interpolate (integerWindow start width) (fun j : ℤ => (j : ZMod p))
    (fun j => (-1 : ZMod p) ^ j)

theorem parityPolynomialMod_eval_int (start : ℤ) (width : ℕ) (small : width < p) (j : ℤ)
    (included : j ∈ integerWindow start width) :
    (parityPolynomialMod p start width).eval (j : ZMod p) = (-1 : ZMod p) ^ j := by
  exact Lagrange.eval_interpolate_at_node _
    (integerWindow_cast_injective p start width small) included

theorem parityPolynomialMod_eval_nat (start : ℤ) (width : ℕ) (small : width < p) (j : ℕ)
    (included : (j : ℤ) ∈ integerWindow start width) :
    (parityPolynomialMod p start width).eval (j : ZMod p) = (-1 : ZMod p) ^ j := by
  simpa only [Int.cast_natCast, zpow_natCast] using
    parityPolynomialMod_eval_int p start width small j included

theorem parityPolynomialMod_degree (start : ℤ) (width : ℕ) (small : width < p) :
    (parityPolynomialMod p start width).natDegree ≤ width - 1 := by
  apply Polynomial.natDegree_le_of_degree_le
  simpa only [parityPolynomialMod, integerWindow_card] using
    (Lagrange.degree_interpolate_le (fun j : ℤ => (-1 : ZMod p) ^ j)
      (integerWindow_cast_injective p start width small))

theorem parityPolynomialMod_good {Index : Type*} [Fintype Index]
    (count : Index → ℕ) (start : ℤ) (width : ℕ) (small : width < p) (i : Index)
    (good : i ∉ badIndices count start width) :
    (parityPolynomialMod p start width).eval (count i : ZMod p) = (-1 : ZMod p) ^ count i :=
  parityPolynomialMod_eval_nat p start width small (count i)
    ((not_mem_badIndices count start width i).mp good)

/-- The residual identity also follows directly in the prime field from its
eigenbasis hypotheses and the explicitly constructed finite-field interpolant. -/
theorem parity_filtered_residual_mod {B Index : Type*} [Fintype B] [Fintype Index]
    [DecidableEq B] [DecidableEq Index]
    (basis : Module.Basis Index (ZMod p) (B → ZMod p))
    (orthogonal : ∀ i j, i ≠ j → dotProduct (basis i) (basis j) = 0)
    (norm_nonzero : ∀ i, dotProduct (basis i) (basis i) ≠ 0)
    (V W : Module.End (ZMod p) (B → ZMod p)) (count : Index → ℕ)
    (start : ℤ) (width : ℕ) (small : width < p)
    (swap_eigen : ∀ i, V (basis i) = (-1 : ZMod p) ^ count i • basis i)
    (count_eigen : ∀ i, W (basis i) = (count i : ZMod p) • basis i) (u w : B) :
    (∑ i ∈ badIndices count start width,
      ((1 - (-1 : ZMod p) ^ count i * (parityPolynomialMod p start width).eval (count i : ZMod p)) *
        basis i u / dotProduct (basis i) (basis i)) * basis i w) +
      SpectralDeformation.operatorEntry
        (SpectralDeformation.filteredOperator V W (parityPolynomialMod p start width)) u w =
      if u = w then 1 else 0 := by
  exact SpectralDeformation.filtered_residual_add_entry basis orthogonal norm_nonzero V W
    (parityPolynomialMod p start width) count swap_eigen count_eigen (badIndices count start width)
    (parityPolynomialMod_good p count start width small) u w

end FiniteField

end

end NtimeDspace.ParityInterpolation
