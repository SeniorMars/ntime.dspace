import NtimeDspace.SpectralDeformation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The concrete rational swap eigenbasis

Ordered pairs index the full one-pair basis, and tuples of ordered pairs index
its tensor basis. Orthogonality and nonzero norms prove linear independence;
the equal index/coordinate cardinality then proves completeness.
-/

namespace NtimeDspace.TensorBasis

noncomputable section

open scoped BigOperators
open SpectralDeformation

/-- Diagonal, symmetric, and antisymmetric one-pair basis vectors. -/
def pairVector {r : ℕ} (index : Fin r × Fin r) : (Fin r × Fin r) → ℚ :=
  if index.1 = index.2 then Pi.single index 1
  else if index.1 < index.2 then pairSymmetric index.1 index.2
  else pairAntisymmetric index.1 index.2

theorem pairVector_norm {r : ℕ} (index : Fin r × Fin r) :
    dotProduct (pairVector index) (pairVector index) =
      if index.1 = index.2 then 1 else 2 := by
  unfold pairVector
  split_ifs with heq hlt
  · simp
  · exact pairSymmetric_norm _ _ heq
  · exact pairAntisymmetric_norm _ _ heq

theorem pairVector_norm_ne_zero {r : ℕ} (index : Fin r × Fin r) :
    dotProduct (pairVector index) (pairVector index) ≠ 0 := by
  rw [pairVector_norm]
  split_ifs <;> norm_num

theorem pairVector_orthogonal {r : ℕ} (left right : Fin r × Fin r)
    (different : left ≠ right) :
    dotProduct (pairVector left) (pairVector right) = 0 := by
  rcases left with ⟨a, b⟩
  rcases right with ⟨c, d⟩
  simp only [pairVector]
  split_ifs with hab hablt hcd hcdlt <;>
    simp only [pairSymmetric, pairAntisymmetric, add_dotProduct, dotProduct_add,
      sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul,
      Pi.single_apply, Prod.mk.injEq]
  all_goals split_ifs <;> simp_all
  all_goals omega

/-- Every entry of the explicit one-pair basis is `0`, `1`, or `-1`. -/
theorem pairVector_entry {r : ℕ} (index p : Fin r × Fin r) :
    pairVector index p ∈ ({-1, 0, 1} : Finset ℚ) := by
  rcases index with ⟨a, b⟩
  rcases p with ⟨c, d⟩
  simp only [pairVector]
  split_ifs with heq hlt <;>
    simp only [pairSymmetric, pairAntisymmetric, Pi.add_apply, Pi.sub_apply,
      Pi.single_apply, Prod.mk.injEq]
  all_goals split_ifs <;> simp_all

theorem pairVector_abs_le_one {r : ℕ} (index p : Fin r × Fin r) :
    |pairVector index p| ≤ 1 := by
  have h := pairVector_entry index p
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h <;> rw [h] <;> norm_num

/-- Finite nonisotropic orthogonal families are linearly independent. -/
theorem linearIndependent_of_orthogonal {I B : Type*} [Fintype I] [Fintype B]
    (vectors : I → B → ℚ)
    (orthogonal : ∀ i j, i ≠ j → dotProduct (vectors i) (vectors j) = 0)
    (norm_nonzero : ∀ i, dotProduct (vectors i) (vectors i) ≠ 0) :
    LinearIndependent ℚ vectors := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients dependence i
  have h := congrArg (dotLinear (vectors i)) dependence
  rw [map_sum, map_zero] at h
  simp only [map_smul, dotLinear, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at h
  rw [Finset.sum_eq_single i] at h
  · exact (mul_eq_zero.mp h).resolve_right (norm_nonzero i)
  · intro j _ different
    rw [orthogonal i j different.symm, mul_zero]
  · simp

theorem pairVector_linearIndependent (r : ℕ) :
    LinearIndependent ℚ (@pairVector r) :=
  linearIndependent_of_orthogonal _ pairVector_orthogonal pairVector_norm_ne_zero

/-- The complete `r²`-element one-pair basis. -/
def pairBasis (r : ℕ) : Module.Basis (Fin r × Fin r) ℚ ((Fin r × Fin r) → ℚ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (pairVector_linearIndependent r)

@[simp] theorem pairBasis_apply {r : ℕ} (index : Fin r × Fin r) :
    pairBasis r index = pairVector index := by
  classical
  simp [pairBasis]

theorem pairVector_swap {r : ℕ} (index : Fin r × Fin r) (p : Fin r × Fin r) :
    pairVector index p.swap =
      (if index.2 < index.1 then (-1 : ℚ) else 1) * pairVector index p := by
  rcases index with ⟨a, b⟩
  by_cases heq : a = b
  · subst b
    have h := congrFun (pairSwap_diagonal (K := ℚ) a) p
    simpa [pairVector, pairSwap, Prod.swap] using h
  · by_cases hlt : a < b
    · have h := congrFun (pairSwap_symmetric (K := ℚ) a b) p
      simpa [pairVector, pairSwap, Prod.swap, heq, hlt, not_lt_of_ge (le_of_lt hlt)] using h
    · have hgt : b < a := by omega
      have h := congrFun (pairSwap_antisymmetric (K := ℚ) a b) p
      simpa [pairVector, pairSwap, Prod.swap, heq, hlt, hgt] using h

section Tensor

variable {Node : Type*} [Fintype Node] [DecidableEq Node]

abbrev Label (Node : Type*) (r : ℕ) := Node → Fin r × Fin r

/-- The actual tensor family whose existence was previously left open. -/
def tensorFamily {r : ℕ} (index : Label Node r) : Label Node r → ℚ :=
  tensorVector (fun t => pairVector (index t))

theorem tensorFamily_orthogonal {r : ℕ} (left right : Label Node r)
    (different : left ≠ right) :
    dotProduct (tensorFamily left) (tensorFamily right) = 0 := by
  have hcoordinate : ∃ t, left t ≠ right t := by
    by_contra! h
    exact different (funext h)
  obtain ⟨t, ht⟩ := hcoordinate
  exact tensorVector_orthogonal_of_factor _ _ t (pairVector_orthogonal _ _ ht)

theorem tensorFamily_norm_ne_zero {r : ℕ} (index : Label Node r) :
    dotProduct (tensorFamily index) (tensorFamily index) ≠ 0 := by
  rw [tensorFamily, tensorVector_dotProduct]
  exact Finset.prod_ne_zero_iff.mpr (fun t _ => pairVector_norm_ne_zero (index t))

theorem tensorFamily_linearIndependent (r : ℕ) :
    LinearIndependent ℚ (@tensorFamily Node _ r) :=
  linearIndependent_of_orthogonal _ tensorFamily_orthogonal tensorFamily_norm_ne_zero

/-- Completeness follows because both the family and coordinate space are
indexed by the same finite set `([r]×[r])^Node`. -/
def tensorBasis (Node : Type*) [Fintype Node] [DecidableEq Node] (r : ℕ) :
    Module.Basis (Label Node r) ℚ (Label Node r → ℚ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (tensorFamily_linearIndependent r)

@[simp] theorem tensorBasis_apply {r : ℕ} (index : Label Node r) :
    tensorBasis Node r index = tensorFamily index := by
  classical
  simp [tensorBasis]

def antisymmetricCoordinates {r : ℕ} (index : Label Node r) : Finset Node :=
  Finset.univ.filter (fun t => (index t).2 < (index t).1)

def antisymmetricCount {r : ℕ} (index : Label Node r) : ℕ :=
  (antisymmetricCoordinates index).card

theorem tensorFamily_local_eigen {r : ℕ} (index : Label Node r) (t : Node)
    (p : Fin r × Fin r) :
    pairVector (index t) p.swap =
      swapSign (antisymmetricCoordinates index) t * pairVector (index t) p := by
  simpa [swapSign, antisymmetricCoordinates] using pairVector_swap (index t) p

/-- The concrete complete tensor basis diagonalizes simultaneous swapping. -/
theorem tensorBasis_V_eigen {r : ℕ} (index : Label Node r) :
    simultaneousSwap (tensorBasis Node r index) =
      (-1 : ℚ) ^ antisymmetricCount index • tensorBasis Node r index := by
  simp only [tensorBasis_apply, tensorFamily, antisymmetricCount]
  exact simultaneousSwap_tensor_count _ _ (tensorFamily_local_eigen index)

/-- The concrete complete tensor basis diagonalizes `W`, with eigenvalue equal
to the number of antisymmetric tensor factors. -/
theorem tensorBasis_W_eigen {r : ℕ} (index : Label Node r) :
    antisymmetryOperator (tensorBasis Node r index) =
      (antisymmetricCount index : ℚ) • tensorBasis Node r index := by
  simp only [tensorBasis_apply, tensorFamily, antisymmetricCount]
  exact antisymmetryOperator_tensor_count (by norm_num) _ _ (tensorFamily_local_eigen index)

omit [DecidableEq Node] in
theorem tensorFamily_abs_le_one {r : ℕ} (index u : Label Node r) :
    |tensorFamily index u| ≤ 1 := by
  classical
  unfold tensorFamily tensorVector
  rw [Finset.abs_prod]
  have hprod (set : Finset Node) : (∏ t ∈ set, |pairVector (index t) (u t)|) ≤ 1 := by
    induction set using Finset.induction_on with
    | empty => simp
    | @insert t set ht ih =>
        rw [Finset.prod_insert ht]
        exact (mul_le_mul_of_nonneg_left ih (abs_nonneg _)).trans
          (by simpa using pairVector_abs_le_one (index t) (u t))
  exact hprod Finset.univ

/-- Tensor basis entries are integers of absolute value at most one, as used
in the measurement-size argument. -/
theorem tensorFamily_entry {r : ℕ} (index u : Label Node r) :
    tensorFamily index u ∈ ({-1, 0, 1} : Finset ℚ) := by
  have hprod (s : Finset Node) :
      (∏ t ∈ s, pairVector (index t) (u t)) ∈ ({-1, 0, 1} : Finset ℚ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert t s ht ih =>
        rw [Finset.prod_insert ht]
        have hentry := pairVector_entry (index t) (u t)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hentry ih ⊢
        rcases hentry with h | h | h <;> rw [h] <;>
          rcases ih with hi | hi | hi <;> rw [hi] <;> norm_num
  exact hprod Finset.univ

/-- The squared norm is a power of two: each non-diagonal pair contributes two. -/
theorem tensorFamily_norm {r : ℕ} (index : Label Node r) :
    dotProduct (tensorFamily index) (tensorFamily index) =
      (2 : ℚ) ^ (Finset.univ.filter (fun t => (index t).1 ≠ (index t).2)).card := by
  rw [tensorFamily, tensorVector_dotProduct]
  simp_rw [pairVector_norm]
  simp [Finset.prod_ite]

/-- The actual bad tensor indices for a finite interpolation set. -/
def badIndices {r : ℕ} (good : Finset ℕ) : Finset (Label Node r) :=
  Finset.univ.filter (fun index => antisymmetricCount index ∉ good)

/-- The paper's explicit residual measurement coefficient. -/
def beta {r : ℕ} (f : Polynomial ℚ) (u index : Label Node r) : ℚ :=
  (1 - (-1 : ℚ) ^ antisymmetricCount index * f.eval (antisymmetricCount index : ℚ)) *
    tensorFamily index u / dotProduct (tensorFamily index) (tensorFamily index)

/-- The full spectral residual identity for the concrete tensor basis and the
actual swap operators. Only interpolation of the supplied polynomial on the
specified good eigenvalues remains a premise. -/
theorem tensor_residual_add_entry {r : ℕ} (f : Polynomial ℚ) (good : Finset ℕ)
    (interpolates : ∀ j ∈ good, f.eval (j : ℚ) = (-1 : ℚ) ^ j)
    (u w : Label Node r) :
    (∑ index ∈ badIndices (Node := Node) (r := r) good, beta f u index * tensorFamily index w) +
      operatorEntry (filteredOperator simultaneousSwap antisymmetryOperator f) u w =
        if u = w then 1 else 0 := by
  have hgood (index : Label Node r) (h : index ∉ badIndices good) :
      f.eval (antisymmetricCount index : ℚ) = (-1 : ℚ) ^ antisymmetricCount index := by
    apply interpolates
    simpa [badIndices] using h
  have h := filtered_residual_add_entry (tensorBasis Node r)
    (by simpa only [tensorBasis_apply] using (@tensorFamily_orthogonal Node _ _ r))
    (by simpa only [tensorBasis_apply] using (@tensorFamily_norm_ne_zero Node _ _ r))
    simultaneousSwap antisymmetryOperator f antisymmetricCount
    tensorBasis_V_eigen tensorBasis_W_eigen (badIndices good) hgood u w
  simpa only [tensorBasis_apply, beta] using h

end Tensor

end

end NtimeDspace.TensorBasis
