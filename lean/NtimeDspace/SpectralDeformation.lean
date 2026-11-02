import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Spectral residuals for the deformation

The residual identity is derived from an orthogonal eigenbasis and from
polynomial action on eigenvectors. The orthogonal tensor basis and its full
construction are separate from this general spectral calculation.
-/

namespace NtimeDspace.SpectralDeformation

open scoped BigOperators

noncomputable section

variable {K B I : Type*} [Field K] [Fintype B] [Fintype I]

def dotLinear (v : B → K) : (B → K) →ₗ[K] K where
  toFun := dotProduct v
  map_add' := dotProduct_add v
  map_smul' c w := dotProduct_smul c v w

/-- The coordinate functional of an orthogonal basis, including the norm
denominator rather than silently treating the basis as orthonormal. -/
theorem orthogonal_repr (basis : Module.Basis I K (B → K))
    (orthogonal : ∀ i j, i ≠ j → dotProduct (basis i) (basis j) = 0)
    (norm_nonzero : ∀ i, dotProduct (basis i) (basis i) ≠ 0)
    (x : B → K) (i : I) :
    basis.repr x i = dotProduct (basis i) x / dotProduct (basis i) (basis i) := by
  classical
  have h := congrArg (dotLinear (basis i)) (basis.sum_repr x)
  rw [map_sum] at h
  simp only [map_smul, dotLinear, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at h
  rw [Finset.sum_eq_single i] at h
  · exact (eq_div_iff (norm_nonzero i)).mpr h
  · intro j _ different
    rw [orthogonal i j different.symm, mul_zero]
  · simp

/-- On a rational orthogonal basis the squared norm cannot vanish. -/
theorem rational_basis_norm_nonzero {B I : Type*} [Fintype B]
    (basis : Module.Basis I ℚ (B → ℚ)) (i : I) :
    dotProduct (basis i) (basis i) ≠ 0 := by
  rw [ne_eq, dotProduct_self_eq_zero]
  exact basis.ne_zero i

/-- Matrix entry of a linear operator in the standard coordinate basis. -/
def operatorEntry [DecidableEq B] (A : Module.End K (B → K)) (u w : B) : K :=
  A (Pi.single w 1) u

def residualWeight (basis : Module.Basis I K (B → K)) (eigenvalue : I → K) (u : B) (i : I) : K :=
  (1 - eigenvalue i) * basis i u / dotProduct (basis i) (basis i)

omit [Fintype B] in
/-- An eigenbasis determines every value of a linear operator. -/
theorem operator_eigen_expansion (basis : Module.Basis I K (B → K))
    (A : Module.End K (B → K)) (eigenvalue : I → K)
    (eigenvectors : ∀ i, A (basis i) = eigenvalue i • basis i) (x : B → K) :
    A x = ∑ i, (basis.repr x i * eigenvalue i) • basis i := by
  conv_lhs => rw [← basis.sum_repr x]
  simp only [map_sum, map_smul, eigenvectors, smul_smul]

/-- The complete entrywise residual formula. Only the local eigenvector
relations and basis orthogonality are assumed; no residual identity is assumed. -/
theorem residual_entry [DecidableEq B] (basis : Module.Basis I K (B → K))
    (orthogonal : ∀ i j, i ≠ j → dotProduct (basis i) (basis j) = 0)
    (norm_nonzero : ∀ i, dotProduct (basis i) (basis i) ≠ 0)
    (A : Module.End K (B → K)) (eigenvalue : I → K)
    (eigenvectors : ∀ i, A (basis i) = eigenvalue i • basis i) (u w : B) :
    (if u = w then 1 else 0) - operatorEntry A u w =
      ∑ i, residualWeight basis eigenvalue u i * basis i w := by
  classical
  have hx := congrFun (basis.sum_repr (Pi.single w (1 : K))) u
  have hA := congrFun (operator_eigen_expansion basis A eigenvalue eigenvectors
    (Pi.single w 1)) u
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx hA
  have hsingle : (Pi.single w (1 : K) : B → K) u = if u = w then 1 else 0 := by
    by_cases h : u = w <;> simp [h, Pi.single_apply]
  rw [hsingle] at hx
  rw [← hx, operatorEntry, hA, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [orthogonal_repr basis orthogonal norm_nonzero,
    dotProduct_single, mul_one, residualWeight]
  ring

/-- Good eigenvectors have eigenvalue one and therefore disappear from the
residual sum. This is the restriction to the manuscript's bad measurements. -/
theorem residual_entry_bad [DecidableEq B] [DecidableEq I]
    (basis : Module.Basis I K (B → K))
    (orthogonal : ∀ i j, i ≠ j → dotProduct (basis i) (basis j) = 0)
    (norm_nonzero : ∀ i, dotProduct (basis i) (basis i) ≠ 0)
    (A : Module.End K (B → K)) (eigenvalue : I → K)
    (eigenvectors : ∀ i, A (basis i) = eigenvalue i • basis i)
    (bad : Finset I) (good_fixed : ∀ i, i ∉ bad → eigenvalue i = 1) (u w : B) :
    (if u = w then 1 else 0) - operatorEntry A u w =
      ∑ i ∈ bad, residualWeight basis eigenvalue u i * basis i w := by
  rw [residual_entry basis orthogonal norm_nonzero A eigenvalue eigenvectors]
  symm
  apply Finset.sum_subset (Finset.subset_univ bad)
  intro i _ good
  simp [residualWeight, good_fixed i good]

/-- Polynomial action on an operator, written as a finite sum of its powers. -/
def polynomialOperator (f : Polynomial K) (W : Module.End K (B → K)) :
    Module.End K (B → K) :=
  ∑ n ∈ f.support, f.coeff n • W ^ n

omit [Fintype B] in
theorem operator_power_eigen (W : Module.End K (B → K)) (v : B → K) (c : K)
    (eigenvector : W v = c • v) (n : ℕ) : (W ^ n) v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, eigenvector,
        smul_smul, pow_succ', mul_comm]

omit [Fintype B] in
theorem polynomialOperator_eigen (f : Polynomial K) (W : Module.End K (B → K))
    (v : B → K) (c : K) (eigenvector : W v = c • v) :
    polynomialOperator f W v = f.eval c • v := by
  simp only [polynomialOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    operator_power_eigen W v c eigenvector, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  exact Polynomial.eval_eq_sum.symm

/-- The paper's operator `A = V f(W)`. -/
def filteredOperator (V W : Module.End K (B → K)) (f : Polynomial K) :
    Module.End K (B → K) := V * polynomialOperator f W

omit [Fintype B] in
theorem filteredOperator_eigen (V W : Module.End K (B → K)) (f : Polynomial K)
    (v : B → K) (sign count : K) (hV : V v = sign • v) (hW : W v = count • v) :
    filteredOperator V W f v = (sign * f.eval count) • v := by
  rw [filteredOperator, Module.End.mul_apply, polynomialOperator_eigen f W v count hW,
    map_smul, hV, smul_smul, mul_comm]

/-- The residual identity for exactly `A = V f(W)` and the paper's eigenvalues.
Interpolation is needed only on the good indices. -/
theorem filtered_residual_add_entry [DecidableEq B] [DecidableEq I]
    (basis : Module.Basis I K (B → K))
    (orthogonal : ∀ i j, i ≠ j → dotProduct (basis i) (basis j) = 0)
    (norm_nonzero : ∀ i, dotProduct (basis i) (basis i) ≠ 0)
    (V W : Module.End K (B → K)) (f : Polynomial K) (antisymmetricCount : I → ℕ)
    (hV : ∀ i, V (basis i) = (-1 : K) ^ antisymmetricCount i • basis i)
    (hW : ∀ i, W (basis i) = (antisymmetricCount i : K) • basis i)
    (bad : Finset I)
    (interpolates : ∀ i, i ∉ bad →
      f.eval (antisymmetricCount i : K) = (-1 : K) ^ antisymmetricCount i) (u w : B) :
    (∑ i ∈ bad,
      ((1 - (-1 : K) ^ antisymmetricCount i * f.eval (antisymmetricCount i : K)) *
        basis i u / dotProduct (basis i) (basis i)) * basis i w) +
      operatorEntry (filteredOperator V W f) u w = if u = w then 1 else 0 := by
  have heig (i : I) := filteredOperator_eigen V W f (basis i)
    ((-1 : K) ^ antisymmetricCount i) (antisymmetricCount i : K) (hV i) (hW i)
  have hgood (i : I) (hi : i ∉ bad) :
      (-1 : K) ^ antisymmetricCount i * f.eval (antisymmetricCount i : K) = 1 := by
    rw [interpolates i hi, ← mul_pow]
    simp
  have h := residual_entry_bad basis orthogonal norm_nonzero
    (filteredOperator V W f)
    (fun i => (-1 : K) ^ antisymmetricCount i * f.eval (antisymmetricCount i : K))
    heig bad hgood u w
  exact (sub_eq_iff_eq_add.mp h).symm

section PairSwap

variable {α : Type*} [DecidableEq α]

/-- The actual one-pair permutation operator, swapping the two coordinates. -/
def pairSwap : Module.End K ((α × α) → K) where
  toFun v p := v (p.2, p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pairSwap_single (a b : α) :
    pairSwap (Pi.single (a, b) (1 : K)) = Pi.single (b, a) 1 := by
  ext p
  rcases p with ⟨u, v⟩
  simp [pairSwap, Pi.single_apply, Prod.mk.injEq, and_comm]

def pairSymmetric (a b : α) : (α × α) → K :=
  Pi.single (a, b) 1 + Pi.single (b, a) 1

def pairAntisymmetric (a b : α) : (α × α) → K :=
  Pi.single (a, b) 1 - Pi.single (b, a) 1

theorem pairSwap_diagonal (a : α) :
    pairSwap (Pi.single (a, a) (1 : K)) = Pi.single (a, a) 1 := pairSwap_single a a

theorem pairSwap_symmetric (a b : α) :
    pairSwap (pairSymmetric (K := K) a b) = pairSymmetric a b := by
  rw [pairSymmetric, map_add, pairSwap_single, pairSwap_single]
  exact add_comm _ _

theorem pairSwap_antisymmetric (a b : α) :
    pairSwap (pairAntisymmetric (K := K) a b) = -pairAntisymmetric a b := by
  rw [pairAntisymmetric, map_sub, pairSwap_single, pairSwap_single, neg_sub]

omit [DecidableEq α] in
theorem pairSwap_involution (v : (α × α) → K) : pairSwap (pairSwap v) = v := by
  ext p
  rfl

variable [Fintype α]

theorem pairSymmetric_norm (a b : α) (different : a ≠ b) :
    dotProduct (pairSymmetric (K := K) a b) (pairSymmetric a b) = 2 := by
  norm_num [pairSymmetric, dotProduct_add, different, different.symm]

theorem pairAntisymmetric_norm (a b : α) (different : a ≠ b) :
    dotProduct (pairAntisymmetric (K := K) a b) (pairAntisymmetric a b) = 2 := by
  norm_num [pairAntisymmetric, dotProduct_sub, different, different.symm]

theorem pairSymmetric_orthogonal_antisymmetric (a b : α) :
    dotProduct (pairSymmetric (K := K) a b) (pairAntisymmetric a b) = 0 := by
  by_cases h : a = b
  · simp [h, pairAntisymmetric]
  · simp [pairSymmetric, pairAntisymmetric, dotProduct_sub, h, Ne.symm h]

end PairSwap

section TensorSwaps

variable {Node α : Type*} [Fintype Node] [DecidableEq Node]

def swapCoordinate (t : Node) (u : Node → α × α) : Node → α × α :=
  Function.update u t (u t).swap

def coordinateSwap (t : Node) : Module.End K ((Node → α × α) → K) where
  toFun v u := v (swapCoordinate t u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The concrete tensor of the one-pair vectors. -/
def tensorVector (pair : Node → (α × α) → K) (u : Node → α × α) : K :=
  ∏ t, pair t (u t)

omit [Fintype Node] in
theorem swapCoordinate_involution (t : Node) (u : Node → α × α) :
    swapCoordinate t (swapCoordinate t u) = u := by
  funext s
  by_cases h : s = t <;> simp [swapCoordinate, h, Function.update_of_ne]

omit [Fintype Node] in
theorem swapCoordinate_commute (s t : Node) (u : Node → α × α) :
    swapCoordinate s (swapCoordinate t u) = swapCoordinate t (swapCoordinate s u) := by
  by_cases h : s = t
  · rw [h]
  funext v
  by_cases hs : v = s
  · subst v
    simp [swapCoordinate, h, Ne.symm h]
  · by_cases ht : v = t
    · subst v
      simp [swapCoordinate, h, Ne.symm h]
    · simp [swapCoordinate, hs, ht, h, Ne.symm h]

omit [Fintype Node] in
/-- The actual coordinate permutation operators commute. -/
theorem coordinateSwap_commute (s t : Node) :
    Commute (coordinateSwap (K := K) (α := α) s) (coordinateSwap t) := by
  apply LinearMap.ext
  intro v
  funext u
  change v (swapCoordinate t (swapCoordinate s u)) = v (swapCoordinate s (swapCoordinate t u))
  rw [swapCoordinate_commute]

/-- Tensoring the one-pair eigenrelations gives each coordinate eigenrelation. -/
theorem coordinateSwap_tensor (pair : Node → (α × α) → K) (eigenvalue : Node → K)
    (local_eigen : ∀ t p, pair t p.swap = eigenvalue t * pair t p) (t : Node) :
    coordinateSwap t (tensorVector pair) = eigenvalue t • tensorVector pair := by
  ext u
  change (∏ s, pair s ((swapCoordinate t u) s)) = eigenvalue t * ∏ s, pair s (u s)
  rw [← Finset.mul_prod_erase Finset.univ
    (fun s => pair s ((swapCoordinate t u) s)) (Finset.mem_univ t)]
  have hprod : (∏ s ∈ Finset.univ.erase t, pair s ((swapCoordinate t u) s)) =
      ∏ s ∈ Finset.univ.erase t, pair s (u s) := by
    apply Finset.prod_congr rfl
    intro s hs
    simp [swapCoordinate, (Finset.mem_erase.mp hs).1]
  rw [hprod]
  simp only [swapCoordinate, Function.update_self, local_eigen]
  rw [mul_assoc, Finset.mul_prod_erase Finset.univ (fun s => pair s (u s)) (Finset.mem_univ t)]

/-- Simultaneously swap every pair in a block. -/
def simultaneousSwap : Module.End K ((Node → α × α) → K) where
  toFun v u := v (fun t => (u t).swap)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq Node] in
theorem simultaneousSwap_tensor (pair : Node → (α × α) → K) (eigenvalue : Node → K)
    (local_eigen : ∀ t p, pair t p.swap = eigenvalue t * pair t p) :
    simultaneousSwap (tensorVector pair) = (∏ t, eigenvalue t) • tensorVector pair := by
  ext u
  change (∏ t, pair t (u t).swap) = (∏ t, eigenvalue t) * ∏ t, pair t (u t)
  simp_rw [local_eigen]
  exact Finset.prod_mul_distrib

/-- The paper's concrete `W = 1/2 ∑ (I−Π_t)` on block coordinates. -/
def antisymmetryOperator : Module.End K ((Node → α × α) → K) :=
  (2 : K)⁻¹ • ∑ t : Node, (1 - coordinateSwap t)

theorem antisymmetryOperator_tensor (pair : Node → (α × α) → K)
    (eigenvalue : Node → K)
    (local_eigen : ∀ t p, pair t p.swap = eigenvalue t * pair t p) :
    antisymmetryOperator (tensorVector pair) =
      ((2 : K)⁻¹ * ∑ t, (1 - eigenvalue t)) • tensorVector pair := by
  simp only [antisymmetryOperator, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, Module.End.one_apply, coordinateSwap_tensor pair eigenvalue local_eigen]
  have hsub (t : Node) : tensorVector pair - eigenvalue t • tensorVector pair =
      (1 - eigenvalue t) • tensorVector pair := by rw [sub_smul, one_smul]
  simp_rw [hsub]
  rw [← Finset.sum_smul, smul_smul]

def swapSign (antisymmetric : Finset Node) (t : Node) : K :=
  if t ∈ antisymmetric then -1 else 1

theorem swapSign_product (antisymmetric : Finset Node) :
    (∏ t : Node, swapSign (K := K) antisymmetric t) = (-1 : K) ^ antisymmetric.card := by
  simp [swapSign]

theorem swapSign_count (antisymmetric : Finset Node) :
    (∑ t : Node, (1 - swapSign (K := K) antisymmetric t)) =
      2 * (antisymmetric.card : K) := by
  have hterm (t : Node) : 1 - swapSign (K := K) antisymmetric t =
      if t ∈ antisymmetric then 2 else 0 := by
    unfold swapSign
    split_ifs <;> ring
  simp_rw [hterm]
  simp [mul_comm]

/-- Simultaneous swapping multiplies a tensor by `(-1)^j`, where `j` counts
its antisymmetric factors. -/
theorem simultaneousSwap_tensor_count (pair : Node → (α × α) → K)
    (antisymmetric : Finset Node)
    (local_eigen : ∀ t p, pair t p.swap = swapSign antisymmetric t * pair t p) :
    simultaneousSwap (tensorVector pair) =
      (-1 : K) ^ antisymmetric.card • tensorVector pair := by
  rw [simultaneousSwap_tensor pair (swapSign antisymmetric) local_eigen, swapSign_product]

/-- The concrete averaged swap operator counts the tensor's antisymmetric
factors. Characteristic two is excluded explicitly. -/
theorem antisymmetryOperator_tensor_count (two_nonzero : (2 : K) ≠ 0)
    (pair : Node → (α × α) → K) (antisymmetric : Finset Node)
    (local_eigen : ∀ t p, pair t p.swap = swapSign antisymmetric t * pair t p) :
    antisymmetryOperator (tensorVector pair) =
      (antisymmetric.card : K) • tensorVector pair := by
  rw [antisymmetryOperator_tensor pair (swapSign antisymmetric) local_eigen,
    swapSign_count, ← mul_assoc, inv_mul_cancel₀ two_nonzero, one_mul]

/-- Inner products of concrete tensor vectors factor into one-pair inner
products. This transfers orthogonality from a pair basis to its tensor family. -/
theorem tensorVector_dotProduct [Fintype α]
    (left right : Node → (α × α) → K) :
    dotProduct (tensorVector left) (tensorVector right) =
      ∏ t, dotProduct (left t) (right t) := by
  classical
  simp only [dotProduct, tensorVector, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun t p => left t p * right t p)).symm

theorem tensorVector_orthogonal_of_factor [Fintype α]
    (left right : Node → (α × α) → K) (t : Node)
    (orthogonal : dotProduct (left t) (right t) = 0) :
    dotProduct (tensorVector left) (tensorVector right) = 0 := by
  rw [tensorVector_dotProduct]
  exact Finset.prod_eq_zero (Finset.mem_univ t) orthogonal

end TensorSwaps

end

end NtimeDspace.SpectralDeformation
