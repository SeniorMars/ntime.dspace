import NtimeDspace.DeformationConstruction
import Mathlib.Data.Matrix.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

/-!
The matrix locality argument in Kintali's deformation. A power of an operator
that changes at most one coordinate can connect only labels within its power's
Hamming distance. Polynomial evaluation and the global swap therefore give the
required bound on mismatch nodes. The matrices below are explicit.
-/

namespace NtimeDspace.MatrixLocality

noncomputable section

open scoped BigOperators

variable {B K : Type*} [Fintype B] [DecidableEq B] [Field K]

def SupportBound (distance : B → B → ℕ) (A : Matrix B B K) (bound : ℕ) : Prop :=
  ∀ u w, A u w ≠ 0 → distance u w ≤ bound

omit [DecidableEq B] in
theorem supportBound_mul (distance : B → B → ℕ)
    (triangle : ∀ u v w, distance u w ≤ distance u v + distance v w)
    (A C : Matrix B B K) (a c : ℕ)
    (left : SupportBound distance A a) (right : SupportBound distance C c) :
    SupportBound distance (A * C) (a + c) := by
  intro u w nonzero
  rw [Matrix.mul_apply] at nonzero
  obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  exact (triangle u v w).trans (Nat.add_le_add
    (left u v (left_ne_zero_of_mul hv)) (right v w (right_ne_zero_of_mul hv)))

theorem supportBound_pow (distance : B → B → ℕ)
    (self : ∀ u, distance u u = 0)
    (triangle : ∀ u v w, distance u w ≤ distance u v + distance v w)
    (W : Matrix B B K) (one_step : SupportBound distance W 1) (power : ℕ) :
    SupportBound distance (W ^ power) power := by
  induction power with
  | zero =>
      intro u w nonzero
      by_cases same : u = w
      · subst w; simp [self]
      · simp [same] at nonzero
  | succ power ih =>
      rw [pow_succ]
      exact supportBound_mul distance triangle _ _ _ _ ih one_step

/-- Direct finite polynomial evaluation at a matrix. -/
def matrixPolynomial (f : Polynomial K) (W : Matrix B B K) : Matrix B B K :=
  ∑ power ∈ f.support, f.coeff power • W ^ power

theorem matrixPolynomial_apply (f : Polynomial K) (W : Matrix B B K) (u w : B) :
    matrixPolynomial f W u w = ∑ power ∈ f.support, f.coeff power * (W ^ power) u w := by
  simp [matrixPolynomial, Matrix.sum_apply]

theorem matrixPolynomial_support (distance : B → B → ℕ)
    (self : ∀ u, distance u u = 0)
    (triangle : ∀ u v w, distance u w ≤ distance u v + distance v w)
    (W : Matrix B B K) (one_step : SupportBound distance W 1) (f : Polynomial K) :
    SupportBound distance (matrixPolynomial f W) f.natDegree := by
  intro u w nonzero
  rw [matrixPolynomial_apply] at nonzero
  obtain ⟨power, hp, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  exact (supportBound_pow distance self triangle W one_step power u w
    (right_ne_zero_of_mul hn)).trans (Polynomial.le_natDegree_of_mem_supp power hp)

section Swaps

variable {Node Group : Type*} [Fintype Node] [DecidableEq Node]
variable [Fintype Group] [DecidableEq Group]

abbrev Label (Node Group : Type*) := Node → Group × Group

def swapAt (node : Node) (label : Label Node Group) : Label Node Group :=
  Function.update label node (label node).swap

def swapAll (label : Label Node Group) : Label Node Group := fun node => (label node).swap

def swapMatrix (node : Node) : Matrix (Label Node Group) (Label Node Group) K :=
  fun u w => if u = swapAt node w then 1 else 0

def Wmatrix : Matrix (Label Node Group) (Label Node Group) K :=
  (2 : K)⁻¹ • ∑ node : Node, (1 - swapMatrix node)

def Vmatrix : Matrix (Label Node Group) (Label Node Group) K :=
  fun u w => if w = swapAll u then 1 else 0

def Amatrix (f : Polynomial K) : Matrix (Label Node Group) (Label Node Group) K :=
  Vmatrix * matrixPolynomial f Wmatrix

omit [Fintype Group] in
theorem swapAt_distance (node : Node) (w : Label Node Group) :
    hammingDist (swapAt node w) w ≤ 1 := by
  unfold hammingDist
  calc
    _ ≤ ({node} : Finset Node).card := by
      apply Finset.card_le_card
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have : t = node := by
        by_contra different
        exact ht (by simp [swapAt, different])
      simpa using this
    _ = 1 := Finset.card_singleton node

omit [Fintype Group] in
theorem Wmatrix_one_step :
    SupportBound hammingDist (Wmatrix : Matrix (Label Node Group) (Label Node Group) K) 1 := by
  intro u w nonzero
  have hsum : (∑ node : Node, ((1 - swapMatrix node :
      Matrix (Label Node Group) (Label Node Group) K) u w)) ≠ 0 := by
    intro hz
    apply nonzero
    simp only [Wmatrix, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    rw [hz, mul_zero]
  obtain ⟨node, _, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  by_cases same : u = w
  · subst w; simp
  · have swapped : u = swapAt node w := by
      by_contra different
      simp [swapMatrix, same, different] at hn
    rw [swapped]
    exact swapAt_distance node w

theorem Amatrix_apply (f : Polynomial K) (u w : Label Node Group) :
    Amatrix f u w = matrixPolynomial f Wmatrix (swapAll u) w := by
  simp [Amatrix, Matrix.mul_apply, Vmatrix]

omit [DecidableEq Node] [Fintype Group] in
theorem mismatch_card_le_distance (u w : Label Node Group) :
    (DeformationConstruction.mismatchNodes
      (fun label node => (label node).1) (fun label node => (label node).2) u w).card ≤
        hammingDist (swapAll u) w := by
  apply Finset.card_le_card
  intro node hn
  simp only [DeformationConstruction.mismatchNodes, Finset.mem_filter,
    Finset.mem_univ, true_and] at hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro equal
  exact hn (congrArg Prod.fst equal).symm

/-- The paper's locality property follows from the explicit swap matrices:
nonzero `A[u,w]` allows at most `degree f` mismatches. -/
theorem Amatrix_locality (f : Polynomial K) (u w : Label Node Group)
    (nonzero : Amatrix f u w ≠ 0) :
    (DeformationConstruction.mismatchNodes
      (fun label node => (label node).1) (fun label node => (label node).2) u w).card ≤
        f.natDegree := by
  rw [Amatrix_apply] at nonzero
  exact (mismatch_card_le_distance u w).trans
    (matrixPolynomial_support hammingDist hammingDist_self hammingDist_triangle
      Wmatrix Wmatrix_one_step f (swapAll u) w nonzero)

end Swaps

end

end NtimeDspace.MatrixLocality
