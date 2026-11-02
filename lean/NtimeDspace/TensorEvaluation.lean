import NtimeDspace.GroupedInnerLoop
import NtimeDspace.SpectralIndexing

/-!
Scalar access to the tensor entries, norms, antisymmetric counts, and mismatch
products used by the finite-field deformation. Runtime definitions scan the
node coordinates and retain scalar accumulators. They construct no vector,
matrix, polynomial, or coordinate set. Tape refinements remain separate.
-/

namespace NtimeDspace.TensorEvaluation

open scoped BigOperators
open GroupedAssignmentEvaluation

variable {r Q : ℕ} {K : Type*} [Field K]

abbrev Label (r Q : ℕ) := Fin Q → Fin r × Fin r

def pairEntry (index position : Fin r × Fin r) : K :=
  if index.1 = index.2 then (if position = index then 1 else 0)
  else if index.1 < index.2 then
    (if position = index then 1 else 0) + (if position = index.swap then 1 else 0)
  else (if position = index then 1 else 0) - (if position = index.swap then 1 else 0)

theorem pairEntry_correct (index position : Fin r × Fin r) :
    pairEntry (K := K) index position = TensorBasisField.pairVector index position := by
  simp only [pairEntry, TensorBasisField.pairVector]
  by_cases diagonal : index.1 = index.2
  · simp [diagonal, Pi.single_apply, eq_comm]
  · by_cases ordered : index.1 < index.2
    · simp [diagonal, ordered, SpectralDeformation.pairSymmetric,
        Pi.single_apply, Prod.swap, eq_comm]
    · simp [diagonal, ordered, SpectralDeformation.pairAntisymmetric,
        Pi.single_apply, Prod.swap, eq_comm]

def tensorEntry (index position : Label r Q) : K :=
  scanProduct (fun node => pairEntry (index node) (position node)) 1

theorem tensorEntry_correct (index position : Label r Q) :
    tensorEntry (K := K) index position = TensorBasisField.tensorFamily index position := by
  simp only [tensorEntry, scanProduct_correct, mul_one, pairEntry_correct,
    TensorBasisField.tensorFamily, SpectralDeformation.tensorVector]

def normExponent (index : Label r Q) : ℕ :=
  scanSum (fun node => if (index node).1 ≠ (index node).2 then 1 else 0) 0

theorem normExponent_correct (index : Label r Q) :
    normExponent index = (Finset.univ.filter (fun node => (index node).1 ≠ (index node).2)).card := by
  simp only [normExponent, scanSum_correct, Nat.add_zero, Finset.card_filter]

theorem normExponent_le (index : Label r Q) : normExponent index ≤ Q := by
  rw [normExponent_correct]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

def tensorNorm (index : Label r Q) : K := (2 : K) ^ normExponent index

theorem tensorNorm_correct (index : Label r Q) :
    tensorNorm (K := K) index =
      dotProduct (TensorBasisField.tensorFamily index) (TensorBasisField.tensorFamily index) := by
  rw [tensorNorm, normExponent_correct, TensorBasisField.tensorFamily_norm]

theorem tensorNorm_nonzero (two_nonzero : (2 : K) ≠ 0) (index : Label r Q) :
    tensorNorm (K := K) index ≠ 0 := pow_ne_zero _ two_nonzero

def antisymmetricCount (index : Label r Q) : ℕ :=
  scanSum (fun node => if (index node).2 < (index node).1 then 1 else 0) 0

theorem antisymmetricCount_correct (index : Label r Q) :
    antisymmetricCount index = TensorBasisField.antisymmetricCount index := by
  simp only [antisymmetricCount, scanSum_correct, Nat.add_zero,
    TensorBasisField.antisymmetricCount, TensorBasisField.antisymmetricCoordinates,
    Finset.card_filter]

theorem antisymmetricCount_le (index : Label r Q) : antisymmetricCount index ≤ Q := by
  rw [antisymmetricCount_correct, TensorBasisField.antisymmetricCount,
    TensorBasisField.antisymmetricCoordinates]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

def sameLabel (first second : Label r Q) : Bool :=
  GroupedInnerLoop.scanAll (fun node => decide (first node = second node))

theorem sameLabel_correct (first second : Label r Q) :
    sameLabel first second = true ↔ first = second := by
  simp only [sameLabel, GroupedInnerLoop.scanAll_correct, decide_eq_true_eq, funext_iff]

def mismatchProduct (nodeValue : Fin Q → K) (u w : Label r Q) (point : K) : K :=
  scanProduct (fun node =>
    if (w node).1 ≠ (u node).2 then 1 - (nodeValue node)⁻¹ * point else 1) 1

theorem mismatchProduct_correct (nodeValue : Fin Q → K) (u w : Label r Q) (point : K) :
    mismatchProduct nodeValue u w point =
      (DeformationConstruction.phi nodeValue
        (fun label node => (label node).1) (fun label node => (label node).2) u w).eval point := by
  simp only [mismatchProduct, scanProduct_correct, mul_one,
    DeformationConstruction.phi, DeformationConstruction.mismatchNodes,
    Finset.prod_filter, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro node _
  split_ifs <;> simp [DeformationConstruction.nodeFactor]

end NtimeDspace.TensorEvaluation
