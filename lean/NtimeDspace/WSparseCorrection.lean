import NtimeDspace.WSchedulePlacement
import NtimeDspace.SparseCorrection

/-!
The two formula-level theorems of `SparseCorrection`, for weighted constraint
systems. The scans themselves are generic and are reused unchanged.
-/

namespace NtimeDspace.WSparseCorrection

open scoped BigOperators
open NtimeDspace.SparseCorrection hiding correction_correct compressed_taylor_correct

variable {n : ℕ} {K : Type*} [CommRing K]

/-- The polynomial equality is proved from the two accessor contracts; it is
not a premise of the running scalar procedure. -/
theorem correction_correct (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K)
    (evaluateCoefficient : WeightedSystem.Incidence formula → Fin n → K → K)
    (evaluation : ∀ inc v x, evaluateCoefficient inc v x = (L inc.1 inc.2 v).eval x)
    (subset : Finset (Fin n)) (selected : Fin n → Bool)
    (membership : ∀ v, selected v = decide (v ∈ subset))
    (node point : K) (inc : WeightedSystem.Incidence formula) :
    correction evaluateCoefficient selected node point inc =
      (WGroupedDeformation.taylorCorrection formula L node subset inc).eval point := by
  rw [correction_eq_sum, WGroupedDeformation.taylorCorrection, PolynomialFacts.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro v _
  simp only [membership, decide_eq_true_eq]
  by_cases member : v ∈ subset
  · simp [member, evaluation, Polynomial.taylor_eval, add_comm]
  · simp [member]

/-- Exact support-width masks feed the polynomial correction without assigning
bits to unused parser-capacity positions. -/
theorem compressed_taylor_correct {capacity : ℕ} (formula : WeightedSystem.System n)
    (L : WeightedSystem.Coefficients formula K)
    (evaluateCoefficient : WeightedSystem.Incidence formula → Fin n → K → K)
    (evaluation : ∀ inc v x, evaluateCoefficient inc v x = (L inc.1 inc.2 v).eval x)
    (support : List (Fin n)) (valid : SupportAssignment.Valid capacity support)
    (mask : Fin support.length → Bool) (node point : K) (inc : WeightedSystem.Incidence formula) :
    compressed evaluateCoefficient (SupportAssignment.extendMask valid.2 mask)
      (SupportAssignment.encode support) node point inc =
      some ((WGroupedDeformation.taylorCorrection formula L node
        (maskSubset support (Nat.le_refl _) mask) inc).eval point) := by
  rcases valid with ⟨ordered, count⟩
  rw [compressed_encode evaluateCoefficient support ⟨ordered, count⟩]
  have selected : SupportAssignment.assignmentBit support count
      (SupportAssignment.extendMask count mask) =
      SupportAssignment.assignmentBit support (Nat.le_refl _) mask := by
    funext v
    exact SupportAssignment.assignmentBit_extendMask support count mask v
  rw [selected]
  congr 1
  exact correction_correct formula L evaluateCoefficient evaluation
    (maskSubset support (Nat.le_refl _) mask)
    (SupportAssignment.assignmentBit support (Nat.le_refl _) mask)
    (maskSubset_membership support (Nat.le_refl _) mask) node point inc

end NtimeDspace.WSparseCorrection
