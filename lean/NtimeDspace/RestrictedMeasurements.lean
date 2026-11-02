import NtimeDspace.GroupedDeformation
import NtimeDspace.TensorBasisField

/-!
# Restricted measurements with repeated variables

An occupied position carries a variable and an integer sign. Distinct positions
may carry the same variable: their signs are added to form its coefficient.
Restricting the coefficients to a variable-group fiber gives exactly the
paper's group-restricted measurement. The triangle inequality bounds its
coefficient norm by the number of occupied positions, without any injectivity
assumption on the variable map.
-/

namespace NtimeDspace.RestrictedMeasurements

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open GroupedDeformation

variable {Label Var Group Index : Type*}

section TensorSigns

/-- The one-pair basis entries constructed directly over the integers. -/
def pairSign {r : ℕ} (index : Fin r × Fin r) : (Fin r × Fin r) → ℤ :=
  if index.1 = index.2 then Pi.single index 1
  else if index.1 < index.2 then Pi.single index 1 + Pi.single index.swap 1
  else Pi.single index 1 - Pi.single index.swap 1

theorem pairSign_entry {r : ℕ} (index p : Fin r × Fin r) :
    pairSign index p ∈ ({-1, 0, 1} : Finset ℤ) := by
  rcases index with ⟨a, b⟩
  rcases p with ⟨c, d⟩
  simp only [pairSign]
  split_ifs with heq hlt <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, Prod.swap_prod_mk, Prod.mk.injEq]
  all_goals split_ifs <;> simp_all

theorem pairSign_abs_le {r : ℕ} (index p : Fin r × Fin r) : |pairSign index p| ≤ 1 := by
  have h := pairSign_entry index p
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h <;> rw [h] <;> norm_num

/-- Casting these integer entries gives the already-verified field basis. -/
theorem pairSign_cast {K : Type*} [Field K] {r : ℕ} (index p : Fin r × Fin r) :
    (pairSign index p : K) = TensorBasisField.pairVector index p := by
  rcases index with ⟨a, b⟩
  simp only [pairSign, TensorBasisField.pairVector]
  split_ifs <;> simp [SpectralDeformation.pairSymmetric,
    SpectralDeformation.pairAntisymmetric, Pi.single_apply]

/-- Integer entries of the complete tensor eigenbasis. -/
def tensorSign {Node : Type*} [Fintype Node] {r : ℕ}
    (index w : TensorBasisField.Label Node r) : ℤ :=
  ∏ t, pairSign (index t) (w t)

theorem tensorSign_abs_le {Node : Type*} [Fintype Node] {r : ℕ}
    (index w : TensorBasisField.Label Node r) : |tensorSign index w| ≤ 1 := by
  rw [tensorSign, Finset.abs_prod]
  classical
  have hprod (set : Finset Node) : (∏ t ∈ set, |pairSign (index t) (w t)|) ≤ 1 := by
    induction set using Finset.induction_on with
    | empty => simp
    | @insert t set ht ih =>
        rw [Finset.prod_insert ht]
        exact (mul_le_mul_of_nonneg_left ih (abs_nonneg _)).trans
          (by simpa using pairSign_abs_le (index t) (w t))
  exact hprod Finset.univ

theorem tensorSign_cast {K Node : Type*} [Field K] [Fintype Node] [DecidableEq Node]
    {r : ℕ} (index w : TensorBasisField.Label Node r) :
    (tensorSign index w : K) = TensorBasisField.tensorFamily index w := by
  simp [tensorSign, TensorBasisField.tensorFamily, SpectralDeformation.tensorVector,
    pairSign_cast]

end TensorSigns

variable [Fintype Var] [DecidableEq Group]

/-- Add the signs of all occupied positions carrying this variable. Repeated
variables are deliberately retained in the sum. -/
def coefficient (occupied : Finset Label) (variableAt : Label → Var)
    (sign : Index → Label → ℤ) (index : Index) (groupOf : Var → Group)
    (group : Group) (v : LocalVariable groupOf group) : ℤ :=
  ∑ w ∈ occupied with variableAt w = v.val, sign index w

/-- A finite sum over variable fibers is the corresponding sum over positions
in the chosen group, even when several positions have the same variable. -/
theorem sum_local_fibers {A : Type*} [AddCommMonoid A]
    (occupied : Finset Label) (variableAt : Label → Var) (groupOf : Var → Group)
    (group : Group) (weight : Label → A) :
    (∑ v : LocalVariable groupOf group,
      ∑ w ∈ occupied with variableAt w = v.val, weight w) =
      ∑ w ∈ occupied with groupOf (variableAt w) = group, weight w := by
  classical
  calc
    _ = ∑ v ∈ Finset.univ.filter (fun v => groupOf v = group),
        ∑ w ∈ occupied with variableAt w = v, weight w :=
      (Finset.sum_subtype _ (by simp) _).symm
    _ = _ := by
      simpa using Finset.sum_fiberwise_eq_sum_filter occupied
        (Finset.univ.filter (fun v => groupOf v = group)) variableAt weight

/-- The coefficient norm is at most the number of occupied positions in this
group. Cancellation among repeated variables can only decrease this norm. -/
theorem coefficient_norm_le_group_card (occupied : Finset Label) (variableAt : Label → Var)
    (sign : Index → Label → ℤ) (index : Index) (groupOf : Var → Group)
    (group : Group) (sign_bound : ∀ w ∈ occupied, |sign index w| ≤ 1) :
    (∑ v, |coefficient occupied variableAt sign index groupOf group v|) ≤
      ((occupied.filter (fun w => groupOf (variableAt w) = group)).card : ℤ) := by
  classical
  calc
    _ ≤ ∑ v : LocalVariable groupOf group,
        ∑ w ∈ occupied with variableAt w = v.val, |sign index w| := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w ∈ occupied with groupOf (variableAt w) = group, |sign index w| :=
      sum_local_fibers occupied variableAt groupOf group _
    _ ≤ ∑ _w ∈ occupied.filter (fun w => groupOf (variableAt w) = group), (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro w hw
      exact sign_bound w (Finset.mem_filter.mp hw).1
    _ = _ := by simp

theorem coefficient_norm_le_card (occupied : Finset Label) (variableAt : Label → Var)
    (sign : Index → Label → ℤ) (index : Index) (groupOf : Var → Group)
    (group : Group) (sign_bound : ∀ w ∈ occupied, |sign index w| ≤ 1) :
    (∑ v, |coefficient occupied variableAt sign index groupOf group v|) ≤
      (occupied.card : ℤ) := by
  exact (coefficient_norm_le_group_card occupied variableAt sign index groupOf group
    sign_bound).trans (Int.ofNat_le.mpr (Finset.card_filter_le _ _))

/-- The manuscript's D3 coefficient-norm bound follows from occupancy alone. -/
theorem coefficient_norm_le (occupied : Finset Label) (variableAt : Label → Var)
    (sign : Index → Label → ℤ) (index : Index) (groupOf : Var → Group)
    (group : Group) (bound : ℕ) (occupancy_bound : occupied.card ≤ bound)
    (sign_bound : ∀ w ∈ occupied, |sign index w| ≤ 1) :
    (∑ v, |coefficient occupied variableAt sign index groupOf group v|) ≤ (bound : ℤ) :=
  (coefficient_norm_le_card occupied variableAt sign index groupOf group sign_bound).trans
    (Int.ofNat_le.mpr occupancy_bound)

/-- For the concrete tensor signs, D3 follows with `D = r^(2Q)` and requires
neither an assumed sign bound nor injectivity of the position-to-variable map. -/
theorem tensor_coefficient_norm_le_dimension {Node : Type*} [Fintype Node] {r : ℕ}
    (occupied : Finset (TensorBasisField.Label Node r))
    (variableAt : TensorBasisField.Label Node r → Var)
    (index : TensorBasisField.Label Node r) (groupOf : Var → Group) (group : Group) :
    (∑ v, |coefficient occupied variableAt tensorSign index groupOf group v|) ≤
      (r ^ (2 * Fintype.card Node) : ℕ) := by
  apply coefficient_norm_le
  · have h := occupied.card_le_univ
    simpa [TensorBasisField.Label, Fintype.card_fun, Fintype.card_prod, ← pow_two, ← pow_mul] using h
  · intro w _
    exact tensorSign_abs_le index w

/-- Evaluating the aggregated coefficient row is exactly summing its occupied
positions. Every occurrence of a repeated variable uses the same Boolean bit. -/
theorem integerMeasurement_eq_restricted_sum (occupied : Finset Label)
    (variableAt : Label → Var) (sign : Index → Label → ℤ) (index : Index)
    (groupOf : Var → Group) (group : Group) (assignment : Var → Bool) :
    integerMeasurement groupOf group (coefficient occupied variableAt sign index groupOf group)
      (partitionAssignmentEquiv groupOf assignment group) =
      ∑ w ∈ occupied with groupOf (variableAt w) = group,
        sign index w * CountingPolynomial.boolValue (assignment (variableAt w)) := by
  classical
  calc
    _ = ∑ v : LocalVariable groupOf group,
        ∑ w ∈ occupied with variableAt w = v.val,
          sign index w * CountingPolynomial.boolValue (assignment (variableAt w)) := by
      unfold integerMeasurement coefficient
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
      rfl
    _ = _ := sum_local_fibers occupied variableAt groupOf group _

/-- The exact integer row can be cast into any commutative ring, including the
finite field used by the modular counter. -/
theorem integerMeasurement_cast_eq_restricted_sum {K : Type*} [CommRing K]
    (occupied : Finset Label) (variableAt : Label → Var)
    (sign : Index → Label → ℤ) (index : Index)
    (groupOf : Var → Group) (group : Group) (assignment : Var → Bool) :
    (integerMeasurement groupOf group (coefficient occupied variableAt sign index groupOf group)
      (partitionAssignmentEquiv groupOf assignment group) : K) =
      ∑ w ∈ occupied with groupOf (variableAt w) = group,
        (sign index w : K) * CountingPolynomial.boolValue (assignment (variableAt w)) := by
  rw [integerMeasurement_eq_restricted_sum]
  simp [CountingPolynomial.boolValue]

/-- Concrete tensor measurements agree with their field-valued spectral row
after casting; the underlying measurement is still the bounded integer sum. -/
theorem tensor_integerMeasurement_cast {K Node : Type*} [Field K]
    [Fintype Node] [DecidableEq Node] {r : ℕ}
    (occupied : Finset (TensorBasisField.Label Node r))
    (variableAt : TensorBasisField.Label Node r → Var)
    (index : TensorBasisField.Label Node r) (groupOf : Var → Group) (group : Group)
    (assignment : Var → Bool) :
    (integerMeasurement groupOf group
      (coefficient occupied variableAt tensorSign index groupOf group)
      (partitionAssignmentEquiv groupOf assignment group) : K) =
      ∑ w ∈ occupied with groupOf (variableAt w) = group,
        TensorBasisField.tensorFamily (K := K) index w *
          CountingPolynomial.boolValue (assignment (variableAt w)) := by
  rw [integerMeasurement_cast_eq_restricted_sum]
  simp only [tensorSign_cast]

/-- The actual Boolean measurement stays in the required finite integer range. -/
theorem integerMeasurement_abs_le (occupied : Finset Label) (variableAt : Label → Var)
    (sign : Index → Label → ℤ) (index : Index) (groupOf : Var → Group)
    (group : Group) (bound : ℕ) (occupancy_bound : occupied.card ≤ bound)
    (sign_bound : ∀ w ∈ occupied, |sign index w| ≤ 1)
    (assignment : LocalAssignment groupOf group) :
    |integerMeasurement groupOf group (coefficient occupied variableAt sign index groupOf group)
      assignment| ≤ (bound : ℤ) :=
  (GroupedDeformation.integerMeasurement_abs_le _ _ _ _).trans
    (coefficient_norm_le occupied variableAt sign index groupOf group bound occupancy_bound sign_bound)

/-- Summing the restricted rows recovers the full measurement. Empty groups
contribute zero, and no occupied position is omitted or counted twice. -/
theorem sum_groups_integerMeasurement [Fintype Group] (occupied : Finset Label)
    (variableAt : Label → Var) (sign : Index → Label → ℤ) (index : Index)
    (groupOf : Var → Group) (assignment : Var → Bool) :
    (∑ group, integerMeasurement groupOf group
      (coefficient occupied variableAt sign index groupOf group)
      (partitionAssignmentEquiv groupOf assignment group)) =
      ∑ w ∈ occupied, sign index w * CountingPolynomial.boolValue (assignment (variableAt w)) := by
  simp_rw [integerMeasurement_eq_restricted_sum]
  exact Finset.sum_fiberwise occupied (fun w => groupOf (variableAt w)) _

theorem sum_groups_tensor_integerMeasurement_cast {K Node : Type*} [Field K]
    [Fintype Node] [DecidableEq Node] [Fintype Group] {r : ℕ}
    (occupied : Finset (TensorBasisField.Label Node r))
    (variableAt : TensorBasisField.Label Node r → Var)
    (index : TensorBasisField.Label Node r) (groupOf : Var → Group)
    (assignment : Var → Bool) :
    (∑ group, (integerMeasurement groupOf group
      (coefficient occupied variableAt tensorSign index groupOf group)
      (partitionAssignmentEquiv groupOf assignment group) : K)) =
      ∑ w ∈ occupied, TensorBasisField.tensorFamily (K := K) index w *
        CountingPolynomial.boolValue (assignment (variableAt w)) := by
  simp_rw [tensor_integerMeasurement_cast]
  exact Finset.sum_fiberwise occupied (fun w => groupOf (variableAt w)) _

omit [DecidableEq Group] in
/-- Every copy/basis-index pair contributes one row to each group. -/
theorem restricted_row_card {Copy : Type*} [Fintype Copy] [Fintype Index] [Fintype Group] :
    Fintype.card (Group × Copy × Index) =
      Fintype.card Group * Fintype.card Copy * Fintype.card Index := by
  simp [Fintype.card_prod, Nat.mul_assoc]

omit [DecidableEq Group] in
/-- The same count when only the occupied copy indices and bad basis indices
are retained as explicit finite sets. -/
theorem restricted_row_finset_card {Copy : Type*} [Fintype Group]
    (copies : Finset Copy) (indices : Finset Index) :
    Fintype.card (Group × copies × indices) =
      Fintype.card Group * copies.card * indices.card := by
  simp [Fintype.card_prod, Nat.mul_assoc]

end

end NtimeDspace.RestrictedMeasurements
