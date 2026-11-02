import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite grouped-counting identity

This is the distributivity and unique-measurement part of the manuscript's
Fact `grouped`. An assignment is a dependent tuple of group assignments.
`measure g` records its group's measurements, and `allowed g` imposes local
constraints such as requiring the support variables to equal one. A local
factor may depend on the entire measurement tuple.

The theorem works over every commutative semiring, in particular over rational
polynomials and finite-field polynomials. It does not assume any deformation
identity. The remaining application obligations are the partition equivalence,
the bounds on actual measurement values, and the equality between local factors
and the manuscript's deformed clause factors. None is asserted here.
-/

namespace NtimeDspace.GroupedCounting

open scoped BigOperators

variable {Group : Type*} [Fintype Group] [DecidableEq Group]
variable {LocalAssignment Measurement : Group → Type*}
variable [∀ group, Fintype (LocalAssignment group)]
variable [∀ group, Fintype (Measurement group)]
variable [∀ group, DecidableEq (Measurement group)]
variable {R : Type*} [CommSemiring R]

/-- For a fixed measurement tuple, choices in distinct groups are independent. -/
theorem fixed_measurement_factorization
    (localFactor : ∀ group, LocalAssignment group → R) :
    (∑ assignment : ∀ group, LocalAssignment group,
        ∏ group, localFactor group (assignment group)) =
      ∏ group, ∑ assignment, localFactor group assignment := by
  exact (Fintype.prod_sum localFactor).symm

omit [∀ group, Fintype (LocalAssignment group)] in
/-- Each full assignment contributes at exactly its own measurement tuple. -/
theorem unique_measurement_sum
    (measure : ∀ group, LocalAssignment group → Measurement group)
    (allowed : ∀ group, LocalAssignment group → Prop)
    [∀ group, DecidablePred (allowed group)]
    (weight : ∀ group, LocalAssignment group → (∀ group, Measurement group) → R)
    (assignment : ∀ group, LocalAssignment group) :
    (∑ measured : ∀ group, Measurement group,
      ∏ group,
        if measure group (assignment group) = measured group ∧ allowed group (assignment group)
        then weight group (assignment group) measured else 0) =
      if ∀ group, allowed group (assignment group)
      then ∏ group, weight group (assignment group) (fun group => measure group (assignment group))
      else 0 := by
  classical
  have hcondition (measured : ∀ group, Measurement group) :
      (∀ group, measure group (assignment group) = measured group ∧
          allowed group (assignment group)) ↔
        measured = (fun group => measure group (assignment group)) ∧
          ∀ group, allowed group (assignment group) := by
    constructor
    · intro h
      exact ⟨funext (fun group => (h group).1.symm), fun group => (h group).2⟩
    · rintro ⟨rfl, h⟩ group
      exact ⟨rfl, h group⟩
  simp_rw [Fintype.prod_ite_zero, hcondition]
  by_cases hallowed : ∀ group, allowed group (assignment group)
  · simp [hallowed]
  · simp [hallowed]

/-- The exact grouped-counting equality, with no truncation of a polynomial.
Its hypotheses encode finite group assignments and their exact measurements;
they do not claim that those data admit the paper's small-space accessors. -/
theorem grouped_counting_identity
    (measure : ∀ group, LocalAssignment group → Measurement group)
    (allowed : ∀ group, LocalAssignment group → Prop)
    [∀ group, DecidablePred (allowed group)]
    (weight : ∀ group, LocalAssignment group → (∀ group, Measurement group) → R) :
    (∑ assignment : ∀ group, LocalAssignment group,
      if ∀ group, allowed group (assignment group)
      then ∏ group, weight group (assignment group) (fun group => measure group (assignment group))
      else 0) =
    ∑ measured : ∀ group, Measurement group,
      ∏ group, ∑ assignment : LocalAssignment group,
        if measure group assignment = measured group ∧ allowed group assignment
        then weight group assignment measured else 0 := by
  classical
  symm
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro assignment _
  exact unique_measurement_sum measure allowed weight assignment

end NtimeDspace.GroupedCounting
