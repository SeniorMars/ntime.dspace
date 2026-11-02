import NtimeDspace.Counting
import NtimeDspace.CoefficientRecursion
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fintype.EquivFin

/-!
Enumerating one local Boolean assignment with a binary mask and scalar
accumulator. Neither the list of assignments nor a table of their contributions
appears in the procedure. The callback reads any assignment bit on demand.
These are functional arithmetic-loop theorems; callback implementation, binary
register representation, and CSLib machine compilation remain separate.
-/

namespace NtimeDspace.AssignmentLoop

open scoped BigOperators

/-- Random access to one assignment held as a binary counter value. -/
def assignment (width mask : ℕ) : Assignment width :=
  fun bit => mask.testBit bit.val

theorem assignment_injective (width : ℕ) :
    Function.Injective (fun mask : Fin (2 ^ width) => assignment width mask.val) := by
  intro first second same
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases within : bit < width
  · exact congrFun same ⟨bit, within⟩
  · have power : 2 ^ width ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (first.isLt.trans_le power),
      Nat.testBit_lt_two_pow (second.isLt.trans_le power)]

theorem assignment_bijective (width : ℕ) :
    Function.Bijective (fun mask : Fin (2 ^ width) => assignment width mask.val) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨assignment_injective width, by simp⟩

/-- The inverse exists only for proofs; the loop below uses the explicit
forward bit accessor and never calls this inverse. -/
noncomputable def assignmentEquiv (width : ℕ) : Fin (2 ^ width) ≃ Assignment width :=
  Equiv.ofBijective _ (assignment_bijective width)

/-- Descending tail-recursive binary-mask loop with one scalar accumulator.
Its bound takes width+1 binary bits, and every visited mask takes width bits. -/
def sumAssignments {R : Type*} [AddMonoid R] (width : ℕ)
    (contribution : Assignment width → R) (accumulator : R) : R :=
  sumLoop (fun mask => contribution (assignment width mask)) (2 ^ width) accumulator

/-- Every Boolean assignment contributes exactly once, including the single
empty assignment at width zero. -/
theorem sumAssignments_correct {R : Type*} [AddCommMonoid R] (width : ℕ)
    (contribution : Assignment width → R) (accumulator : R) :
    sumAssignments width contribution accumulator =
      (∑ a : Assignment width, contribution a) + accumulator := by
  rw [sumAssignments, sumLoop_correct]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  exact (assignmentEquiv width).sum_comp contribution

/-- Filtering is evaluated one mask at a time; it does not construct a list of
the assignments satisfying the predicate. -/
def sumFiltered {R : Type*} [AddMonoid R] (width : ℕ)
    (accept : Assignment width → Bool) (contribution : Assignment width → R) : R :=
  sumAssignments width (fun a => if accept a then contribution a else 0) 0

theorem sumFiltered_correct {R : Type*} [AddCommMonoid R] (width : ℕ)
    (accept : Assignment width → Bool) (contribution : Assignment width → R) :
    sumFiltered width accept contribution =
      ∑ a : Assignment width, if accept a then contribution a else 0 := by
  simp [sumFiltered, sumAssignments_correct]

/-- For a prime-field accumulator every intermediate scalar value has a
canonical representative below the prime. This says nothing about hidden
allocation by the callback, which must be refined separately. -/
theorem accumulator_bound {p : ℕ} [Fact p.Prime] (accumulator : ZMod p) :
    accumulator.val < p := ZMod.val_lt accumulator

/-- Every mask accessed by the loop has no set bits outside the local group. -/
theorem mask_has_no_high_bits (width mask : ℕ) (within : mask < 2 ^ width)
    (bit : ℕ) (high : width ≤ bit) : mask.testBit bit = false :=
  Nat.testBit_lt_two_pow (within.trans_le (Nat.pow_le_pow_right (by decide) high))

end NtimeDspace.AssignmentLoop
