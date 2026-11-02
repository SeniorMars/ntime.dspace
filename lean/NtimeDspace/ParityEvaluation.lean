import NtimeDspace.ParityInterpolation
import NtimeDspace.CoefficientRecursion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Group.Int.Even

/-!
# Scalar evaluation of the finite-field parity interpolant

The executable definitions use indexed sum/product loops, integer parity,
field arithmetic, and the signed window start. They do not construct a
polynomial, a finite set, or a list of interpolation nodes. Polynomial and
finite-set expressions occur only in correctness statements and proofs.

Field operations remain arithmetic primitives; no machine resource bound is
asserted here. The denominator theorem ensures that every division actually
performed by a valid interpolation query has a nonzero denominator.
-/

namespace NtimeDspace.ParityEvaluation

open scoped BigOperators
open ParityInterpolation

/-- Descending scalar product loop with an explicit accumulator. -/
def productLoop {R : Type*} [Monoid R] (term : ℕ → R) : ℕ → R → R
  | 0, accumulator => accumulator
  | count + 1, accumulator => productLoop term count (term count * accumulator)

theorem productLoop_correct {R : Type*} [CommMonoid R] (term : ℕ → R)
    (count : ℕ) (accumulator : R) :
    productLoop term count accumulator = (∏ index ∈ Finset.range count, term index) * accumulator := by
  induction count generalizing accumulator with
  | zero => simp [productLoop]
  | succ count ih => simp [productLoop, ih, Finset.prod_range_succ, mul_assoc]

theorem sum_window {R : Type*} [AddCommMonoid R] (start : ℤ) (width : ℕ) (term : ℤ → R) :
    (∑ node ∈ integerWindow start width, term node) =
      ∑ slot ∈ Finset.range width, term (start + slot) := by
  simp [integerWindow, Int.Ico_eq_finset_map, Finset.sum_map]

theorem product_window {R : Type*} [CommMonoid R] (start : ℤ) (width : ℕ) (term : ℤ → R) :
    (∏ node ∈ integerWindow start width, term node) =
      ∏ slot ∈ Finset.range width, term (start + slot) := by
  simp [integerWindow, Int.Ico_eq_finset_map, Finset.prod_map]

variable (p : ℕ) [Fact p.Prime]

/-- The parity sign is computed by integer remainder, including negative
integer nodes, rather than by an integer exponentiation procedure. -/
def paritySign (integer : ℤ) : ZMod p := if integer % 2 = 0 then 1 else -1

theorem paritySign_correct (integer : ℤ) : paritySign p integer = (-1 : ZMod p) ^ integer := by
  simp only [paritySign, neg_one_zpow_eq_ite, Int.even_iff]

def node (start : ℤ) (slot : ℕ) : ZMod p := (start + (slot : ℤ) : ℤ)

/-- A single Lagrange basis value. The diagonal slot contributes one and does
not execute a division. -/
def basisValue (start : ℤ) (width slot : ℕ) (x : ZMod p) : ZMod p :=
  productLoop (fun other =>
    if other = slot then 1 else (x - node p start other) / (node p start slot - node p start other))
    width 1

theorem basisValue_correct (start : ℤ) (width slot : ℕ) (x : ZMod p) :
    basisValue p start width slot x =
      (Lagrange.basis (integerWindow start width) (fun integer : ℤ => (integer : ZMod p))
        (start + slot)).eval x := by
  rw [basisValue, productLoop_correct, mul_one, Lagrange.basis, Polynomial.eval_prod]
  have erase_eq : (integerWindow start width).erase (start + slot) =
      (integerWindow start width).filter (fun integer => integer ≠ start + slot) := by
    ext integer
    simp only [Finset.mem_erase, Finset.mem_filter, and_comm]
  rw [erase_eq, Finset.prod_filter, product_window]
  apply Finset.prod_congr rfl
  intro other _
  by_cases same : other = slot
  · simp [same]
  · have different : start + (other : ℤ) ≠ start + (slot : ℤ) := by omega
    simp only [ite_eq_right same, ite_eq_left different, Lagrange.basisDivisor,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
      node, div_eq_mul_inv, mul_comm]

/-- Sum the Lagrange contributions through scalar slot counters. -/
def evaluate (start : ℤ) (width : ℕ) (x : ZMod p) : ZMod p :=
  sumLoop (fun slot => paritySign p (start + slot) * basisValue p start width slot x) width 0

/-- The scalar evaluator agrees with the actual polynomial used in the
finite-field deformation. This identity also holds for empty windows. -/
theorem evaluate_correct (start : ℤ) (width : ℕ) (x : ZMod p) :
    evaluate p start width x = (parityPolynomialMod p start width).eval x := by
  rw [evaluate, sumLoop_correct, add_zero, parityPolynomialMod, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, sum_window]
  apply Finset.sum_congr rfl
  intro slot _
  rw [Polynomial.eval_mul, Polynomial.eval_C, paritySign_correct, basisValue_correct]

theorem node_in_window (start : ℤ) (width : ℕ) (slot : Fin width) :
    start + (slot.val : ℤ) ∈ integerWindow start width := by
  rw [mem_integerWindow]
  have := slot.isLt
  constructor <;> omega

/-- Every denominator used by a non-diagonal loop slot is nonzero when the
integer window has width below the prime. The starting point is unrestricted. -/
theorem denominator_ne_zero (start : ℤ) (width : ℕ) (small : width < p)
    (slot other : Fin width) (different : other ≠ slot) :
    node p start slot.val - node p start other.val ≠ 0 := by
  apply sub_ne_zero.mpr
  intro same
  have same_integer := integerWindow_cast_injective p start width small
    (node_in_window start width slot) (node_in_window start width other) same
  apply different
  apply Fin.ext
  omega

theorem evaluate_at_node (start : ℤ) (width : ℕ) (small : width < p) (slot : Fin width) :
    evaluate p start width (node p start slot.val) = paritySign p (start + slot.val) := by
  rw [evaluate_correct, paritySign_correct]
  exact parityPolynomialMod_eval_int p start width small (start + slot.val)
    (node_in_window start width slot)

@[simp] theorem evaluate_zero_width (start : ℤ) (x : ZMod p) : evaluate p start 0 x = 0 := rfl

end NtimeDspace.ParityEvaluation
