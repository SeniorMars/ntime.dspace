import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
On-demand coefficient computation for a product, used in Lemma `lem:scalar`.
The input is a binary product tree. Only coefficients up to the requested degree
are queried. Proving that a balanced tree is constructed in small space, and
compiling the recursion to a bounded-workspace machine, remain obligations.
-/

namespace NtimeDspace

open scoped BigOperators

inductive CoefficientTree (R : Type*) where
  | leaf : (ℕ → R) → CoefficientTree R
  | branch : CoefficientTree R → CoefficientTree R → CoefficientTree R

/-- A scalar accumulator for a finite sum. It builds no list of summands. -/
def sumLoop {R : Type*} [AddMonoid R] (term : ℕ → R) : ℕ → R → R
  | 0, acc => acc
  | n + 1, acc => sumLoop term n (term n + acc)

theorem sumLoop_correct {R : Type*} [AddCommMonoid R]
    (term : ℕ → R) (n : ℕ) (acc : R) :
    sumLoop term n acc = (∑ i ∈ Finset.range n, term i) + acc := by
  induction n generalizing acc with
  | zero => simp [sumLoop]
  | succ n ih => simp [sumLoop, ih, Finset.sum_range_succ, add_assoc]

/-- Convolution queries one requested coefficient recursively. This is an
arithmetic procedure, not yet a CSLib machine or a machine-space theorem. -/
def CoefficientTree.coefficient {R : Type*} [Semiring R] : CoefficientTree R → ℕ → R
  | .leaf coefficient, m => coefficient m
  | .branch left right, m =>
      sumLoop (fun i => left.coefficient i * right.coefficient (m - i)) (m + 1) 0

/-- Relate the arithmetic oracle tree to a polynomial, without storing the
product polynomial as part of the coefficient procedure. -/
inductive CoefficientTree.Represents {R : Type*} [Semiring R] :
    CoefficientTree R → Polynomial R → Prop where
  | leaf (P : Polynomial R) : Represents (.leaf P.coeff) P
  | branch {left right : CoefficientTree R} {P Q : Polynomial R} :
      Represents left P → Represents right Q → Represents (.branch left right) (P * Q)

theorem CoefficientTree.coefficient_correct {R : Type*} [Semiring R]
    {tree : CoefficientTree R} {P : Polynomial R}
    (h : tree.Represents P) (m : ℕ) : tree.coefficient m = P.coeff m := by
  induction h generalizing m with
  | leaf P => rfl
  | @branch left right P Q hP hQ ihP ihQ =>
      simp only [CoefficientTree.coefficient, sumLoop_correct, add_zero, ihP, ihQ]
      rw [Polynomial.coeff_mul]
      exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => P.coeff i * Q.coeff j) m).symm

/-- For truncated reciprocal series, only coefficients below the order need
agree with the representing polynomial. No full polynomial oracle is required. -/
inductive CoefficientTree.RepresentsBelow {R : Type*} [Semiring R] (order : ℕ) :
    CoefficientTree R → Polynomial R → Prop where
  | leaf (oracle : ℕ → R) (P : Polynomial R)
      (agree : ∀ m < order, oracle m = P.coeff m) :
      RepresentsBelow order (.leaf oracle) P
  | branch {left right : CoefficientTree R} {P Q : Polynomial R} :
      RepresentsBelow order left P → RepresentsBelow order right Q →
      RepresentsBelow order (.branch left right) (P * Q)

theorem CoefficientTree.coefficient_correct_below {R : Type*} [Semiring R]
    {tree : CoefficientTree R} {P : Polynomial R} {order : ℕ}
    (h : tree.RepresentsBelow order P) (m : ℕ) (hm : m < order) :
    tree.coefficient m = P.coeff m := by
  induction h generalizing m with
  | leaf oracle P agree => exact agree m hm
  | @branch left right P Q hP hQ ihP ihQ =>
      simp only [CoefficientTree.coefficient, sumLoop_correct, add_zero]
      rw [Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j) m]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [ihP i (by omega), ihQ (m - i) (by omega)]

end NtimeDspace
