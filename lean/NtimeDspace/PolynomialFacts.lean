import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff

/-! Small polynomial facts with names stable across both checked Mathlib pins. -/

namespace NtimeDspace.PolynomialFacts

open scoped BigOperators

theorem eval_finset_sum {K I : Type*} [CommSemiring K]
    (s : Finset I) (g : I → Polynomial K) (x : K) :
    (∑ i ∈ s, g i).eval x = ∑ i ∈ s, (g i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, Polynomial.eval_add, ih]

theorem coeff_finset_sum {K I : Type*} [Semiring K]
    (s : Finset I) (g : I → Polynomial K) (n : ℕ) :
    (∑ i ∈ s, g i).coeff n = ∑ i ∈ s, (g i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, Polynomial.coeff_add, ih]

end NtimeDspace.PolynomialFacts
