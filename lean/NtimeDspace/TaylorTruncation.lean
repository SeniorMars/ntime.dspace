import NtimeDspace.BooleanMobius
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
Boolean truncation for an actual multivariate polynomial after scaling every
variable by `z`. This discharges the monomial-divisibility hypothesis for all
such polynomials, including products of clause factors with corrections whose
coefficients are divisible by `z`. It does not construct the spectral deformation
or assert an algorithmic space bound.
-/

namespace NtimeDspace.TaylorTruncation

open scoped BigOperators
open BooleanMobius

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

def scaledEval (P : MvPolynomial ι R) (z : R) (support : Finset ι) : R :=
  P.eval₂ (RingHom.id R) (fun i => if i ∈ support then z else 0)

omit [DecidableEq ι] in
theorem exponent_support_card_le (d : ι →₀ ℕ) :
    d.support.card ≤ ∑ i ∈ d.support, d i := by
  calc
    d.support.card = ∑ _i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

theorem scaled_monomial_eval (d : ι →₀ ℕ) (c z : R) (support : Finset ι) :
    c * (∏ i ∈ d.support, (if i ∈ support then z else 0) ^ d i) =
      booleanMonomial (c * z ^ (∑ i ∈ d.support, d i)) d.support support := by
  have hpower (i : ι) (hi : i ∈ d.support) :
      (if i ∈ support then z else 0) ^ d i =
        if i ∈ support then z ^ d i else 0 := by
    split_ifs <;> simp_all [Finsupp.mem_support_iff]
  rw [Finset.prod_congr rfl hpower, Finset.prod_ite_zero]
  simp only [← Finset.prod_pow_eq_pow_sum, booleanMonomial, Finset.subset_iff]
  split_ifs <;> simp

theorem scaledEval_monomial_sum (P : MvPolynomial ι R) (z : R) (support : Finset ι) :
    scaledEval P z support = ∑ d ∈ P.support,
      booleanMonomial (P.coeff d * z ^ (∑ i ∈ d.support, d i)) d.support support := by
  rw [scaledEval, MvPolynomial.eval₂_eq]
  apply Finset.sum_congr rfl
  intro d _
  exact scaled_monomial_eval d (P.coeff d) z support

/-- Every finite difference of a scaled polynomial contains one factor `z`
per selected variable, even when monomials have repeated variables. -/
theorem scaled_difference_dvd (P : MvPolynomial ι R) (z : R) (support : Finset ι) :
    z ^ support.card ∣ finiteDifference (scaledEval P z) support := by
  have heval : scaledEval P z = fun assigned => ∑ d ∈ P.support,
      booleanMonomial (P.coeff d * z ^ (∑ i ∈ d.support, d i)) d.support assigned := by
    funext assigned
    exact scaledEval_monomial_sum P z assigned
  rw [heval]
  apply finiteDifference_monomial_sum_dvd
  intro d _
  exact dvd_mul_of_dvd_right (pow_dvd_pow z (exponent_support_card_le d)) _

/-- The low-support Taylor congruence now follows for every multivariate
polynomial, without a separate hypothesis about its expanded monomials. -/
theorem scaled_polynomial_truncation (P : MvPolynomial ι R) (z : R)
    (order : ℕ) (support : Finset ι) :
    z ^ order ∣ scaledEval P z support -
      ∑ subset ∈ support.powerset.filter (fun subset => subset.card < order),
        finiteDifference (scaledEval P z) subset := by
  exact finiteDifference_truncation _ support z order
    (fun subset _ => scaled_difference_dvd P z subset)

/-- The untruncated Taylor-data sum, in the paper's loop order: support,
subsupport, then full assignments containing the support. -/
def taylorData (ground : Finset ι) (P : Finset ι → MvPolynomial ι R)
    (z : R) (order : ℕ) : R :=
  ∑ support ∈ ground.powerset.filter (fun support => support.card < order),
    ∑ subset ∈ support.powerset,
      (-1 : R) ^ (support.card - subset.card) *
        ∑ assigned ∈ ground.powerset,
          if support ⊆ assigned then scaledEval (P assigned) z subset else 0

theorem powerset_eq_filter {ground assigned : Finset ι} (included : assigned ⊆ ground) :
    assigned.powerset = ground.powerset.filter (fun support => support ⊆ assigned) := by
  ext support
  simp only [Finset.mem_powerset, Finset.mem_filter]
  exact ⟨fun h => ⟨h.trans included, h⟩, fun h => h.2⟩

/-- Reorders the actual finite Taylor-data sum. No per-assignment witness or
measurement value is counted more than once by this transformation. -/
theorem taylorData_eq_sum_differences (ground : Finset ι)
    (P : Finset ι → MvPolynomial ι R) (z : R) (order : ℕ) :
    taylorData ground P z order =
      ∑ assigned ∈ ground.powerset,
        ∑ support ∈ assigned.powerset.filter (fun support => support.card < order),
          finiteDifference (scaledEval (P assigned) z) support := by
  unfold taylorData
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext support
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro assigned hassigned
  rw [powerset_eq_filter (Finset.mem_powerset.mp hassigned), Finset.filter_filter]
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro support _
  by_cases small : support.card < order <;>
    by_cases included : support ⊆ assigned <;>
      simp [small, included, finiteDifference]

/-- Summing the fixed-assignment congruences gives the paper's Taylor-data
congruence for every family of scaled multivariate polynomials. -/
theorem taylorData_congruence (ground : Finset ι)
    (P : Finset ι → MvPolynomial ι R) (z : R) (order : ℕ) :
    z ^ order ∣ (∑ assigned ∈ ground.powerset, scaledEval (P assigned) z assigned) -
      taylorData ground P z order := by
  rw [taylorData_eq_sum_differences, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro assigned _
  exact scaled_polynomial_truncation (P assigned) z order assigned

end NtimeDspace.TaylorTruncation
