import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic

/-!
# Boolean finite differences

This is the Boolean-lattice inversion used in the manuscript's derivation of
Fact `taylor`. A finite set is the support of a Boolean assignment, and
`finiteDifference f E` is the alternating sum of `f` over subsets of `E`.

The reconstruction theorem is exact over an arbitrary commutative ring.
The truncation result proves divisibility by `z^J` when the coefficient of
each monomial is divisible by `z` to the cardinality of its variable support.
For the manuscript one takes the ring to be a polynomial ring and `z = X`.
`TaylorTruncation.lean` discharges this divisibility for arbitrary scaled
multivariate polynomials; `DeformationTaylor.lean` instantiates linear corrections.
-/

namespace NtimeDspace.BooleanMobius

open scoped BigOperators

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- The mixed finite difference at the all-zero assignment. -/
def finiteDifference (f : Finset ι → R) (support : Finset ι) : R :=
  ∑ subset ∈ support.powerset, (-1 : R) ^ (support.card - subset.card) * f subset

omit [DecidableEq ι] in
@[simp] theorem finiteDifference_empty (f : Finset ι → R) :
    finiteDifference f ∅ = f ∅ := by
  simp [finiteDifference]

/-- Adjoining a fresh variable subtracts the value with that variable absent
from the value with it present. -/
theorem finiteDifference_insert (f : Finset ι → R) (support : Finset ι)
    (index : ι) (fresh : index ∉ support) :
    finiteDifference f (insert index support) =
      finiteDifference (fun subset => f (insert index subset)) support -
        finiteDifference f support := by
  unfold finiteDifference
  rw [Finset.sum_powerset_insert fresh, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro subset hsubset
  have hle := Finset.card_le_card (Finset.mem_powerset.mp hsubset)
  have hfresh : index ∉ subset :=
    fun h => fresh (Finset.mem_powerset.mp hsubset h)
  have hexponent : (insert index support).card - subset.card =
      (support.card - subset.card) + 1 := by
    rw [Finset.card_insert_of_notMem fresh]
    omega
  rw [hexponent]
  simp only [Finset.card_insert_of_notMem fresh,
    Finset.card_insert_of_notMem hfresh, Nat.add_sub_add_right, pow_succ]
  ring

/-- Boolean Möbius inversion: summing all finite differences reconstructs the
value on the indicated Boolean support. -/
theorem finiteDifference_reconstruction (f : Finset ι → R) (support : Finset ι) :
    (∑ subset ∈ support.powerset, finiteDifference f subset) = f support := by
  induction support using Finset.induction_on generalizing f with
  | empty => simp
  | @insert index support fresh ih =>
      rw [Finset.sum_powerset_insert fresh, ih]
      have hrecurrence (subset : Finset ι) (hsubset : subset ∈ support.powerset) :
          finiteDifference f (insert index subset) =
            finiteDifference (fun t => f (insert index t)) subset -
              finiteDifference f subset :=
        finiteDifference_insert f subset index
          (fun h => fresh (Finset.mem_powerset.mp hsubset h))
      simp_rw [Finset.sum_congr rfl hrecurrence]
      rw [Finset.sum_sub_distrib, ih, ih]
      ring

omit [DecidableEq ι] in
/-- Only the values on subsets of the selected support affect a difference. -/
theorem finiteDifference_congr {f g : Finset ι → R} (support : Finset ι)
    (agree : ∀ subset ⊆ support, f subset = g subset) :
    finiteDifference f support = finiteDifference g support := by
  apply Finset.sum_congr rfl
  intro subset hsubset
  rw [agree subset (Finset.mem_powerset.mp hsubset)]

/-- A finite difference vanishes if one of its selected variables is irrelevant. -/
theorem finiteDifference_eq_zero_of_irrelevant (f : Finset ι → R)
    (support : Finset ι) (index : ι) (selected : index ∈ support)
    (irrelevant : ∀ subset ⊆ support.erase index, f (insert index subset) = f subset) :
    finiteDifference f support = 0 := by
  calc
    finiteDifference f support = finiteDifference f (insert index (support.erase index)) := by
      rw [Finset.insert_erase selected]
    _ = finiteDifference (fun subset => f (insert index subset)) (support.erase index) -
        finiteDifference f (support.erase index) :=
      finiteDifference_insert f (support.erase index) index (Finset.notMem_erase _ _)
    _ = 0 := by
      rw [finiteDifference_congr (support.erase index) irrelevant, sub_self]

/-- A monomial on Boolean inputs is its coefficient precisely when every
variable in its support is assigned one. Positive exponents do not matter. -/
def booleanMonomial (coefficient : R) (monomialSupport : Finset ι)
    (assignmentSupport : Finset ι) : R :=
  if monomialSupport ⊆ assignmentSupport then coefficient else 0

/-- A Boolean finite difference selects exactly one monomial support. -/
theorem finiteDifference_booleanMonomial (coefficient : R)
    (monomialSupport support : Finset ι) :
    finiteDifference (booleanMonomial coefficient monomialSupport) support =
      if monomialSupport = support then coefficient else 0 := by
  by_cases equal : monomialSupport = support
  · subst monomialSupport
    simp only [ite_true]
    unfold finiteDifference booleanMonomial
    rw [Finset.sum_eq_single support]
    · simp
    · intro subset hsubset hne
      have hnot : ¬ support ⊆ subset := by
        intro h
        exact hne (Finset.Subset.antisymm (Finset.mem_powerset.mp hsubset) h)
      simp [hnot]
    · simp
  · rw [if_neg equal]
    by_cases included : monomialSupport ⊆ support
    · obtain ⟨index, selected, absent⟩ := Finset.exists_of_ssubset
        (Finset.ssubset_iff_subset_ne.mpr ⟨included, equal⟩)
      apply finiteDifference_eq_zero_of_irrelevant _ support index selected
      intro subset _
      simp only [booleanMonomial, Finset.subset_insert_iff_of_notMem absent]
    · unfold finiteDifference
      apply Finset.sum_eq_zero
      intro subset hsubset
      have hnot : ¬ monomialSupport ⊆ subset :=
        fun h => included (Finset.Subset.trans h (Finset.mem_powerset.mp hsubset))
      simp [booleanMonomial, hnot]

omit [DecidableEq ι] in
/-- Finite differences commute with finite sums. -/
theorem finiteDifference_sum {Term : Type*} (terms : Finset Term)
    (f : Term → Finset ι → R) (support : Finset ι) :
    finiteDifference (fun subset => ∑ term ∈ terms, f term subset) support =
      ∑ term ∈ terms, finiteDifference (f term) support := by
  unfold finiteDifference
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- If every finite difference has the indicated divisibility, discarding
supports of cardinality at least `order` preserves the result modulo `z^order`. -/
theorem finiteDifference_truncation (f : Finset ι → R) (support : Finset ι)
    (z : R) (order : ℕ)
    (divisible : ∀ subset ⊆ support, z ^ subset.card ∣ finiteDifference f subset) :
    z ^ order ∣ f support -
      ∑ subset ∈ support.powerset.filter (fun subset => subset.card < order),
        finiteDifference f subset := by
  have hsplit := Finset.sum_filter_add_sum_filter_not support.powerset
    (fun subset : Finset ι => subset.card < order) (finiteDifference f)
  rw [finiteDifference_reconstruction] at hsplit
  have hremainder : f support -
      ∑ subset ∈ support.powerset.filter (fun subset => subset.card < order),
        finiteDifference f subset =
      ∑ subset ∈ support.powerset.filter (fun subset => ¬ subset.card < order),
        finiteDifference f subset := by
    rw [← hsplit]
    ring
  rw [hremainder]
  apply Finset.dvd_sum
  intro subset hsubset
  obtain ⟨hin, hlarge⟩ := Finset.mem_filter.mp hsubset
  exact (pow_dvd_pow z (Nat.le_of_not_gt hlarge)).trans
    (divisible subset (Finset.mem_powerset.mp hin))

/-- Monomial support selection transfers coefficient divisibility to every
finite difference. Repeated supports and arbitrary finite term indexing are allowed. -/
theorem finiteDifference_monomial_sum_dvd {Term : Type*} (terms : Finset Term)
    (coefficient : Term → R) (monomialSupport : Term → Finset ι) (z : R)
    (coefficient_divisible : ∀ term ∈ terms,
      z ^ (monomialSupport term).card ∣ coefficient term)
    (support : Finset ι) :
    z ^ support.card ∣
      finiteDifference
        (fun subset => ∑ term ∈ terms,
          booleanMonomial (coefficient term) (monomialSupport term) subset) support := by
  rw [finiteDifference_sum]
  apply Finset.dvd_sum
  intro term hterm
  rw [finiteDifference_booleanMonomial]
  by_cases hequal : monomialSupport term = support
  · rw [if_pos hequal]
    simpa [hequal] using coefficient_divisible term hterm
  · rw [if_neg hequal]
    exact dvd_zero _

/-- The low-support truncation principle used by the Taylor-data argument.
For polynomial coefficients, choosing `z = Polynomial.X` gives equality modulo
`X^order`. The hypothesis is local to each monomial coefficient. -/
theorem boolean_monomial_truncation {Term : Type*} (terms : Finset Term)
    (coefficient : Term → R) (monomialSupport : Term → Finset ι)
    (z : R) (order : ℕ)
    (coefficient_divisible : ∀ term ∈ terms,
      z ^ (monomialSupport term).card ∣ coefficient term)
    (support : Finset ι) :
    z ^ order ∣
      (∑ term ∈ terms, booleanMonomial (coefficient term) (monomialSupport term) support) -
      ∑ subset ∈ support.powerset.filter (fun subset => subset.card < order),
        finiteDifference
          (fun assigned => ∑ term ∈ terms,
            booleanMonomial (coefficient term) (monomialSupport term) assigned) subset := by
  refine finiteDifference_truncation
    (fun assigned => ∑ term ∈ terms,
      booleanMonomial (coefficient term) (monomialSupport term) assigned)
    support z order ?_
  intro subset _
  exact finiteDifference_monomial_sum_dvd terms coefficient monomialSupport z
    coefficient_divisible subset

end NtimeDspace.BooleanMobius
