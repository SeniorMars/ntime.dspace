import NtimeDspace.IntervalCoefficients

/-!
# Hermite coefficients as sums over digit tuples

`IntervalCoefficients.allCoefficient` computes a coefficient of the inverse of a
product of `count` factors by a divide-and-conquer recursion whose depth grows
with the input. A loop program cannot unroll such a recursion. Here the same
coefficient is a sum over digit tuples `f : Fin count → Fin J` with
`∑ f i = index` of products of single-factor coefficients. Enumerating the
tuples as the numbers below `J ^ count` takes `count · log J` bits.
-/

namespace NtimeDspace.HermiteTuple

open PowerSeries

variable {R : Type*} [CommRing R]

/-- Truncations multiply below the truncation order. -/
theorem trunc_prod_trunc {ι : Type*} (s : Finset ι) (f : ι → PowerSeries R) (n : ℕ) :
    trunc n (∏ i ∈ s, (trunc n (f i) : PowerSeries R)) = trunc n (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, trunc_trunc_mul, ← trunc_mul_trunc, ih,
      trunc_mul_trunc]

theorem prod_monomial_poly {ι : Type*} (s : Finset ι) (f : ι → ℕ) (g : ι → R) :
    ∏ i ∈ s, Polynomial.monomial (f i) (g i) =
      Polynomial.monomial (∑ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Polynomial.monomial_mul_monomial, Finset.sum_insert ha,
      Finset.prod_insert ha]

/-- The coefficient of a product of truncated sums is a sum over digit tuples. -/
theorem tuple_coeff (count J index : ℕ) (c : Fin count → ℕ → R) :
    (∏ i : Fin count, ∑ d ∈ Finset.range J, Polynomial.monomial d (c i d)).coeff index =
      ∑ f : Fin count → Fin J,
        if ∑ i, (f i : ℕ) = index then ∏ i, c i (f i) else 0 := by
  classical
  have hsum (i : Fin count) : ∑ d ∈ Finset.range J, Polynomial.monomial d (c i d) =
      ∑ d : Fin J, Polynomial.monomial (d : ℕ) (c i d) :=
    (Fin.sum_univ_eq_sum_range (fun d => Polynomial.monomial d (c i d)) J).symm
  simp only [hsum]
  rw [Finset.prod_univ_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [prod_monomial_poly, Polynomial.coeff_monomial]

omit [CommRing R] in
theorem coe_prod' {S : Type*} [CommRing S] {ι : Type*} (s : Finset ι) (f : ι → Polynomial S) :
    ((∏ i ∈ s, f i : Polynomial S) : PowerSeries S) = ∏ i ∈ s, (f i : PowerSeries S) := by
  have := map_prod (Polynomial.coeToPowerSeries.ringHom (R := S)) f s
  simp only [Polynomial.coeToPowerSeries.ringHom_apply] at this
  exact this

variable {p : ℕ} [Fact p.Prime]

theorem inv_prod {ι : Type*} (s : Finset ι) (φ : ι → PowerSeries (ZMod p)) :
    (∏ i ∈ s, φ i)⁻¹ = ∏ i ∈ s, (φ i)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, PowerSeries.mul_inv_rev, ih, mul_comm]

theorem trunc_eq_sum (φ : PowerSeries R) (J : ℕ) :
    trunc J φ = ∑ d ∈ Finset.range J, Polynomial.monomial d (coeff d φ) := by
  ext m
  rw [coeff_trunc, Polynomial.finsetSum_coeff]
  by_cases hm : m < J
  · rw [if_pos hm, Finset.sum_eq_single m]
    · simp
    · intro d _ hd; rw [Polynomial.coeff_monomial, if_neg hd]
    · intro hm'; exact absurd (Finset.mem_range.mpr hm) hm'
  · rw [if_neg hm]
    symm
    refine Finset.sum_eq_zero fun d hd => ?_
    have : d ≠ m := fun h => hm (h ▸ Finset.mem_range.mp hd)
    rw [Polynomial.coeff_monomial, if_neg this]

/-- **Hermite coefficients as digit-tuple sums.** -/
theorem allCoefficient_eq_tuple (factor : IntervalCoefficients.Factors p) (count : ℕ)
    (valid : IntervalCoefficients.Valid factor count) (J index : ℕ) (below : index < J)
    (within : J ≤ p) :
    IntervalCoefficients.allCoefficient factor count index =
      ∑ f : Fin count → Fin J, if ∑ i, (f i : ℕ) = index then
        ∏ i : Fin count, HermiteRecovery.modularReciprocalCoefficient (factor i).1 (factor i).2 (f i) else 0 := by
  classical
  rw [IntervalCoefficients.allCoefficient_correct factor count valid index (below.trans_le within)]
  set F : Fin count → PowerSeries (ZMod p) := fun i =>
    ((((Polynomial.X + Polynomial.C (factor i).1) ^ (factor i).2 : Polynomial (ZMod p)) :
      PowerSeries (ZMod p)))⁻¹
  have hprod : ((∏ slot ∈ Finset.range count,
      (Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2 : Polynomial (ZMod p)) :
        PowerSeries (ZMod p))⁻¹ = ∏ i : Fin count, F i := by
    rw [coe_prod', inv_prod, ← Fin.prod_univ_eq_prod_range
      (fun slot => ((((Polynomial.X + Polynomial.C (factor slot).1) ^ (factor slot).2 :
        Polynomial (ZMod p)) : PowerSeries (ZMod p)))⁻¹) count]
  rw [hprod]
  have htrunc : coeff index (∏ i : Fin count, F i) =
      (∏ i : Fin count, ∑ d ∈ Finset.range J, Polynomial.monomial d (coeff d (F i))).coeff
        index := by
    have h1 : coeff index (∏ i : Fin count, F i) =
        (trunc J (∏ i : Fin count, F i)).coeff index := by
      rw [coeff_trunc, if_pos below]
    rw [h1, ← trunc_prod_trunc, coeff_trunc, if_pos below]
    simp only [trunc_eq_sum]
    rw [← Polynomial.coeff_coe]
    simp only [coe_prod']
  rw [htrunc, tuple_coeff]
  refine Finset.sum_congr rfl fun f _ => ?_
  split_ifs with hf
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (f i : ℕ) < p := (f i).isLt.trans_le within
    rw [HermiteRecovery.modularReciprocalCoefficient_correct (factor i).1 (valid i i.isLt).1 (factor i).2 (f i)
      (valid i i.isLt).2 hi]
    simp only [F, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C,
      add_comm]
  · rfl

end NtimeDspace.HermiteTuple
