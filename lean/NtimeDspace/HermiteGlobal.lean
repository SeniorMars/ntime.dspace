import NtimeDspace.PolynomialFacts
import NtimeDspace.HermiteRecovery
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Global Hermite recovery

Polynomial reconstruction from the local reciprocal weights, with an explicit
degree argument. This development uses polynomials rather than Laurent series.
-/

namespace NtimeDspace.HermiteRecovery

open scoped BigOperators
open Polynomial

variable {K : Type*} [Field K]

noncomputable section

local instance hermiteGlobalDecidableEq : DecidableEq K := Classical.decEq K

/-- The polynomial vanishing to the prescribed order at every interpolation node. -/
noncomputable def nodeProduct (nodes : Finset K) (order : ℕ) : Polynomial K :=
  ∏ t ∈ nodes, (X - C t) ^ order

theorem nodeProduct_monic (nodes : Finset K) (order : ℕ) :
    (nodeProduct nodes order).Monic :=
  monic_prod_of_monic _ _ (fun t _ => (monic_X_sub_C t).pow order)

theorem nodeProduct_natDegree (nodes : Finset K) (order : ℕ) :
    (nodeProduct nodes order).natDegree = nodes.card * order := by
  unfold nodeProduct
  rw [natDegree_prod_of_monic _ _ (fun t _ => (monic_X_sub_C t).pow order)]
  simp

theorem nodeProduct_dvd (nodes : Finset K) (order : ℕ) (P : Polynomial K)
    (local_divisibility : ∀ t ∈ nodes, (X - C t) ^ order ∣ P) :
    nodeProduct nodes order ∣ P := by
  apply Finset.prod_dvd_of_coprime _ local_divisibility
  intro a ha b hb hab
  exact (isCoprime_X_sub_C_of_isUnit_sub
    (sub_ne_zero.mpr hab).isUnit).pow

theorem cofactor_degree (nodes : Finset K) (t : K) (order : ℕ)
    (member : t ∈ nodes) :
    (nodeProduct (nodes.erase t) order).natDegree = (nodes.card - 1) * order := by
  classical
  rw [nodeProduct_natDegree, Finset.card_erase_of_mem member]

theorem cofactor_divisible (nodes : Finset K) (a b : K) (order : ℕ)
    (member : a ∈ nodes) (different : a ≠ b) :
    (X - C a) ^ order ∣ nodeProduct (nodes.erase b) order := by
  classical
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨different, member⟩)

/-- Any polynomial divisible by a monic polynomial and having no larger degree
is exactly its top coefficient times that monic polynomial. -/
theorem eq_top_coeff_mul_of_monic_dvd (P D : Polynomial K) (monic : D.Monic)
    (divisibility : D ∣ P) (degree_bound : P.natDegree ≤ D.natDegree) :
    P = C (P.coeff D.natDegree) * D := by
  have h := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    monic divisibility degree_bound
  have hc := congrArg (fun Q : Polynomial K => Q.coeff D.natDegree) h
  change P.coeff D.natDegree = (C P.leadingCoeff * D).coeff D.natDegree at hc
  rw [coeff_C_mul, coeff_natDegree, monic.leadingCoeff, mul_one] at hc
  rwa [← hc] at h

/-- The polynomial part of Hermite recovery. Each local numerator has degree
below `order` and solves its own congruence. Pairwise coprimality and the global
degree bound force the stated constant term; no global recovery is assumed. -/
theorem recovery_of_local_numerators (nodes : Finset K) (order : ℕ)
    (positive : 0 < order) (H : Polynomial K) (B : K → Polynomial K)
    (H_degree : H.natDegree < nodes.card * order)
    (B_degree : ∀ t ∈ nodes, (B t).natDegree < order)
    (local_identity : ∀ t ∈ nodes,
      (X - C t) ^ order ∣ H - X * nodeProduct (nodes.erase t) order * B t) :
    H.eval 0 = -(nodeProduct nodes order).eval 0 *
      ∑ t ∈ nodes, (B t).coeff (order - 1) := by
  classical
  let S : Polynomial K := ∑ t ∈ nodes, X * nodeProduct (nodes.erase t) order * B t
  have hcard : 0 < nodes.card := by nlinarith [H.natDegree.zero_le]
  have hindex : 1 + (nodes.card - 1) * order + (order - 1) =
      nodes.card * order := by
    have hn := Nat.sub_add_cancel (Nat.one_le_of_lt hcard)
    have hj := Nat.sub_add_cancel (Nat.one_le_of_lt positive)
    have hn' := congrArg (fun n => n * order) hn
    simp only [Nat.add_mul, one_mul] at hn'
    omega
  have htermdegree (t : K) (ht : t ∈ nodes) :
      (X * nodeProduct (nodes.erase t) order * B t).natDegree ≤
        nodes.card * order := by
    have h₁ := natDegree_mul_le
      (p := (X : Polynomial K)) (q := nodeProduct (nodes.erase t) order)
    have h₂ := natDegree_mul_le
      (p := X * nodeProduct (nodes.erase t) order) (q := B t)
    rw [natDegree_X, cofactor_degree nodes t order ht] at h₁
    have hb := B_degree t ht
    omega
  have hSdegree : S.natDegree ≤ nodes.card * order :=
    natDegree_sum_le_of_forall_le _ _ htermdegree
  have hdiv : nodeProduct nodes order ∣ H - S := by
    apply nodeProduct_dvd
    intro t ht
    rw [show S = X * nodeProduct (nodes.erase t) order * B t +
      ∑ u ∈ nodes.erase t, X * nodeProduct (nodes.erase u) order * B u by
        dsimp [S]
        exact (Finset.add_sum_erase _ _ ht).symm]
    rw [sub_add_eq_sub_sub]
    apply dvd_sub (local_identity t ht)
    apply Finset.dvd_sum
    intro u hu
    have htu : t ≠ u := (Finset.mem_erase.mp hu).1.symm
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (cofactor_divisible nodes t u order ht htu) X) (B u)
  have hRdegree : (H - S).natDegree ≤ (nodeProduct nodes order).natDegree := by
    rw [nodeProduct_natDegree]
    simpa using natDegree_sub_le_of_le (Nat.le_of_lt H_degree) hSdegree
  have hR := eq_top_coeff_mul_of_monic_dvd (H - S) (nodeProduct nodes order)
    (nodeProduct_monic nodes order) hdiv hRdegree
  have htermcoeff (t : K) (ht : t ∈ nodes) :
      (X * nodeProduct (nodes.erase t) order * B t).coeff (nodes.card * order) =
        (B t).coeff (order - 1) := by
    rw [← hindex]
    rw [coeff_mul_add_eq_of_natDegree_le
      (show (X * nodeProduct (nodes.erase t) order).natDegree ≤
        1 + (nodes.card - 1) * order by
        simpa only [natDegree_X, cofactor_degree nodes t order ht]
          using (natDegree_mul_le (p := (X : Polynomial K))
            (q := nodeProduct (nodes.erase t) order)))
      (by have := B_degree t ht; omega)]
    have hm := (monic_X (R := K)).mul (nodeProduct_monic (nodes.erase t) order)
    have hd : (X * nodeProduct (nodes.erase t) order).natDegree =
        1 + (nodes.card - 1) * order := by
      rw [natDegree_mul (X_ne_zero) (nodeProduct_monic _ _).ne_zero,
        natDegree_X, cofactor_degree nodes t order ht]
    rw [← hd, coeff_natDegree, hm.leadingCoeff, one_mul]
  have hcoeff : (H - S).coeff (nodeProduct nodes order).natDegree =
      -(∑ t ∈ nodes, (B t).coeff (order - 1)) := by
    rw [nodeProduct_natDegree, coeff_sub, coeff_eq_zero_of_natDegree_lt H_degree,
      zero_sub]
    congr 1
    dsimp [S]
    rw [NtimeDspace.PolynomialFacts.coeff_finset_sum]
    exact Finset.sum_congr rfl htermcoeff
  rw [hcoeff] at hR
  have heval := congrArg (Polynomial.eval 0) hR
  have hSzero : S.eval 0 = 0 := by simp [S, NtimeDspace.PolynomialFacts.eval_finset_sum]
  simp only [eval_sub, eval_mul, eval_C, hSzero, sub_zero] at heval
  rw [heval]
  ring

/-- Shifting the complementary vanishing polynomial to a node produces exactly
the denominator used to define the paper's reciprocal weight. -/
theorem taylor_cofactor (nodes : Finset K) (t : K) (order : ℕ) :
    taylor t (X * nodeProduct (nodes.erase t) order) =
      nodeDenominator nodes t order := by
  have hX : (taylorAlgHom t) X = X + C t := taylor_X t
  have hC (u : K) : (taylorAlgHom t) (C u) = C u := taylor_C t u
  change (taylorAlgHom t) (X * nodeProduct (nodes.erase t) order) = _
  simp only [nodeProduct, map_mul, map_prod, map_pow, map_sub,
    hX, hC, nodeDenominator]
  simp only [sub_eq_add_neg, add_assoc]

/-- Translation preserves the coefficient at any upper degree bound. -/
theorem coeff_taylor_of_natDegree_le (P : Polynomial K) (t : K) (n : ℕ)
    (degree_bound : P.natDegree ≤ n) : (taylor t P).coeff n = P.coeff n := by
  rcases lt_or_eq_of_le degree_bound with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa using hlt),
      coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq, coeff_taylor_natDegree, coeff_natDegree]

/-- Full multi-node Hermite coefficient recovery with the explicitly constructed
truncated reciprocal weights. The input data may contain arbitrary higher terms;
only agreement with the Taylor expansion modulo `X^order` is required. -/
theorem multi_node_hermite_identity (nodes : Finset K) (order : ℕ)
    (positive : 0 < order) (nonzero_nodes : ∀ t ∈ nodes, t ≠ 0)
    (H : Polynomial K) (Y : K → Polynomial K)
    (H_degree : H.natDegree < nodes.card * order)
    (taylor_agreement : ∀ t ∈ nodes, X ^ order ∣ Y t - taylor t H) :
    H.eval 0 = -(nodeProduct nodes order).eval 0 *
      ∑ t ∈ nodes, (Y t * nodeWeight nodes t order).coeff (order - 1) := by
  classical
  let A : K → Polynomial K := fun t => PowerSeries.trunc order
    ((taylor t H * nodeWeight nodes t order : Polynomial K) : PowerSeries K)
  let B : K → Polynomial K := fun t => taylor (-t) (A t)
  have hAdegree (t : K) : (A t).natDegree < order := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    dsimp [A]
    rw [hn]
    exact PowerSeries.natDegree_trunc_lt _ n
  have hBdegree (t : K) (_ht : t ∈ nodes) : (B t).natDegree < order := by
    simpa only [B, natDegree_taylor] using hAdegree t
  have hlocal (t : K) (ht : t ∈ nodes) :
      (X - C t) ^ order ∣ H - X * nodeProduct (nodes.erase t) order * B t := by
    apply X_sub_C_pow_dvd_iff.mpr
    change X ^ order ∣ taylor t (H - X * nodeProduct (nodes.erase t) order * B t)
    rw [map_sub, taylor_mul, taylor_cofactor]
    dsimp only [B]
    rw [taylor_taylor, add_neg_cancel, taylor_zero]
    apply dvd_sub_comm.mpr
    exact local_inverse_product_trunc (nodeDenominator nodes t order) (taylor t H)
      (nodeDenominator_constant_ne_zero nodes t (nonzero_nodes t ht) order) order
  rw [recovery_of_local_numerators nodes order positive H B H_degree hBdegree hlocal]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only [B]
  rw [coeff_taylor_of_natDegree_le _ _ _ (by have := hAdegree t; omega)]
  dsimp only [A]
  rw [PowerSeries.coeff_trunc, if_pos (by omega), coeff_coe]
  exact (coeff_mul_eq_of_X_pow_dvd_sub (Y t) (taylor t H)
    (nodeWeight nodes t order) order (order - 1) (by omega)
      (taylor_agreement t ht)).symm

/-- The algebraic identity in the paper's scalar Hermite lemma for any finite
set of distinct nonzero field nodes. Both the reciprocal weights and the global
Hermite identity are proved, rather than supplied as assumptions. The remaining
algorithmic resource claim in that lemma is outside this algebraic theorem. -/
theorem multi_node_scalar_recovery {p : ℕ} [Fact p.Prime]
    (nodes : Finset (ZMod p)) (order : ℕ)
    (positive : 0 < order) (below_prime : order < p)
    (nonzero_nodes : ∀ t ∈ nodes, t ≠ 0)
    (H : Polynomial (ZMod p)) (Y : ZMod p → Polynomial (ZMod p))
    (H_degree : H.natDegree < nodes.card * order)
    (Y_degree : ∀ t ∈ nodes, (Y t).natDegree ≤ p - 2)
    (taylor_agreement : ∀ t ∈ nodes, X ^ order ∣ Y t - taylor t H) :
    H.eval 0 = (nodeProduct nodes order).eval 0 *
      ∑ t ∈ nodes, ∑ z : (ZMod p)ˣ,
        (z : ZMod p) ^ (p - order) *
          (nodeWeight nodes t order).eval (z : ZMod p) * (Y t).eval (z : ZMod p) := by
  rw [multi_node_hermite_identity nodes order positive nonzero_nodes H Y
    H_degree taylor_agreement]
  have hsum : (∑ t ∈ nodes, (Y t * nodeWeight nodes t order).coeff (order - 1)) =
      -(∑ t ∈ nodes, ∑ z : (ZMod p)ˣ,
        (z : ZMod p) ^ (p - order) *
          (nodeWeight nodes t order).eval (z : ZMod p) * (Y t).eval (z : ZMod p)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    exact NtimeDspace.weighted_taylor_projector (Y t) (nodeWeight nodes t order)
      order positive below_prime (Y_degree t ht)
        (nodeWeight_degree_lt nodes t order positive)
  rw [hsum, neg_mul_neg]

end

end NtimeDspace.HermiteRecovery
