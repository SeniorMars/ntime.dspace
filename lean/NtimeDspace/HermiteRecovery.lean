import NtimeDspace.ScalarRecovery
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-!
# Truncated reciprocal weights and single-node Hermite recovery

The reciprocal is the actual formal-power-series inverse, truncated to a
polynomial. No Hermite identity is assumed. These results address the scalar
recovery lemma's single-node case and reusable local coefficient calculations.
The multiple-node identity is proved in `HermiteGlobal.lean` using these local
calculations.
-/

namespace NtimeDspace.HermiteRecovery

open scoped BigOperators

variable {K : Type*} [Field K]

/-- The single-node weight from the manuscript, with `t ≠ 0` required by the
correctness theorems rather than hidden in the definition. -/
noncomputable def reciprocalWeight (t : K) (order : ℕ) : Polynomial K :=
  PowerSeries.trunc order ((PowerSeries.C t + PowerSeries.X : PowerSeries K)⁻¹)

theorem reciprocalWeight_degree_lt (t : K) (order : ℕ) (positive : 0 < order) :
    (reciprocalWeight t order).natDegree < order := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  exact PowerSeries.natDegree_trunc_lt _ n

/-- Truncating a reciprocal preserves its inverse identity through the retained order. -/
theorem reciprocalWeight_inverse (t : K) (nonzero : t ≠ 0) (order : ℕ) :
    PowerSeries.trunc order
      ((PowerSeries.C t + PowerSeries.X) *
        (reciprocalWeight t order : PowerSeries K)) =
      PowerSeries.trunc order (1 : PowerSeries K) := by
  rw [reciprocalWeight, PowerSeries.trunc_mul_trunc,
    PowerSeries.mul_inv_cancel _ (by simpa using nonzero)]

/-- A product coefficient below the cutoff is unchanged by truncating its
power-series factor. -/
theorem coeff_mul_trunc_right (P : Polynomial K) (series : PowerSeries K)
    (order index : ℕ) (below : index < order) :
    (P * PowerSeries.trunc order series).coeff index =
      PowerSeries.coeff index ((P : PowerSeries K) * series) := by
  rw [Polynomial.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hsnd : pair.2 < order := by
    have hsum := Finset.mem_antidiagonal.mp hpair
    omega
  rw [PowerSeries.coeff_trunc,
    if_pos hsnd,
    Polynomial.coeff_coe]

/-- The truncated reciprocal of a polynomial with nonzero constant coefficient. -/
noncomputable def truncatedInverse (denominator : Polynomial K) (order : ℕ) : Polynomial K :=
  PowerSeries.trunc order ((denominator : PowerSeries K)⁻¹)

theorem truncatedInverse_degree_lt (denominator : Polynomial K) (order : ℕ)
    (positive : 0 < order) :
    (truncatedInverse denominator order).natDegree < order := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  exact PowerSeries.natDegree_trunc_lt _ n

/-- The concrete truncated reciprocal solves the polynomial inverse problem
modulo `X^order`; no inverse coefficient is assumed. -/
theorem truncatedInverse_correct (denominator : Polynomial K)
    (nonzero_constant : denominator.coeff 0 ≠ 0) (order : ℕ) :
    Polynomial.X ^ order ∣ denominator * truncatedInverse denominator order - 1 := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro index below
  rw [Polynomial.coeff_sub, truncatedInverse, coeff_mul_trunc_right _ _ _ _ below,
    PowerSeries.mul_inv_cancel _ (by simpa only [Polynomial.constantCoeff_coe]
      using nonzero_constant)]
  simp [PowerSeries.coeff_one, Polynomial.coeff_one]

/-- Multiplying a polynomial by the concrete reciprocal and truncating gives
the local numerator used in Hermite interpolation. It solves the corresponding
local congruence even when the polynomial itself has arbitrarily high degree. -/
theorem local_inverse_product_trunc (denominator P : Polynomial K)
    (nonzero_constant : denominator.coeff 0 ≠ 0) (order : ℕ) :
    Polynomial.X ^ order ∣
      denominator * PowerSeries.trunc order
        ((P * truncatedInverse denominator order : Polynomial K) : PowerSeries K) - P := by
  have hdiv : Polynomial.X ^ order ∣
      denominator * (P * truncatedInverse denominator order) - P := by
    have h := dvd_mul_of_dvd_left
      (truncatedInverse_correct denominator nonzero_constant order) P
    convert h using 1
    ring
  apply Polynomial.X_pow_dvd_iff.mpr
  intro index below
  rw [Polynomial.coeff_sub, coeff_mul_trunc_right _ _ _ _ below,
    ← Polynomial.coe_mul, Polynomial.coeff_coe]
  have hzero := Polynomial.X_pow_dvd_iff.mp hdiv index below
  simpa only [Polynomial.coeff_sub] using hzero

/-- The denominator defining the paper's weight at a node. Nodes are field
elements in a finite set, so distinct nodes are genuinely distinct in the field. -/
noncomputable def nodeDenominator (nodes : Finset K) (node : K) (order : ℕ) : Polynomial K := by
  classical
  exact (Polynomial.X + Polynomial.C node) *
    ∏ other ∈ nodes.erase node,
      (Polynomial.X + Polynomial.C (node - other)) ^ order

/-- Every denominator in the actual reciprocal weight has invertible constant
coefficient at a nonzero node. -/
theorem nodeDenominator_constant_ne_zero (nodes : Finset K) (node : K)
    (nonzero_node : node ≠ 0) (order : ℕ) :
    (nodeDenominator nodes node order).coeff 0 ≠ 0 := by
  classical
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [nodeDenominator, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, zero_add, Polynomial.eval_prod,
    Polynomial.eval_pow]
  apply mul_ne_zero nonzero_node
  apply Finset.prod_ne_zero_iff.mpr
  intro other hother
  exact pow_ne_zero order (sub_ne_zero.mpr (Finset.mem_erase.mp hother).1.symm)

/-- The concrete multiple-node truncated reciprocal weight. The reciprocal
denominator is exactly `(node+X) ∏ (node-other+X)^order`. -/
noncomputable def nodeWeight (nodes : Finset K) (node : K) (order : ℕ) : Polynomial K :=
  truncatedInverse (nodeDenominator nodes node order) order

theorem nodeWeight_singleton (node : K) (order : ℕ) :
    nodeWeight {node} node order = reciprocalWeight node order := by
  classical
  simp [nodeWeight, nodeDenominator, truncatedInverse, reciprocalWeight,
    Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, add_comm]

theorem nodeWeight_degree_lt (nodes : Finset K) (node : K) (order : ℕ)
    (positive : 0 < order) : (nodeWeight nodes node order).natDegree < order :=
  truncatedInverse_degree_lt _ order positive

/-- Concrete weights satisfy the required local inverse congruence, also for
multiple interpolation nodes. The global coefficient-recovery sum is separate. -/
theorem nodeWeight_inverse_mod (nodes : Finset K) (node : K)
    (nonzero_node : node ≠ 0) (order : ℕ) :
    Polynomial.X ^ order ∣
      nodeDenominator nodes node order * nodeWeight nodes node order - 1 :=
  truncatedInverse_correct _ (nodeDenominator_constant_ne_zero nodes node nonzero_node order) order

/-- Multiplying a degree-`n` polynomial by a linear factor leaves just one term
above its truncation at order `n+1`. -/
theorem linear_factor_trunc_remainder (B : Polynomial K) (t : K) (n : ℕ)
    (degree_bound : B.natDegree ≤ n) :
    (Polynomial.X + Polynomial.C t) * B =
      PowerSeries.trunc (n + 1)
        (((Polynomial.X + Polynomial.C t) * B : Polynomial K) : PowerSeries K) +
        Polynomial.C (B.coeff n) * Polynomial.X ^ (n + 1) := by
  have hdegree : ((Polynomial.X + Polynomial.C t) * B).natDegree ≤ n + 1 := by
    have h := Polynomial.natDegree_mul_le
      (p := Polynomial.X + Polynomial.C t) (q := B)
    rw [Polynomial.natDegree_X_add_C] at h
    omega
  ext index
  rw [Polynomial.coeff_add, PowerSeries.coeff_trunc, Polynomial.coeff_coe,
    Polynomial.coeff_C_mul_X_pow]
  by_cases hbelow : index < n + 1
  · simp [hbelow, Nat.ne_of_lt hbelow]
  · by_cases hequal : index = n + 1
    · subst index
      have hBzero : B.coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [add_mul, Polynomial.coeff_X_mul, hBzero]
    · have habove : n + 1 < index := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree habove)]
      simp [hbelow, hequal]

/-- Recover a polynomial's value at `-t` from one coefficient after division by
`t+X`. The degree restriction makes the top discarded term the only remainder. -/
theorem single_node_polynomial_recovery (P : Polynomial K) (t : K)
    (nonzero : t ≠ 0) (n : ℕ) (degree_bound : P.natDegree < n + 1) :
    P.eval (-t) = -(-t) ^ (n + 1) *
      (P * reciprocalWeight t (n + 1)).coeff n := by
  let series : PowerSeries K :=
    (P : PowerSeries K) * (PowerSeries.C t + PowerSeries.X)⁻¹
  let B : Polynomial K := PowerSeries.trunc (n + 1) series
  have hBdegree : B.natDegree ≤ n :=
    Nat.le_of_lt_succ (PowerSeries.natDegree_trunc_lt series n)
  have htrunc : PowerSeries.trunc (n + 1)
      (((Polynomial.X + Polynomial.C t) * B : Polynomial K) : PowerSeries K) = P := by
    simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C]
    change PowerSeries.trunc (n + 1)
      ((PowerSeries.X + PowerSeries.C t) *
        (PowerSeries.trunc (n + 1) series : PowerSeries K)) = P
    rw [PowerSeries.trunc_mul_trunc]
    have hcancel : (PowerSeries.X + PowerSeries.C t) * series = (P : PowerSeries K) := by
      dsimp [series]
      calc
        _ = (P : PowerSeries K) *
            ((PowerSeries.C t + PowerSeries.X) *
              (PowerSeries.C t + PowerSeries.X)⁻¹) := by ring
        _ = (P : PowerSeries K) := by
          rw [PowerSeries.mul_inv_cancel _ (by simpa using nonzero), mul_one]
    rw [hcancel, PowerSeries.trunc_coe_eq_self degree_bound]
  have hpolynomial := linear_factor_trunc_remainder B t n hBdegree
  rw [htrunc] at hpolynomial
  have heval := congrArg (Polynomial.eval (-t)) hpolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, neg_add_cancel, zero_mul] at heval
  have hcoeff : B.coeff n = (P * reciprocalWeight t (n + 1)).coeff n := by
    rw [reciprocalWeight, coeff_mul_trunc_right _ _ _ _ (Nat.lt_succ_self n)]
    simp [B, series, PowerSeries.coeff_trunc]
  rw [← hcoeff]
  linear_combination -heval

/-- Multiplying by any polynomial preserves agreement of coefficients below a
given power of `X`. This allows the untruncated `Y` in the paper. -/
theorem coeff_mul_eq_of_X_pow_dvd_sub (Y P G : Polynomial K)
    (order index : ℕ) (below : index < order)
    (agreement : Polynomial.X ^ order ∣ Y - P) :
    (Y * G).coeff index = (P * G).coeff index := by
  have hdiv : Polynomial.X ^ order ∣ (Y - P) * G :=
    dvd_mul_of_dvd_left agreement G
  have hzero := Polynomial.X_pow_dvd_iff.mp hdiv index below
  rw [sub_mul, Polynomial.coeff_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- The full coefficient-recovery identity for one nonzero interpolation node,
at arbitrary positive multiplicity. Its reciprocal weight is constructed here.
There is no assumption of a Hermite coefficient identity. -/
theorem single_node_hermite_identity (H Y : Polynomial K) (t : K)
    (nonzero : t ≠ 0) (order : ℕ) (positive : 0 < order)
    (degree_bound : H.natDegree < order)
    (taylor_agreement : Polynomial.X ^ order ∣ Y - Polynomial.taylor t H) :
    H.eval 0 = -(-t) ^ order *
      (Y * reciprocalWeight t order).coeff (order - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have hdegree : (Polynomial.taylor t H).natDegree < n + 1 := by
    rwa [Polynomial.natDegree_taylor]
  have h := single_node_polynomial_recovery (Polynomial.taylor t H) t nonzero n hdegree
  rw [Polynomial.taylor_eval, neg_add_cancel] at h
  have hcoeff := coeff_mul_eq_of_X_pow_dvd_sub Y (Polynomial.taylor t H)
    (reciprocalWeight t (n + 1)) (n + 1) n (Nat.lt_succ_self n) taylor_agreement
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    h.trans (congrArg (fun c => -(-t) ^ (n + 1) * c) hcoeff.symm)

/-- The paper's scalar evaluation formula, fully proved for one node. The
finite-field degree bound is needed only for the coefficient projector. -/
theorem single_node_scalar_recovery {p : ℕ} [Fact p.Prime]
    (H Y : Polynomial (ZMod p)) (t : ZMod p) (nonzero : t ≠ 0)
    (order : ℕ) (positive : 0 < order) (below_prime : order < p)
    (degree_bound : H.natDegree < order)
    (Y_degree : Y.natDegree ≤ p - 2)
    (taylor_agreement : Polynomial.X ^ order ∣ Y - Polynomial.taylor t H) :
    H.eval 0 = (-t) ^ order * ∑ z : (ZMod p)ˣ,
      (z : ZMod p) ^ (p - order) *
        (reciprocalWeight t order).eval (z : ZMod p) * Y.eval (z : ZMod p) := by
  rw [single_node_hermite_identity H Y t nonzero order positive degree_bound taylor_agreement,
    NtimeDspace.weighted_taylor_projector Y (reciprocalWeight t order) order
      positive below_prime Y_degree (reciprocalWeight_degree_lt t order positive)]
  ring

end NtimeDspace.HermiteRecovery
