import NtimeDspace.Projector

/-!
The scalar-evaluation transformation in Lemma `lem:scalar`.

This proves the finite-field transformation of a coefficient recovery identity.
The Hermite coefficient identity is an explicit hypothesis in this intermediate
module; `HermiteRecovery.lean` constructs the weights and `HermiteGlobal.lean`
proves that identity.
No theorem here asserts the complete scalar Hermite lemma or a space bound.
-/

namespace NtimeDspace

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

/-- An untruncated polynomial of degree at most `p-2` may be multiplied by a
weight of degree below `J` without aliasing the desired coefficient `J-1`. -/
theorem weighted_taylor_projector
    (Y G : Polynomial (ZMod p)) (J : ℕ)
    (hJ : 0 < J) (hJp : J < p)
    (hY : Y.natDegree ≤ p - 2) (hG : G.natDegree < J) :
    (Y * G).coeff (J - 1) =
      -(∑ z : (ZMod p)ˣ,
        (z : ZMod p) ^ (p - J) * G.eval (z : ZMod p) * Y.eval (z : ZMod p)) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hi : J - 1 < p - 1 := by omega
  have hdeg : (Y * G).natDegree < (J - 1) + (p - 1) := by
    have hmul : (Y * G).natDegree ≤ Y.natDegree + G.natDegree := Polynomial.natDegree_mul_le
    omega
  have hexp : p - 1 - (J - 1) = p - J := by omega
  rw [coefficient_projector_neg (Y * G) (J - 1) hi hdeg, hexp]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [Polynomial.eval_mul]
  ring

/-- The nested scalar sum used by the modular counter, as an algebraic function.
This finite sum specifies its value; it is not a compiled streaming machine. -/
noncomputable def scalarRecover {Node : Type*} [Fintype Node]
    (omegaZero : ZMod p) (J : ℕ)
    (Y G : Node → Polynomial (ZMod p)) : ZMod p :=
  omegaZero * ∑ t, ∑ z : (ZMod p)ˣ,
    (z : ZMod p) ^ (p - J) * (G t).eval (z : ZMod p) * (Y t).eval (z : ZMod p)

/-- The new evaluation transformation preserves any explicitly supplied Hermite
coefficient-recovery identity. The hypothesis `hHermite` is visible and is not
an axiom, an instance, or an asserted existence result. -/
theorem scalarRecover_eq_of_hermite_identity {Node : Type*} [Fintype Node]
    (omegaZero target : ZMod p) (J : ℕ)
    (Y G : Node → Polynomial (ZMod p))
    (hJ : 0 < J) (hJp : J < p)
    (hY : ∀ t, (Y t).natDegree ≤ p - 2)
    (hG : ∀ t, (G t).natDegree < J)
    (hHermite : target = -omegaZero * ∑ t, (Y t * G t).coeff (J - 1)) :
    scalarRecover omegaZero J Y G = target := by
  rw [hHermite]
  simp_rw [weighted_taylor_projector _ _ J hJ hJp (hY _) (hG _)]
  simp [scalarRecover, Finset.sum_neg_distrib]

end NtimeDspace
