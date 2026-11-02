import NtimeDspace.TensorBasisField
import Mathlib.Data.Real.Basic

/-!
The exact one-coordinate antisymmetric frequency of the concrete ordered-pair
basis. The proof uses swapping symmetry and counts the diagonal separately.
-/

namespace NtimeDspace.SpectralPairCount

noncomputable section

open scoped BigOperators

def antisymmetricBit {r : ℕ} (pair : Fin r × Fin r) : ℝ :=
  if pair.2 < pair.1 then 1 else 0

theorem antisymmetricBit_bounds {r : ℕ} (pair : Fin r × Fin r) :
    antisymmetricBit pair ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [antisymmetricBit]
  split_ifs <;> simp

theorem antisymmetricBit_sum (r : ℕ) :
    2 * (∑ pair : Fin r × Fin r, antisymmetricBit pair) = (r : ℝ) * ((r : ℝ) - 1) := by
  have swap : (∑ pair : Fin r × Fin r, antisymmetricBit pair.swap) =
      ∑ pair : Fin r × Fin r, antisymmetricBit pair :=
    (Equiv.prodComm (Fin r) (Fin r)).sum_comp antisymmetricBit
  have diagonal : (∑ pair : Fin r × Fin r, if pair.1 = pair.2 then (1 : ℝ) else 0) = r := by
    rw [Fintype.sum_prod_type]
    simp
  have point (pair : Fin r × Fin r) :
      antisymmetricBit pair + antisymmetricBit pair.swap +
        (if pair.1 = pair.2 then (1 : ℝ) else 0) = 1 := by
    simp only [antisymmetricBit, Prod.fst_swap, Prod.snd_swap]
    split_ifs <;> norm_num <;> omega
  have total := congrArg (fun f : (Fin r × Fin r) → ℝ => ∑ pair, f pair) (funext point)
  simp only [Finset.sum_add_distrib, swap, diagonal, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_mul] at total
  nlinarith

theorem antisymmetricCount_eq_sum {Node : Type*} [Fintype Node] [DecidableEq Node]
    {r : ℕ} (index : TensorBasisField.Label Node r) :
    (TensorBasisField.antisymmetricCount index : ℝ) = ∑ t, antisymmetricBit (index t) := by
  simp [TensorBasisField.antisymmetricCount, TensorBasisField.antisymmetricCoordinates,
    antisymmetricBit, Finset.sum_boole]

end

end NtimeDspace.SpectralPairCount
