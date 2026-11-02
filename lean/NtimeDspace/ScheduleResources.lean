import NtimeDspace.ScheduleSearch

/-!
Discrete representation budgets for the explicit schedule implementation.
The chosen seed is a single natural mask with a proved bit limit; its layout
has exactly the matrix-and-offset bit count. These bounds concern the stored
representations and counter ranges, not the work tapes of a full machine.
-/

namespace NtimeDspace.ScheduleResources

open Parameters ParameterChoice

variable {n r nodes : ℕ}

/-- A concrete logarithmic bound for the possibly gapped factor identifiers. -/
theorem four_mul_log2_le (n : ℕ) : (4 * n + 1).log2 ≤ n.log2 + 2 := by
  have upper : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have scaled : 4 * n + 1 < 2 ^ (n.log2 + 3) := by
    rw [show n.log2 + 3 = (n.log2 + 1) + 2 by omega, pow_add]
    norm_num
    omega
  have small : (4 * n + 1).log2 < n.log2 + 3 :=
    (Nat.log2_lt (by omega : 4 * n + 1 ≠ 0)).mpr scaled
  omega

theorem inputBits_le_log2 (formula : Formula n) (bounded : formula.BoundedOccurrence) :
    PopulationAccess.inputBits formula ≤ n.log2 + 3 :=
  (PopulationAccess.inputBits_le formula bounded).trans
    (by have := four_mul_log2_le n; omega)

/-- Exact relation between the full joint-seed layout and the admissibility
cost. Both affine matrices and both offsets are counted. -/
theorem seed_bits_identity (inputBits k : ℕ) :
    8 * AffineSeedEncoding.totalBits inputBits (Q k) k = cost k * (inputBits + 1) := by
  simp only [AffineSeedEncoding.totalBits, Q, cost]
  ring

theorem seed_bits_le (formula : Formula n) (k : ℕ) (admissible : cost k ≤ n.log2) :
    8 * AffineSeedEncoding.totalBits (PopulationAccess.inputBits formula) (Q k) k ≤
      n.log2 * (PopulationAccess.inputBits formula + 1) := by
  rw [seed_bits_identity]
  exact Nat.mul_le_mul_right _ admissible

/-- The complete stored seed has O(log² n) bits, with a discrete constant and
no asymptotic premise on the selected search parameter. -/
theorem chosen_seed_bits_le (formula : Formula n) (bounded : formula.BoundedOccurrence) :
    8 * AffineSeedEncoding.totalBits (PopulationAccess.inputBits formula) (Q (choose n)) (choose n) ≤
      n.log2 * (n.log2 + 4) := by
  exact (seed_bits_le formula (choose n) (ParameterChoice.admissible n)).trans
    (Nat.mul_le_mul_left _ (by have := inputBits_le_log2 formula bounded; omega))

/-- The selected natural counter is represented by precisely that many
available bit positions; its higher bits are all false. -/
theorem chosen_seed_no_high_bits (formula : Formula n) (bit : ℕ)
    (high : AffineSeedEncoding.totalBits (PopulationAccess.inputBits formula)
      (Q (choose n)) (choose n) ≤ bit) :
    (ScheduleSearch.selectedMask formula (Q (choose n)) (choose n)).testBit bit = false := by
  apply Nat.testBit_lt_two_pow
  exact (ScheduleSearch.selectedMask_lt formula (Q (choose n)) (choose n)).trans_le
    (Nat.pow_le_pow_right (by decide) high)

/-- The rank's accumulator is also bounded by the actual full population,
including all unused-variable dummies. -/
theorem bucketSize_le_population (formula : Formula n)
    (label : FormulaIncidences.Incidence formula → TensorEvaluation.Label r nodes)
    (value : TensorEvaluation.Label r nodes) :
    RankedPopulationPlacement.bucketSize formula label value ≤ PopulationAccess.populationCount formula := by
  rw [RankedPopulationPlacement.bucketSize_eq_card, PopulationAccess.populationCount_correct]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem rank_lt_population (formula : Formula n)
    (label : FormulaIncidences.Incidence formula → TensorEvaluation.Label r nodes)
    (inc : FormulaIncidences.Incidence formula) :
    RankedPopulationPlacement.rank formula label inc < PopulationAccess.populationCount formula :=
  (RankedPopulationPlacement.rank_lt_bucket formula label inc).trans_le
    (bucketSize_le_population formula label (label inc))

theorem rank_lt_three_variables (formula : Formula n) (bounded : formula.BoundedOccurrence)
    (label : FormulaIncidences.Incidence formula → TensorEvaluation.Label r nodes)
    (inc : FormulaIncidences.Incidence formula) :
    RankedPopulationPlacement.rank formula label inc < 3 * n := by
  have bound := FormulaIncidences.population_le_three_variables formula bounded
  rw [← PopulationAccess.populationCount_correct] at bound
  exact (rank_lt_population formula label inc).trans_le bound

end NtimeDspace.ScheduleResources
