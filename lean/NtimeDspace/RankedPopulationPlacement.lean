import NtimeDspace.PopulationAccess
import NtimeDspace.TensorEvaluation

/-!
Copy placement by scalar predecessor counts over the literal-plus-dummy
population. The explicit incidence identifier may contain gaps; only actual
incidences contribute to the scan. No inverse enumeration, occupancy table,
or list of bucket members is executed. These are arithmetic access procedures,
not yet a tape-space bound.
-/

namespace NtimeDspace.RankedPopulationPlacement

open scoped BigOperators

variable {n r Q : ℕ}

abbrev Incidence (formula : Formula n) := FormulaIncidences.Incidence formula

def rank (formula : Formula n) (label : Incidence formula → TensorEvaluation.Label r Q)
    (inc : Incidence formula) : ℕ :=
  PopulationAccess.scanPopulation formula (fun other =>
    if (PopulationAccess.incidenceNumber formula other).val <
        (PopulationAccess.incidenceNumber formula inc).val ∧
        TensorEvaluation.sameLabel (label other) (label inc) = true then 1 else 0) 0

def bucketSize (formula : Formula n) (label : Incidence formula → TensorEvaluation.Label r Q)
    (value : TensorEvaluation.Label r Q) : ℕ :=
  PopulationAccess.scanPopulation formula (fun inc =>
    if TensorEvaluation.sameLabel (label inc) value then 1 else 0) 0

theorem rank_eq_card (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (inc : Incidence formula) :
    rank formula label inc =
      (Finset.univ.filter (fun other : Incidence formula =>
        (PopulationAccess.incidenceNumber formula other).val <
          (PopulationAccess.incidenceNumber formula inc).val ∧ label other = label inc)).card := by
  classical
  simp only [rank, PopulationAccess.scanPopulation_correct, add_zero, Finset.card_filter,
    TensorEvaluation.sameLabel_correct]

theorem bucketSize_eq_card (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (value : TensorEvaluation.Label r Q) :
    bucketSize formula label value =
      (Finset.univ.filter (fun inc : Incidence formula => label inc = value)).card := by
  classical
  simp only [bucketSize, PopulationAccess.scanPopulation_correct, add_zero, Finset.card_filter,
    TensorEvaluation.sameLabel_correct]

theorem bucketSize_eq_bucketCount (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (value : TensorEvaluation.Label r Q) :
    (bucketSize formula label value : ℚ) = HashVariance.bucketCount label value := by
  classical
  simp only [bucketSize_eq_card, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, HashVariance.bucketCount]

theorem rank_lt_bucket (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (inc : Incidence formula) :
    rank formula label inc < bucketSize formula label (label inc) := by
  classical
  rw [rank_eq_card, bucketSize_eq_card]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro other member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
    exact member.2
  · intro same
    have member : inc ∈ Finset.univ.filter (fun other : Incidence formula => label other = label inc) := by simp
    rw [← same] at member
    simp at member

theorem rank_strict (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (first second : Incidence formula)
    (earlier : (PopulationAccess.incidenceNumber formula first).val <
      (PopulationAccess.incidenceNumber formula second).val)
    (same_label : label first = label second) : rank formula label first < rank formula label second := by
  classical
  rw [rank_eq_card, rank_eq_card]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro other member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
    exact ⟨member.1.trans earlier, member.2.trans same_label⟩
  · intro same
    have member : first ∈ Finset.univ.filter (fun other : Incidence formula =>
        (PopulationAccess.incidenceNumber formula other).val <
          (PopulationAccess.incidenceNumber formula second).val ∧ label other = label second) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, earlier, same_label⟩
    rw [← same] at member
    simp at member

theorem placement_injective (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) :
    Function.Injective (fun inc => (rank formula label inc, label inc)) := by
  intro first second same
  have ranks : rank formula label first = rank formula label second := congrArg Prod.fst same
  have labels : label first = label second := congrArg Prod.snd same
  rcases lt_trichotomy (PopulationAccess.incidenceNumber formula first).val
      (PopulationAccess.incidenceNumber formula second).val with before | equal | after
  · have := rank_strict formula label first second before labels
    omega
  · exact PopulationAccess.incidenceNumber_injective formula (Fin.ext equal)
  · have := rank_strict formula label second first after labels.symm
    omega

/-- Capacity enters only as a bound on the scalar predecessor count. -/
def copyIndex (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (capacity : ℕ)
    (bounded : ∀ value, bucketSize formula label value ≤ capacity) (inc : Incidence formula) :
    Fin capacity :=
  ⟨rank formula label inc, (rank_lt_bucket formula label inc).trans_le (bounded (label inc))⟩

theorem copyIndex_placement_injective (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (capacity : ℕ)
    (bounded : ∀ value, bucketSize formula label value ≤ capacity) :
    Function.Injective (fun inc => (copyIndex formula label capacity bounded inc, label inc)) := by
  intro first second same
  apply placement_injective formula label
  exact congrArg (fun pair => (pair.1.val, pair.2)) same

/-- Floor capacity computed using natural division, rather than a rational
floor or a stored occupancy table. -/
def copyCount (formula : Formula n) (r Q : ℕ) : ℕ :=
  2 * PopulationAccess.populationCount formula / r ^ (2 * Q)

theorem copy_slots_le (formula : Formula n) (r Q : ℕ) :
    copyCount formula r Q * r ^ (2 * Q) ≤ 2 * PopulationAccess.populationCount formula :=
  Nat.div_mul_le_self _ _

theorem balanced_bucket_bound (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (positive : 0 < r)
    (balanced : ∀ value, bucketSize formula label value * r ^ (2 * Q) ≤
      2 * PopulationAccess.populationCount formula) (value : TensorEvaluation.Label r Q) :
    bucketSize formula label value ≤ copyCount formula r Q := by
  exact (Nat.le_div_iff_mul_le (pow_pos positive _)).mpr (balanced value)

/-- Restrict the injective full-population placement to actual literal positions.
Dummy incidences affect ranks, but never become new formula literals. -/
def literalCopy (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (capacity : ℕ)
    (bounded : ∀ value, bucketSize formula label value ≤ capacity) :
    FormulaCounter.Incidence formula → Fin capacity :=
  fun inc => copyIndex formula label capacity bounded (.inl inc)

theorem literal_placement_injective (formula : Formula n)
    (label : Incidence formula → TensorEvaluation.Label r Q) (capacity : ℕ)
    (bounded : ∀ value, bucketSize formula label value ≤ capacity) :
    Function.Injective (fun inc => (literalCopy formula label capacity bounded inc, label (.inl inc))) :=
  (copyIndex_placement_injective formula label capacity bounded).comp Sum.inl_injective

end NtimeDspace.RankedPopulationPlacement
