import NtimeDspace.RankedPopulationPlacement
import NtimeDspace.AffineScheduleEvaluation

/-!
Explicit binary identifiers and scalar affine schedules for the full incidence
population. Clause identifiers precede declared-variable dummy identifiers;
gaps left by used variables cause no collision. The second-moment construction
applies to these concrete injective identifiers, so it does not need a chosen
finite-type enumeration. Exhaustive seed search and machine costs are separate.
-/

namespace NtimeDspace.UniformSchedules

open scoped BigOperators
open HashSchedules

variable {n Q : ℕ}

abbrev Seed (formula : Formula n) (Q bits : ℕ) :=
  AffineSeed (Fin (PopulationAccess.inputBits formula)) (Fin Q × Fin bits) (ZMod 2) ×
    AffineSeed (Fin (PopulationAccess.inputBits formula)) (Fin Q × Fin bits) (ZMod 2)

abbrev Label (Q bits : ℕ) := TensorEvaluation.Label (2 ^ bits) Q

theorem identifier_capacity (formula : Formula n) :
    formula.clauses.length + n ≤ 2 ^ PopulationAccess.inputBits formula :=
  Nat.lt_log2_self.le

def variableInput (formula : Formula n) (v : Fin n) :
    Fin (PopulationAccess.inputBits formula) → ZMod 2 :=
  AffineScheduleEvaluation.binaryDecode
    ⟨v.val, v.isLt.trans_le ((by omega : n ≤ formula.clauses.length + n).trans
      (identifier_capacity formula))⟩

def factorInput (formula : Formula n) (factor : FormulaIncidences.Factor formula) :
    Fin (PopulationAccess.inputBits formula) → ZMod 2 :=
  AffineScheduleEvaluation.binaryDecode
    ⟨(PopulationAccess.factorNumber formula factor).val,
      (PopulationAccess.factorNumber formula factor).isLt.trans_le (identifier_capacity formula)⟩

theorem variableInput_injective (formula : Formula n) : Function.Injective (variableInput formula) := by
  intro first second same
  have encoded := congrArg AffineScheduleEvaluation.binaryEncode same
  simp only [variableInput, AffineScheduleEvaluation.binaryEncode_decode] at encoded
  exact Fin.ext (congrArg (fun index : Fin (2 ^ PopulationAccess.inputBits formula) => index.val) encoded)

theorem factorInput_injective (formula : Formula n) : Function.Injective (factorInput formula) := by
  intro first second same
  have encoded := congrArg AffineScheduleEvaluation.binaryEncode same
  simp only [factorInput, AffineScheduleEvaluation.binaryEncode_decode] at encoded
  exact PopulationAccess.factorNumber_injective formula (Fin.ext (congrArg (fun index : Fin (2 ^ PopulationAccess.inputBits formula) => index.val) encoded))

def variableGroup (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits)
    (node : Fin Q) (v : Fin n) : Fin (2 ^ bits) :=
  AffineScheduleEvaluation.group seed.1 (variableInput formula v) node

def factorGroup (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits)
    (node : Fin Q) (factor : FormulaIncidences.Factor formula) : Fin (2 ^ bits) :=
  AffineScheduleEvaluation.group seed.2 (factorInput formula factor) node

def incidenceLabel (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits)
    (inc : FormulaIncidences.Incidence formula) : Label Q bits :=
  fun node =>
    (variableGroup formula bits seed node (FormulaIncidences.variableOf formula inc),
      factorGroup formula bits seed node (FormulaIncidences.factorOf formula inc))

def literalLabel (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits)
    (inc : FormulaCounter.Incidence formula) : Label Q bits :=
  incidenceLabel formula bits seed (.inl inc)

def clauseGroup (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits)
    (node : Fin Q) (clause : Fin formula.clauses.length) : Fin (2 ^ bits) :=
  factorGroup formula bits seed node (.inl clause)

theorem variables_match (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits)
    (node : Fin Q) (inc : FormulaCounter.Incidence formula) :
    variableGroup formula bits seed node (IncidenceEvaluation.variableOf formula inc) =
      (literalLabel formula bits seed inc node).1 := rfl

theorem clauses_match (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits)
    (node : Fin Q) (inc : FormulaCounter.Incidence formula) :
    (literalLabel formula bits seed inc node).2 = clauseGroup formula bits seed node inc.1 := rfl

/-- Balance uses only integer cross-products of scalar counts. -/
def Balanced (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits) : Prop :=
  (∀ value, RankedPopulationPlacement.bucketSize formula (incidenceLabel formula bits seed) value *
      (2 ^ bits) ^ (2 * Q) ≤ 2 * PopulationAccess.populationCount formula) ∧
  (∀ node group, LocalAssignmentLoop.groupSize (variableGroup formula bits seed node) group *
      2 ^ bits ≤ 2 * n)

/-- Proof-side raw output, used only to apply the finite affine-family theorem. -/
noncomputable def rawLabel (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits) :=
  HashVariance.productHash affineEval affineEval
    (variableInput formula ∘ FormulaIncidences.variableOf formula)
    (factorInput formula ∘ FormulaIncidences.factorOf formula) seed

theorem incidenceLabel_eq_raw (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits) :
    incidenceLabel formula bits seed =
      SchedulePlacement.labelEquiv (Fin Q) bits ∘ rawLabel formula bits seed := by
  funext inc node
  simp only [incidenceLabel, variableGroup, factorGroup, AffineScheduleEvaluation.group_correct,
    Function.comp_apply, SchedulePlacement.labelEquiv, rawLabel, HashVariance.productHash]
  rfl

/-- The same variance argument works with our explicit, possibly gapped,
identifiers; no chosen enumeration or seed is executed by these maps. -/
theorem exists_balanced_schedule (formula : Formula n) (bounded : formula.BoundedOccurrence)
    (positive : 0 < n) (nodes_positive : 0 < Q) (bits : ℕ)
    (incidence_parameter : 12 * (((2 ^ bits) ^ (2 * Q) : ℕ) : ℚ) ^ 2 ≤
      FormulaIncidences.population formula)
    (group_parameter : 2 * (Q : ℚ) * ((2 ^ bits : ℕ) : ℚ) ^ 2 ≤ n) :
    ∃ seed : Seed formula Q bits, Balanced formula bits seed := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, positive⟩⟩
  let : Nonempty (Fin Q) := ⟨⟨0, nodes_positive⟩⟩
  let : Nonempty (FormulaIncidences.Incidence formula) :=
    Fintype.card_pos_iff.mp (positive.trans_le (FormulaIncidences.variables_le_population formula))
  have hincidence : 12 * (Fintype.card (SchedulePlacement.RawLabel (Fin Q) bits) : ℚ) ^ 2 ≤
      Fintype.card (FormulaIncidences.Incidence formula) := by
    simpa only [SchedulePlacement.label_card, Fintype.card_fin, FormulaIncidences.population]
      using incidence_parameter
  have hgroup : 2 * (Fintype.card (Fin Q) : ℚ) *
      (Fintype.card (Fin bits → ZMod 2) : ℚ) ^ 2 ≤ Fintype.card (Fin n) := by
    simpa using group_parameter
  obtain ⟨seed, labels, groups⟩ := HashVariance.exists_balanced_affine_seed
    (Node := Fin Q) (Bit := Fin bits)
    (FormulaIncidences.variableOf formula) (FormulaIncidences.factorOf formula)
    (variableInput formula) (factorInput formula)
    (variableInput_injective formula) (factorInput_injective formula)
    (FormulaIncidences.variable_bucketCount_le_three formula bounded)
    (FormulaIncidences.factor_bucketCount_le_three formula) hincidence hgroup
  refine ⟨seed, ?_, ?_⟩
  · intro value
    have same := HashVariance.bucketCount_comp_injective (rawLabel formula bits seed)
      (SchedulePlacement.labelEquiv (Fin Q) bits) (SchedulePlacement.labelEquiv (Fin Q) bits).injective
      ((SchedulePlacement.labelEquiv (Fin Q) bits).symm value)
    simp only [Equiv.apply_symm_apply] at same
    have count : (RankedPopulationPlacement.bucketSize formula
        (incidenceLabel formula bits seed) value : ℚ) ≤
          2 * (PopulationAccess.populationCount formula : ℚ) / ((2 ^ bits) ^ (2 * Q) : ℕ) := by
      rw [RankedPopulationPlacement.bucketSize_eq_bucketCount, incidenceLabel_eq_raw, same,
        PopulationAccess.populationCount_correct]
      simpa only [rawLabel, SchedulePlacement.label_card, Fintype.card_fin,
        FormulaIncidences.population, Nat.cast_pow, Nat.cast_ofNat] using
        labels ((SchedulePlacement.labelEquiv (Fin Q) bits).symm value)
    have multiplied := (le_div_iff₀ (by positivity : (0 : ℚ) < ((2 ^ bits) ^ (2 * Q) : ℕ))).mp count
    exact_mod_cast multiplied
  · intro node group
    have same := HashVariance.bucketCount_comp_injective
      (fun v bit => affineEval seed.1 (variableInput formula v) (node, bit))
      (SchedulePlacement.binaryEquiv bits).symm (SchedulePlacement.binaryEquiv bits).symm.injective
      (SchedulePlacement.binaryEquiv bits group)
    simp only [Equiv.symm_apply_apply] at same
    have count : (LocalAssignmentLoop.groupSize (variableGroup formula bits seed node) group : ℚ) ≤
        2 * (n : ℚ) / (2 ^ bits : ℕ) := by
      rw [LocalAssignmentLoop.groupSize_eq_card]
      have castCard : ((CanonicalPlacement.bucket (variableGroup formula bits seed node) group).card : ℚ) =
          HashVariance.bucketCount (variableGroup formula bits seed node) group := by
        simp only [CanonicalPlacement.bucket, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero, HashVariance.bucketCount]
      rw [castCard]
      have map_eq : variableGroup formula bits seed node =
          (SchedulePlacement.binaryEquiv bits).symm ∘
            (fun v bit => affineEval seed.1 (variableInput formula v) (node, bit)) := by
        funext v
        exact AffineScheduleEvaluation.group_correct _ _ _
      rw [map_eq, same]
      simpa using groups node (SchedulePlacement.binaryEquiv bits group)
    have multiplied := (le_div_iff₀ (by positivity : (0 : ℚ) < (2 ^ bits : ℕ))).mp count
    exact_mod_cast multiplied

end NtimeDspace.UniformSchedules
