import NtimeDspace.HashVariance

/-!
# Balanced affine schedules for arbitrary incidence degrees

`HashVariance.exists_balanced_affine_seed` is stated for degree-three
variables and factors, which gives the constants `6` and `12`. A weighted
constraint system of arity `Δ` has factors of degree up to `Δ`. Here the
degree bounds are parameters `a` and `b`: the incidence second moment is at most
`(a+b)M`, and the incidence parameter becomes `2(a+b)D² ≤ M`.
-/

namespace NtimeDspace.WHashVariance

open scoped BigOperators
open HashSchedules HashVariance

/-- The balanced-seed selection with a general variance constant `c`. -/
theorem exists_balanced_seed_const {Seed Label NodeGroup : Type*}
    (seeds : Finset Seed) (nonempty : seeds.Nonempty)
    (labels : Finset Label) (nodeGroups : Finset NodeGroup)
    (incidences : Seed → Label → ℚ) (groupOccupancy : Seed → NodeGroup → ℚ)
    (M D Q N r c : ℚ)
    (M_positive : 0 < M) (D_positive : 0 < D) (Q_positive : 0 < Q)
    (N_positive : 0 < N) (r_positive : 0 < r) (c_positive : 0 < c)
    (incidence_parameter : 2 * c * D ^ 2 ≤ M)
    (group_parameter : 2 * Q * r ^ 2 ≤ N)
    (incidence_moment :
      ∑ seed ∈ seeds, squaredDeviation labels (incidences seed) (M / D) ≤
        seeds.card * (c * M))
    (group_moment :
      ∑ seed ∈ seeds, squaredDeviation nodeGroups (groupOccupancy seed) (N / r) ≤
        seeds.card * (Q * N)) :
    ∃ seed ∈ seeds,
      (∀ label ∈ labels, incidences seed label ≤ 2 * M / D) ∧
      (∀ nodeGroup ∈ nodeGroups, groupOccupancy seed nodeGroup ≤ 2 * N / r) := by
  obtain ⟨seed, hseed, hincidence, hgroup⟩ := exists_simultaneous_bounds seeds nonempty
    (fun seed => squaredDeviation labels (incidences seed) (M / D))
    (fun seed => squaredDeviation nodeGroups (groupOccupancy seed) (N / r))
    (c * M) (Q * N) (by positivity) (mul_pos Q_positive N_positive)
    (fun _ _ => squaredDeviation_nonnegative _ _ _)
    (fun _ _ => squaredDeviation_nonnegative _ _ _) incidence_moment group_moment
  refine ⟨seed, hseed, ?_, ?_⟩
  · intro label hlabel
    apply occupancy_bound_of_variance _ M D (2 * c) M_positive.le D_positive incidence_parameter
    have h := (deviation_square_le labels (incidences seed) (M / D) label hlabel).trans hincidence
    nlinarith
  · intro nodeGroup hnodeGroup
    apply occupancy_bound_of_variance _ N r (2 * Q) N_positive.le r_positive group_parameter
    have h := (deviation_square_le nodeGroups (groupOccupancy seed) (N / r) nodeGroup
      hnodeGroup).trans hgroup
    nlinarith

section Incidences

variable {Item Bucket Seed Variable Factor : Type*} [Fintype Item]
variable [DecidableEq Variable] [DecidableEq Factor]
variable [Fintype Bucket] [DecidableEq Bucket] [Nonempty Bucket] [Fintype Seed]

/-- The incidence second moment `E Δ ≤ (a+b)M` for degree bounds `a` and `b`. -/
theorem incidence_second_moment_le
    (hash : Seed → Item → Bucket) (variableOf : Item → Variable) (factorOf : Item → Factor)
    (a b : ℚ)
    (variable_bound : ∀ incidence, bucketCount variableOf (variableOf incidence) ≤ a)
    (factor_bound : ∀ incidence, bucketCount factorOf (factorOf incidence) ≤ b)
    (ordinary_collision : ∀ first second,
      variableOf first ≠ variableOf second → factorOf first ≠ factorOf second →
        collisionCount hash first second ≤ (Fintype.card Seed : ℚ) / Fintype.card Bucket) :
    (∑ seed, squaredDeviation Finset.univ (bucketCount (hash seed))
      ((Fintype.card Item : ℚ) / Fintype.card Bucket)) ≤
      Fintype.card Seed * ((a + b) * (Fintype.card Item : ℚ)) := by
  have hmoment := sum_squaredDeviation_le_exceptional hash
    (fun first second => variableOf first = variableOf second ∨ factorOf first = factorOf second)
    (fun first second h => ordinary_collision first second
      (fun hv => h (Or.inl hv)) (fun hf => h (Or.inr hf)))
  have hpairs := exceptional_incidence_pairs_le variableOf factorOf a b variable_bound factor_bound
  have hscaled := mul_le_mul_of_nonneg_left hpairs
    (show (0 : ℚ) ≤ Fintype.card Seed by positivity)
  nlinarith

end Incidences

section AffineIncidences

variable {Item Input Output K : Type*} [Fintype Item] [Fintype Input] [Fintype Output]
variable [DecidableEq Input] [DecidableEq Output] [Field K] [Fintype K] [DecidableEq K]

theorem affine_incidence_second_moment_le
    (variableCode factorCode : Item → Input → K) (a b : ℚ)
    (variable_bound : ∀ incidence, bucketCount variableCode (variableCode incidence) ≤ a)
    (factor_bound : ∀ incidence, bucketCount factorCode (factorCode incidence) ≤ b) :
    (∑ seed : AffineSeed Input Output K × AffineSeed Input Output K,
      squaredDeviation Finset.univ
        (bucketCount (productHash affineEval affineEval variableCode factorCode seed))
        ((Fintype.card Item : ℚ) / Fintype.card ((Output → K) × (Output → K)))) ≤
      Fintype.card (AffineSeed Input Output K × AffineSeed Input Output K) *
        ((a + b) * (Fintype.card Item : ℚ)) := by
  apply incidence_second_moment_le _ variableCode factorCode a b variable_bound factor_bound
  intro first second variables_distinct factors_distinct
  rw [collisionCount_productHash,
    affine_collisionCount (variableCode first) (variableCode second) variables_distinct,
    affine_collisionCount (factorCode first) (factorCode second) factors_distinct]
  simp only [Fintype.card_prod, Nat.cast_mul]
  exact le_of_eq (div_mul_div_comm _ _ _ _)

end AffineIncidences

section BalancedAffineSchedules

variable {Incidence Variable Factor Input Node Bit K : Type*}
variable [Fintype Incidence] [Nonempty Incidence] [Fintype Variable] [Nonempty Variable]
variable [DecidableEq Variable] [DecidableEq Factor]
variable [Fintype Input] [DecidableEq Input] [Fintype Node] [Nonempty Node] [DecidableEq Node]
variable [Fintype Bit] [DecidableEq Bit] [Field K] [Fintype K] [DecidableEq K]

/-- **Balanced affine schedules for degree bounds `a` and `b`.** -/
theorem exists_balanced_affine_seed
    (variableOf : Incidence → Variable) (factorOf : Incidence → Factor)
    (variableCode : Variable → Input → K) (factorCode : Factor → Input → K)
    (variable_injective : Function.Injective variableCode)
    (factor_injective : Function.Injective factorCode)
    (a b : ℚ) (degrees_positive : 0 < a + b)
    (variable_degree : ∀ variableIndex, bucketCount variableOf variableIndex ≤ a)
    (factor_degree : ∀ factorIndex, bucketCount factorOf factorIndex ≤ b)
    (incidence_parameter :
      2 * (a + b) * (Fintype.card (((Node × Bit) → K) × ((Node × Bit) → K)) : ℚ) ^ 2 ≤
        Fintype.card Incidence)
    (group_parameter :
      2 * (Fintype.card Node : ℚ) * (Fintype.card (Bit → K) : ℚ) ^ 2 ≤
        Fintype.card Variable) :
    ∃ seed : AffineSeed Input (Node × Bit) K × AffineSeed Input (Node × Bit) K,
      (∀ label,
        bucketCount (productHash affineEval affineEval
          (variableCode ∘ variableOf) (factorCode ∘ factorOf) seed) label ≤
          2 * (Fintype.card Incidence : ℚ) /
            Fintype.card (((Node × Bit) → K) × ((Node × Bit) → K))) ∧
      (∀ node group,
        bucketCount (fun variableIndex bit =>
          affineEval seed.1 (variableCode variableIndex) (node, bit)) group ≤
          2 * (Fintype.card Variable : ℚ) / Fintype.card (Bit → K)) := by
  have incidence_moment := affine_incidence_second_moment_le
    (Output := Node × Bit) (variableCode ∘ variableOf) (factorCode ∘ factorOf) a b
    (fun incidence => by
      simpa only [Function.comp_apply,
        bucketCount_comp_injective variableOf variableCode variable_injective] using
          variable_degree (variableOf incidence))
    (fun incidence => by
      simpa only [Function.comp_apply,
        bucketCount_comp_injective factorOf factorCode factor_injective] using
          factor_degree (factorOf incidence))
  have group_moment := affine_joint_group_second_moment_le
    (Node := Node) (Bit := Bit) variableCode variable_injective
  obtain ⟨seed, _, incidence_bound, group_bound⟩ := exists_balanced_seed_const
    Finset.univ Finset.univ_nonempty Finset.univ Finset.univ
    (fun seed => bucketCount (productHash affineEval affineEval
      (variableCode ∘ variableOf) (factorCode ∘ factorOf) seed))
    (fun seed (nodeGroup : Node × (Bit → K)) => bucketCount
      (fun variableIndex bit => affineEval seed.1 (variableCode variableIndex) (nodeGroup.1, bit))
      nodeGroup.2)
    (Fintype.card Incidence)
    (Fintype.card (((Node × Bit) → K) × ((Node × Bit) → K)))
    (Fintype.card Node) (Fintype.card Variable) (Fintype.card (Bit → K)) (a + b)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    degrees_positive incidence_parameter group_parameter
    (by simpa only [Finset.card_univ] using incidence_moment)
    (by simpa only [Finset.card_univ] using group_moment)
  exact ⟨seed, fun label => incidence_bound label (Finset.mem_univ _),
    fun node group => group_bound (node, group) (Finset.mem_univ _)⟩

end BalancedAffineSchedules

end NtimeDspace.WHashVariance
