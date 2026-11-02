import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Balanced schedules from finite second-moment bounds

This file proves the finite averaging and occupancy argument in `lem:seed`.
All expectations are explicit unnormalized sums over a nonempty finite seed
set. Rational arithmetic suffices because the paper's occupancies and their
means are rational.

The second-moment estimates are hypotheses of the balance theorem. They are
not assumed existence of a balanced seed. The affine-family section proves
pairwise uniformity by equal fiber cardinalities. Deriving the exact incidence
second moments and compiling a seed-search machine are separate obligations.
-/

namespace NtimeDspace.HashSchedules

open scoped BigOperators

section Affine

variable {Input Output K : Type*} [Fintype Input] [Field K]

/-- A seed is the full coefficient matrix and an independent offset vector. -/
abbrev AffineSeed (Input Output K : Type*) :=
  (Output → Input → K) × (Output → K)

/-- The actual affine hash family `x ↦ Γx + θ`. -/
def affineEval (seed : AffineSeed Input Output K) (input : Input → K) : Output → K :=
  fun output => (∑ coordinate, seed.1 output coordinate * input coordinate) + seed.2 output

theorem affineEval_add (first second : AffineSeed Input Output K) (input : Input → K) :
    affineEval (first + second) input = affineEval first input + affineEval second input := by
  funext output
  simp only [affineEval, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    add_mul, Finset.sum_add_distrib]
  ring

/-- Evaluation at two fixed inputs is additive as a function of the seed. -/
def affinePairHom (firstInput secondInput : Input → K) :
    AffineSeed Input Output K →+ ((Output → K) × (Output → K)) where
  toFun seed := (affineEval seed firstInput, affineEval seed secondInput)
  map_zero' := by
    ext output <;> simp [affineEval]
  map_add' first second := by
    simp [affineEval_add]

/-- For any two distinct inputs, every ordered pair of output vectors has a
seed. The proof solves for one matrix column and the offset explicitly. -/
theorem affinePairHom_surjective (firstInput secondInput : Input → K)
    (distinct : firstInput ≠ secondInput) :
    Function.Surjective (affinePairHom (Output := Output) firstInput secondInput) := by
  classical
  have hdifferent : ∃ coordinate, firstInput coordinate ≠ secondInput coordinate := by
    by_contra h
    push_neg at h
    exact distinct (funext h)
  obtain ⟨pivot, hpivot⟩ := hdifferent
  have hpivot_nonzero : secondInput pivot - firstInput pivot ≠ 0 :=
    sub_ne_zero.mpr hpivot.symm
  intro desired
  let slope : Output → K := fun output =>
    (desired.2 output - desired.1 output) / (secondInput pivot - firstInput pivot)
  let seed : AffineSeed Input Output K :=
    (fun output coordinate => if coordinate = pivot then slope output else 0,
      fun output => desired.1 output - slope output * firstInput pivot)
  refine ⟨seed, ?_⟩
  apply Prod.ext
  · funext output
    change affineEval seed firstInput output = desired.1 output
    simp [affineEval, seed]
  · funext output
    change affineEval seed secondInput output = desired.2 output
    have hslope : slope output * (secondInput pivot - firstInput pivot) =
        desired.2 output - desired.1 output :=
      div_mul_cancel₀ _ hpivot_nonzero
    simp only [affineEval, seed]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linear_combination hslope

/-- Every ordered pair of values occurs equally often when the affine seed is
uniform on a finite field. Thus distinct inputs have independent uniform
outputs. The equality is of actual seed-fiber cardinalities, not a probabilistic
independence assumption. -/
theorem affine_pair_fiber_card_eq [Fintype Output] [Fintype K]
    (firstInput secondInput : Input → K) (distinct : firstInput ≠ secondInput)
    (firstValues secondValues : (Output → K) × (Output → K)) :
    Nat.card {seed : AffineSeed Input Output K //
      affinePairHom firstInput secondInput seed = firstValues} =
    Nat.card {seed : AffineSeed Input Output K //
      affinePairHom firstInput secondInput seed = secondValues} := by
  exact Nat.card_congr (AddMonoidHom.fiberEquivOfSurjective
    (affinePairHom_surjective firstInput secondInput distinct) firstValues secondValues)

/-- The binary affine schedules used by the manuscript are an instance of the
proved finite-field family. -/
theorem binary_affine_pair_fiber_card_eq [Fintype Output]
    (firstInput secondInput : Input → ZMod 2) (distinct : firstInput ≠ secondInput)
    (firstValues secondValues : (Output → ZMod 2) × (Output → ZMod 2)) :
    Nat.card {seed : AffineSeed Input Output (ZMod 2) //
      affinePairHom firstInput secondInput seed = firstValues} =
    Nat.card {seed : AffineSeed Input Output (ZMod 2) //
      affinePairHom firstInput secondInput seed = secondValues} :=
  affine_pair_fiber_card_eq firstInput secondInput distinct firstValues secondValues

/-- A binary seed has exactly one bit per matrix entry and offset entry. This
is a cardinality statement, not an implementation or work-tape-space bound. -/
theorem binary_affine_seed_card [Fintype Output] :
    Nat.card (AffineSeed Input Output (ZMod 2)) =
      2 ^ (Fintype.card Output * (Fintype.card Input + 1)) := by
  classical
  simp only [Nat.card_eq_fintype_card, AffineSeed,
    Fintype.card_prod, Fintype.card_fun, ZMod.card]
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

end Affine

/-- Two nonnegative quantities with bounded finite uniform expectations admit
one seed simultaneously within twice both bounds. The proof averages their
weighted sum, rather than separately choosing two seeds. -/
theorem exists_simultaneous_bounds {Seed : Type*} (seeds : Finset Seed)
    (nonempty : seeds.Nonempty) (first second : Seed → ℚ) (A B : ℚ)
    (A_positive : 0 < A) (B_positive : 0 < B)
    (first_nonnegative : ∀ seed ∈ seeds, 0 ≤ first seed)
    (second_nonnegative : ∀ seed ∈ seeds, 0 ≤ second seed)
    (first_sum : ∑ seed ∈ seeds, first seed ≤ seeds.card * A)
    (second_sum : ∑ seed ∈ seeds, second seed ≤ seeds.card * B) :
    ∃ seed ∈ seeds, first seed ≤ 2 * A ∧ second seed ≤ 2 * B := by
  have hweighted :
      (∑ seed ∈ seeds, (B * first seed + A * second seed)) ≤
        ∑ _seed ∈ seeds, 2 * A * B := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hfirst := mul_le_mul_of_nonneg_left first_sum B_positive.le
    have hsecond := mul_le_mul_of_nonneg_left second_sum A_positive.le
    nlinarith
  obtain ⟨seed, hseed, hscore⟩ := Finset.exists_le_of_sum_le nonempty hweighted
  refine ⟨seed, hseed, ?_, ?_⟩
  · apply (mul_le_mul_iff_right₀ B_positive).mp
    have hnonnegative := mul_nonneg A_positive.le (second_nonnegative seed hseed)
    nlinarith
  · apply (mul_le_mul_iff_right₀ A_positive).mp
    have hnonnegative := mul_nonneg B_positive.le (first_nonnegative seed hseed)
    nlinarith

/-- Squared deviation across a finite family of buckets. -/
def squaredDeviation {Bucket : Type*} (buckets : Finset Bucket)
    (occupancy : Bucket → ℚ) (mean : ℚ) : ℚ :=
  ∑ bucket ∈ buckets, (occupancy bucket - mean) ^ 2

theorem squaredDeviation_nonnegative {Bucket : Type*} (buckets : Finset Bucket)
    (occupancy : Bucket → ℚ) (mean : ℚ) :
    0 ≤ squaredDeviation buckets occupancy mean :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem deviation_square_le {Bucket : Type*} (buckets : Finset Bucket)
    (occupancy : Bucket → ℚ) (mean : ℚ) (bucket : Bucket) (included : bucket ∈ buckets) :
    (occupancy bucket - mean) ^ 2 ≤ squaredDeviation buckets occupancy mean := by
  unfold squaredDeviation
  exact Finset.single_le_sum (f := fun b => (occupancy b - mean) ^ 2)
    (fun b _ => sq_nonneg (occupancy b - mean)) included

/-- A point within one mean's squared distance of a nonnegative mean cannot
exceed twice that mean. -/
theorem le_twice_mean_of_square_le (occupancy mean : ℚ) (mean_nonnegative : 0 ≤ mean)
    (deviation_bound : (occupancy - mean) ^ 2 ≤ mean ^ 2) :
    occupancy ≤ 2 * mean := by
  by_contra h
  have hgap : 0 < occupancy - 2 * mean := by linarith
  have hoccupancy : 0 < occupancy := by linarith
  have hproduct := mul_pos hoccupancy hgap
  nlinarith

/-- Converts the manuscript's parameter inequality and a squared-deviation
bound into the desired per-bucket occupancy bound, without using square roots. -/
theorem occupancy_bound_of_variance (occupancy mass buckets scale : ℚ)
    (mass_nonnegative : 0 ≤ mass) (buckets_positive : 0 < buckets)
    (parameter_bound : scale * buckets ^ 2 ≤ mass)
    (variance_bound : (occupancy - mass / buckets) ^ 2 ≤ scale * mass) :
    occupancy ≤ 2 * mass / buckets := by
  have hscaled : scale * mass * buckets ^ 2 ≤ mass ^ 2 := by
    have h := mul_le_mul_of_nonneg_left parameter_bound mass_nonnegative
    nlinarith
  have hvariance : scale * mass ≤ (mass / buckets) ^ 2 := by
    rw [div_pow]
    exact (le_div_iff₀ (sq_pos_of_pos buckets_positive)).mpr hscaled
  have h := le_twice_mean_of_square_le occupancy (mass / buckets)
    (div_nonneg mass_nonnegative buckets_positive.le) (variance_bound.trans hvariance)
  simpa only [mul_div_assoc] using h

/-- The complete averaging-and-balance step in Lemma `seed`.

`labels` indexes incidence labels. `nodeGroups` indexes pairs `(node, group)`.
The two displayed sum assumptions are exactly the bounds `E Δ ≤ 6M` and
`E Δ' ≤ QN` after multiplication by the number of equally likely seeds.
The theorem concludes existence of one seed satisfying both occupancy bounds.
No assumption asserts that a good seed already exists.
-/
theorem exists_balanced_seed {Seed Label NodeGroup : Type*}
    (seeds : Finset Seed) (nonempty : seeds.Nonempty)
    (labels : Finset Label) (nodeGroups : Finset NodeGroup)
    (incidences : Seed → Label → ℚ) (groupOccupancy : Seed → NodeGroup → ℚ)
    (M D Q N r : ℚ)
    (M_positive : 0 < M) (D_positive : 0 < D) (Q_positive : 0 < Q)
    (N_positive : 0 < N) (r_positive : 0 < r)
    (incidence_parameter : 12 * D ^ 2 ≤ M)
    (group_parameter : 2 * Q * r ^ 2 ≤ N)
    (incidence_moment :
      ∑ seed ∈ seeds, squaredDeviation labels (incidences seed) (M / D) ≤
        seeds.card * (6 * M))
    (group_moment :
      ∑ seed ∈ seeds, squaredDeviation nodeGroups (groupOccupancy seed) (N / r) ≤
        seeds.card * (Q * N)) :
    ∃ seed ∈ seeds,
      (∀ label ∈ labels, incidences seed label ≤ 2 * M / D) ∧
      (∀ nodeGroup ∈ nodeGroups, groupOccupancy seed nodeGroup ≤ 2 * N / r) := by
  obtain ⟨seed, hseed, hincidence, hgroup⟩ := exists_simultaneous_bounds seeds nonempty
    (fun seed => squaredDeviation labels (incidences seed) (M / D))
    (fun seed => squaredDeviation nodeGroups (groupOccupancy seed) (N / r))
    (6 * M) (Q * N) (by positivity) (mul_pos Q_positive N_positive)
    (fun _ _ => squaredDeviation_nonnegative _ _ _)
    (fun _ _ => squaredDeviation_nonnegative _ _ _) incidence_moment group_moment
  refine ⟨seed, hseed, ?_, ?_⟩
  · intro label hlabel
    apply occupancy_bound_of_variance _ M D 12 M_positive.le D_positive incidence_parameter
    have h := (deviation_square_le labels (incidences seed) (M / D) label hlabel).trans hincidence
    nlinarith
  · intro nodeGroup hnodeGroup
    apply occupancy_bound_of_variance _ N r (2 * Q) N_positive.le r_positive group_parameter
    have h := (deviation_square_le nodeGroups (groupOccupancy seed) (N / r) nodeGroup hnodeGroup).trans hgroup
    nlinarith

end NtimeDspace.HashSchedules
