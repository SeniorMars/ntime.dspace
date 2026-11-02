import NtimeDspace.HashSchedules

/-!
# Finite collision counts and schedule variance

This file expands squared bucket deviations into ordered collision counts.
Uniform expectations are finite sums divided by the seed count; the stated
bounds are kept unnormalized to avoid unnecessary denominators.

It then derives the manuscript's `6M` incidence and `QN` variable-group bounds
for the concrete affine families. The incidence estimate assumes at most three
occurrences of each endpoint code; the group estimate assumes an injective
variable encoding. No collision-probability assumption remains in those final
affine-family theorems. No seed-search resource bound is claimed.
-/

namespace NtimeDspace.HashVariance

open scoped BigOperators
open HashSchedules

variable {Item Bucket Seed : Type*}

section Counts

variable [Fintype Item] [Fintype Bucket] [DecidableEq Bucket]

/-- The actual number of items assigned to a bucket, viewed in the rationals. -/
def bucketCount (hash : Item → Bucket) (bucket : Bucket) : ℚ :=
  ∑ item, if hash item = bucket then 1 else 0

theorem sum_bucketCount (hash : Item → Bucket) :
    (∑ bucket, bucketCount hash bucket) = Fintype.card Item := by
  unfold bucketCount
  rw [Finset.sum_comm]
  simp

omit [Fintype Bucket] in
/-- An injective vector encoding preserves the original occurrence counts. -/
theorem bucketCount_comp_injective {Encoded : Type*} [DecidableEq Encoded]
    (endpoint : Item → Bucket) (code : Bucket → Encoded) (injective_code : Function.Injective code)
    (bucket : Bucket) :
    bucketCount (code ∘ endpoint) (code bucket) = bucketCount endpoint bucket := by
  simp only [bucketCount, Function.comp_apply, injective_code.eq_iff]

/-- Squared occupancies count ordered pairs landing in the same bucket. -/
theorem sum_bucketCount_sq (hash : Item → Bucket) :
    (∑ bucket, (bucketCount hash bucket) ^ 2) =
      ∑ first, ∑ second, if hash first = hash second then (1 : ℚ) else 0 := by
  simp only [bucketCount, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro second _
  simp [eq_comm]

/-- The exact variance expansion in the manuscript's schedule argument. -/
theorem squaredDeviation_eq_collisions [Nonempty Bucket] (hash : Item → Bucket) :
    squaredDeviation Finset.univ (bucketCount hash)
        ((Fintype.card Item : ℚ) / Fintype.card Bucket) =
      (∑ first, ∑ second, if hash first = hash second then (1 : ℚ) else 0) -
        (Fintype.card Item : ℚ) ^ 2 / Fintype.card Bucket := by
  let mass : ℚ := Fintype.card Item
  let buckets : ℚ := Fintype.card Bucket
  have buckets_nonzero : buckets ≠ 0 := by
    dsimp [buckets]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm (bucket : Bucket) :
      (bucketCount hash bucket - mass / buckets) ^ 2 =
        (bucketCount hash bucket) ^ 2 -
          (2 * mass / buckets) * bucketCount hash bucket + (mass / buckets) ^ 2 := by ring
  change (∑ bucket, (bucketCount hash bucket - mass / buckets) ^ 2) = _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_bucketCount, sum_bucketCount_sq]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change _ - (2 * mass / buckets) * mass + buckets * (mass / buckets) ^ 2 =
    _ - mass ^ 2 / buckets
  field_simp
  ring

end Counts

section Moments

variable [Fintype Item] [Fintype Bucket] [DecidableEq Bucket] [Nonempty Bucket]
variable [Fintype Seed]

/-- Number of seeds for which two given items collide. -/
def collisionCount (hash : Seed → Item → Bucket) (first second : Item) : ℚ :=
  ∑ seed, if hash seed first = hash seed second then 1 else 0

omit [Fintype Item] [Fintype Bucket] [Nonempty Bucket] in
theorem collisionCount_le_card (hash : Seed → Item → Bucket) (first second : Item) :
    collisionCount hash first second ≤ Fintype.card Seed := by
  calc
    _ ≤ ∑ _seed : Seed, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro seed _
      split_ifs <;> norm_num
    _ = _ := by simp

/-- Expanding the finite expected variance and exchanging the seed/item sums. -/
theorem sum_squaredDeviation_eq_collisions (hash : Seed → Item → Bucket) :
    (∑ seed, squaredDeviation Finset.univ (bucketCount (hash seed))
      ((Fintype.card Item : ℚ) / Fintype.card Bucket)) =
      (∑ first, ∑ second, collisionCount hash first second) -
        Fintype.card Seed * ((Fintype.card Item : ℚ) ^ 2 / Fintype.card Bucket) := by
  simp_rw [squaredDeviation_eq_collisions]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_comm]
  rfl

/-- If every nonexceptional ordered pair has collision probability at most
`1 / card Bucket`, the expected squared deviation is at most the number of
exceptional ordered pairs. Their dependence is unrestricted. -/
theorem sum_squaredDeviation_le_exceptional
    (hash : Seed → Item → Bucket) (exceptional : Item → Item → Prop)
    [DecidableRel exceptional]
    (ordinary_collision : ∀ first second, ¬ exceptional first second →
      collisionCount hash first second ≤ (Fintype.card Seed : ℚ) / Fintype.card Bucket) :
    (∑ seed, squaredDeviation Finset.univ (bucketCount (hash seed))
      ((Fintype.card Item : ℚ) / Fintype.card Bucket)) ≤
      Fintype.card Seed *
        ∑ first, ∑ second, if exceptional first second then (1 : ℚ) else 0 := by
  let seedCount : ℚ := Fintype.card Seed
  let bucketNumber : ℚ := Fintype.card Bucket
  have hpair (first second : Item) : collisionCount hash first second ≤
      seedCount / bucketNumber +
        seedCount * (if exceptional first second then 1 else 0) := by
    by_cases hexceptional : exceptional first second
    · rw [if_pos hexceptional, mul_one]
      have hbaseline : 0 ≤ seedCount / bucketNumber := by positivity
      have h := collisionCount_le_card hash first second
      change collisionCount hash first second ≤ seedCount at h
      linarith
    · rw [if_neg hexceptional, mul_zero, add_zero]
      exact ordinary_collision first second hexceptional
  have htotal := Finset.sum_le_sum (fun first (_ : first ∈ (Finset.univ : Finset Item)) =>
    Finset.sum_le_sum (fun second (_ : second ∈ (Finset.univ : Finset Item)) => hpair first second))
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum] at htotal
  rw [sum_squaredDeviation_eq_collisions]
  change _ - seedCount * ((Fintype.card Item : ℚ) ^ 2 / bucketNumber) ≤ _
  change _ ≤ (Fintype.card Item : ℚ) *
      ((Fintype.card Item : ℚ) * (seedCount / bucketNumber)) +
      seedCount * (∑ first, ∑ second, if exceptional first second then (1 : ℚ) else 0) at htotal
  have hbaseline : (Fintype.card Item : ℚ) *
      ((Fintype.card Item : ℚ) * (seedCount / bucketNumber)) =
      seedCount * ((Fintype.card Item : ℚ) ^ 2 / bucketNumber) := by ring
  rw [hbaseline] at htotal
  change _ ≤ seedCount * _
  linarith

end Moments

section UniformPairs

variable {Value : Type*} [Fintype Seed] [Fintype Value] [DecidableEq Value]

/-- The rational cardinality of one ordered-pair output fiber. -/
def pairFiberCount (pair : Seed → Value × Value) (values : Value × Value) : ℚ :=
  ∑ seed, if pair seed = values then 1 else 0

omit [Fintype Value] in
theorem pairFiberCount_eq_card (pair : Seed → Value × Value) (values : Value × Value) :
    pairFiberCount pair values = Nat.card {seed // pair seed = values} := by
  classical
  simp [pairFiberCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_pairFiberCount (pair : Seed → Value × Value) :
    (∑ values, pairFiberCount pair values) = Fintype.card Seed := by
  unfold pairFiberCount
  rw [Finset.sum_comm]
  simp

theorem sum_diagonal_pairFiberCount (pair : Seed → Value × Value) :
    (∑ value, pairFiberCount pair (value, value)) =
      ∑ seed, if (pair seed).1 = (pair seed).2 then (1 : ℚ) else 0 := by
  unfold pairFiberCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro seed _
  by_cases hequal : (pair seed).1 = (pair seed).2
  · have hp : pair seed = ((pair seed).1, (pair seed).1) := Prod.ext rfl hequal.symm
    rw [hp]
    simp
  · have hne (value : Value) : pair seed ≠ (value, value) := by
      intro h
      apply hequal
      rw [h]
    simp [hne, hequal]

/-- Equal ordered-pair fiber sizes imply the exact uniform collision law.
This connects combinatorial pairwise uniformity to the moment hypotheses. -/
theorem collision_sum_of_uniform_pairs [Nonempty Value] (pair : Seed → Value × Value)
    (uniform : ∀ first second, pairFiberCount pair first = pairFiberCount pair second) :
    (∑ seed, if (pair seed).1 = (pair seed).2 then (1 : ℚ) else 0) =
      (Fintype.card Seed : ℚ) / Fintype.card Value := by
  classical
  let chosen : Value := Classical.choice inferInstance
  let fiber : ℚ := pairFiberCount pair (chosen, chosen)
  have hcount := sum_pairFiberCount pair
  simp_rw [uniform _ (chosen, chosen)] at hcount
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_prod, Nat.cast_mul] at hcount
  change (Fintype.card Value : ℚ) * Fintype.card Value * fiber = Fintype.card Seed at hcount
  rw [← sum_diagonal_pairFiberCount]
  simp_rw [uniform _ (chosen, chosen)]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card Value : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (eq_div_iff hcard).mpr
  change ((Fintype.card Value : ℚ) * fiber) * Fintype.card Value = Fintype.card Seed
  calc
    _ = (Fintype.card Value : ℚ) * Fintype.card Value * fiber := by ring
    _ = _ := hcount

end UniformPairs

section AffineCollision

variable {Input Output K : Type*} [Fintype Input] [Fintype Output]
variable [DecidableEq Input] [DecidableEq Output] [Field K] [Fintype K] [DecidableEq K]

/-- The exact collision law for the concrete affine seed family already proved
pairwise uniform in `HashSchedules`. -/
theorem affine_collisionCount (firstInput secondInput : Input → K)
    (distinct : firstInput ≠ secondInput) :
    collisionCount (fun seed : AffineSeed Input Output K => affineEval seed)
        firstInput secondInput =
      (Fintype.card (AffineSeed Input Output K) : ℚ) / Fintype.card (Output → K) := by
  apply collision_sum_of_uniform_pairs
    (fun seed : AffineSeed Input Output K =>
      (affineEval seed firstInput, affineEval seed secondInput))
  intro firstValues secondValues
  rw [pairFiberCount_eq_card, pairFiberCount_eq_card]
  exact congrArg (fun n : ℕ => (n : ℚ))
    (affine_pair_fiber_card_eq firstInput secondInput distinct firstValues secondValues)

end AffineCollision

section IndependentFamilies

variable {FirstSeed SecondSeed FirstInput SecondInput FirstValue SecondValue : Type*}
variable [Fintype FirstSeed] [Fintype SecondSeed]
variable [DecidableEq FirstValue] [DecidableEq SecondValue]

/-- Independent schedules use the full Cartesian product of their seed sets. -/
def productHash (firstHash : FirstSeed → FirstInput → FirstValue)
    (secondHash : SecondSeed → SecondInput → SecondValue)
    (firstEndpoint : Item → FirstInput) (secondEndpoint : Item → SecondInput)
    (seed : FirstSeed × SecondSeed) (item : Item) : FirstValue × SecondValue :=
  (firstHash seed.1 (firstEndpoint item), secondHash seed.2 (secondEndpoint item))

/-- Collision counts factor exactly for independently chosen schedules. -/
theorem collisionCount_productHash
    (firstHash : FirstSeed → FirstInput → FirstValue)
    (secondHash : SecondSeed → SecondInput → SecondValue)
    (firstEndpoint : Item → FirstInput) (secondEndpoint : Item → SecondInput)
    (first second : Item) :
    collisionCount (productHash firstHash secondHash firstEndpoint secondEndpoint) first second =
      collisionCount firstHash (firstEndpoint first) (firstEndpoint second) *
        collisionCount secondHash (secondEndpoint first) (secondEndpoint second) := by
  unfold collisionCount productHash
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstSeed _
  apply Finset.sum_congr rfl
  intro secondSeed _
  by_cases hfirst : firstHash firstSeed (firstEndpoint first) =
      firstHash firstSeed (firstEndpoint second) <;>
    by_cases hsecond : secondHash secondSeed (secondEndpoint first) =
      secondHash secondSeed (secondEndpoint second) <;>
    simp [hfirst, hsecond, Prod.mk.injEq]

end IndependentFamilies

section Incidences

variable {Variable Factor : Type*} [Fintype Item]
variable [DecidableEq Variable] [DecidableEq Factor]

/-- If an incidence shares its variable with at most `a` incidences and its
factor with at most `b`, at most `(a+b)M` ordered pairs share either endpoint. -/
theorem exceptional_incidence_pairs_le (variableOf : Item → Variable) (factorOf : Item → Factor)
    (a b : ℚ)
    (variable_bound : ∀ incidence, bucketCount variableOf (variableOf incidence) ≤ a)
    (factor_bound : ∀ incidence, bucketCount factorOf (factorOf incidence) ≤ b) :
    (∑ first, ∑ second,
      if variableOf first = variableOf second ∨ factorOf first = factorOf second
      then (1 : ℚ) else 0) ≤ Fintype.card Item * (a + b) := by
  have hrow (first : Item) :
      (∑ second,
        if variableOf first = variableOf second ∨ factorOf first = factorOf second
        then (1 : ℚ) else 0) ≤ a + b := by
    calc
      _ ≤ ∑ second,
          ((if variableOf second = variableOf first then (1 : ℚ) else 0) +
            (if factorOf second = factorOf first then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro second _
        by_cases hv : variableOf first = variableOf second <;>
          by_cases hf : factorOf first = factorOf second <;>
          simp [hv, hf, eq_comm]
      _ = bucketCount variableOf (variableOf first) + bucketCount factorOf (factorOf first) := by
        rw [Finset.sum_add_distrib]
        rfl
      _ ≤ a + b := add_le_add (variable_bound first) (factor_bound first)
  calc
    _ ≤ ∑ _first : Item, (a + b) := Finset.sum_le_sum (fun first _ => hrow first)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

variable [Fintype Bucket] [DecidableEq Bucket] [Nonempty Bucket] [Fintype Seed]

/-- The incidence second-moment bound `E Δ ≤ 6M`, derived from degree-three
occurrence bounds and the exact ordinary-pair collision hypothesis. -/
theorem incidence_second_moment_le_six
    (hash : Seed → Item → Bucket) (variableOf : Item → Variable) (factorOf : Item → Factor)
    (variable_bound : ∀ incidence, bucketCount variableOf (variableOf incidence) ≤ 3)
    (factor_bound : ∀ incidence, bucketCount factorOf (factorOf incidence) ≤ 3)
    (ordinary_collision : ∀ first second,
      variableOf first ≠ variableOf second → factorOf first ≠ factorOf second →
        collisionCount hash first second ≤ (Fintype.card Seed : ℚ) / Fintype.card Bucket) :
    (∑ seed, squaredDeviation Finset.univ (bucketCount (hash seed))
      ((Fintype.card Item : ℚ) / Fintype.card Bucket)) ≤
      Fintype.card Seed * (6 * (Fintype.card Item : ℚ)) := by
  have hmoment := sum_squaredDeviation_le_exceptional hash
    (fun first second => variableOf first = variableOf second ∨ factorOf first = factorOf second)
    (fun first second h => ordinary_collision first second
      (fun hv => h (Or.inl hv)) (fun hf => h (Or.inr hf)))
  have hpairs := exceptional_incidence_pairs_le variableOf factorOf 3 3 variable_bound factor_bound
  have hscaled := mul_le_mul_of_nonneg_left hpairs
    (show (0 : ℚ) ≤ Fintype.card Seed by positivity)
  nlinarith

end Incidences

section GroupMoments

variable [Fintype Item] [Fintype Bucket] [DecidableEq Bucket] [Nonempty Bucket] [Fintype Seed]

/-- Pairwise uniform collision bounds suffice for `E Δ ≤ N`; only diagonal
ordered pairs are exceptional. -/
theorem pairwise_second_moment_le (hash : Seed → Item → Bucket)
    (distinct_collision : ∀ first second, first ≠ second →
      collisionCount hash first second ≤ (Fintype.card Seed : ℚ) / Fintype.card Bucket) :
    (∑ seed, squaredDeviation Finset.univ (bucketCount (hash seed))
      ((Fintype.card Item : ℚ) / Fintype.card Bucket)) ≤
      Fintype.card Seed * (Fintype.card Item : ℚ) := by
  classical
  simpa using sum_squaredDeviation_le_exceptional hash Eq distinct_collision

/-- Summing the per-node bound proves the manuscript's `E Δ' ≤ QN`. -/
theorem group_second_moment_le {Node : Type*} [Fintype Node]
    (hash : Seed → Node → Item → Bucket)
    (distinct_collision : ∀ node first second, first ≠ second →
      collisionCount (fun seed => hash seed node) first second ≤
        (Fintype.card Seed : ℚ) / Fintype.card Bucket) :
    (∑ seed, ∑ node, squaredDeviation Finset.univ (bucketCount (hash seed node))
      ((Fintype.card Item : ℚ) / Fintype.card Bucket)) ≤
      Fintype.card Seed * ((Fintype.card Node : ℚ) * Fintype.card Item) := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _node : Node, (Fintype.card Seed : ℚ) * Fintype.card Item :=
      Finset.sum_le_sum (fun node _ =>
        pairwise_second_moment_le (fun seed => hash seed node) (distinct_collision node))
    _ = _ := by simp; ring

end GroupMoments

section AffineIncidences

variable {Input Output K : Type*} [Fintype Item] [Fintype Input] [Fintype Output]
variable [DecidableEq Input] [DecidableEq Output] [Field K] [Fintype K] [DecidableEq K]

/-- The manuscript's incidence moment estimate for the actual two independent
affine schedules. Incidences sharing a variable or factor may be dependent;
the degree-three bounds account for all such pairs. `variableCode` and
`factorCode` are the finite-vector labels supplied to the schedules. -/
theorem affine_incidence_second_moment_le_six
    (variableCode factorCode : Item → Input → K)
    (variable_bound : ∀ incidence, bucketCount variableCode (variableCode incidence) ≤ 3)
    (factor_bound : ∀ incidence, bucketCount factorCode (factorCode incidence) ≤ 3) :
    (∑ seed : AffineSeed Input Output K × AffineSeed Input Output K,
      squaredDeviation Finset.univ
        (bucketCount (productHash affineEval affineEval variableCode factorCode seed))
        ((Fintype.card Item : ℚ) / Fintype.card ((Output → K) × (Output → K)))) ≤
      Fintype.card (AffineSeed Input Output K × AffineSeed Input Output K) *
        (6 * (Fintype.card Item : ℚ)) := by
  apply incidence_second_moment_le_six _ variableCode factorCode variable_bound factor_bound
  intro first second variables_distinct factors_distinct
  rw [collisionCount_productHash,
    affine_collisionCount (variableCode first) (variableCode second) variables_distinct,
    affine_collisionCount (factorCode first) (factorCode second) factors_distinct]
  simp only [Fintype.card_prod, Nat.cast_mul]
  exact le_of_eq (div_mul_div_comm _ _ _ _)

end AffineIncidences

section AffineGroups

variable {Input Node Bit K : Type*} [Fintype Input] [Field K]

/-- Restrict the affine matrix and offset to the block of rows for one node. -/
def projectedAffinePairHom (node : Node) (firstInput secondInput : Input → K) :
    AffineSeed Input (Node × Bit) K →+ ((Bit → K) × (Bit → K)) where
  toFun seed :=
    (fun bit => affineEval seed firstInput (node, bit),
      fun bit => affineEval seed secondInput (node, bit))
  map_zero' := by ext bit <;> simp [affineEval]
  map_add' first second := by
    apply Prod.ext <;> funext bit <;> simp [affineEval_add]

/-- A row-block projection retains pairwise surjectivity: extend either desired
block to a full output vector and use the concrete affine construction. -/
theorem projectedAffinePairHom_surjective (node : Node) (firstInput secondInput : Input → K)
    (distinct : firstInput ≠ secondInput) :
    Function.Surjective (projectedAffinePairHom (Bit := Bit) node firstInput secondInput) := by
  intro desired
  obtain ⟨seed, hseed⟩ := affinePairHom_surjective firstInput secondInput distinct
    ((fun coordinate : Node × Bit => desired.1 coordinate.2),
      (fun coordinate : Node × Bit => desired.2 coordinate.2))
  refine ⟨seed, ?_⟩
  apply Prod.ext
  · funext bit
    exact congrArg (fun pair => pair.1 (node, bit)) hseed
  · funext bit
    exact congrArg (fun pair => pair.2 (node, bit)) hseed

variable [Fintype Node] [Fintype Bit] [Fintype K]
variable [DecidableEq Input] [DecidableEq Node] [DecidableEq Bit] [DecidableEq K]

/-- Exact collision probability for a node's projected affine schedule, using
the entire common seed rather than fresh independent seeds at each node. -/
theorem projected_affine_collisionCount (node : Node) (firstInput secondInput : Input → K)
    (distinct : firstInput ≠ secondInput) :
    collisionCount
      (fun seed : AffineSeed Input (Node × Bit) K =>
        fun input bit => affineEval seed input (node, bit)) firstInput secondInput =
      (Fintype.card (AffineSeed Input (Node × Bit) K) : ℚ) / Fintype.card (Bit → K) := by
  apply collision_sum_of_uniform_pairs
    (fun seed : AffineSeed Input (Node × Bit) K =>
      (fun bit => affineEval seed firstInput (node, bit),
        fun bit => affineEval seed secondInput (node, bit)))
  intro firstValues secondValues
  rw [pairFiberCount_eq_card, pairFiberCount_eq_card]
  apply congrArg (fun n : ℕ => (n : ℚ))
  exact Nat.card_congr (AddMonoidHom.fiberEquivOfSurjective
    (projectedAffinePairHom_surjective node firstInput secondInput distinct) firstValues secondValues)

/-- The manuscript's `E Δ' ≤ QN` for the actual single affine variable schedule.
Only injectivity of the declared variables' vector encoding is assumed. -/
theorem affine_group_second_moment_le [Fintype Item]
    (variableCode : Item → Input → K) (injective_code : Function.Injective variableCode) :
    (∑ seed : AffineSeed Input (Node × Bit) K,
      squaredDeviation Finset.univ
        (fun nodeGroup : Node × (Bit → K) =>
          bucketCount (fun item bit => affineEval seed (variableCode item) (nodeGroup.1, bit))
            nodeGroup.2)
        ((Fintype.card Item : ℚ) / Fintype.card (Bit → K))) ≤
      Fintype.card (AffineSeed Input (Node × Bit) K) *
        ((Fintype.card Node : ℚ) * Fintype.card Item) := by
  have h := group_second_moment_le
    (fun seed : AffineSeed Input (Node × Bit) K =>
      fun node item bit => affineEval seed (variableCode item) (node, bit))
    (fun node first second hne =>
      (projected_affine_collisionCount node (variableCode first) (variableCode second)
        (fun heq => hne (injective_code heq))).le)
  simpa only [squaredDeviation, Fintype.sum_prod_type] using h

/-- Adding the independent factor-schedule seed multiplies every term of the
variable-schedule moment estimate by the same seed count. -/
theorem affine_joint_group_second_moment_le [Fintype Item]
    (variableCode : Item → Input → K) (injective_code : Function.Injective variableCode) :
    (∑ seed : AffineSeed Input (Node × Bit) K × AffineSeed Input (Node × Bit) K,
      squaredDeviation Finset.univ
        (fun nodeGroup : Node × (Bit → K) =>
          bucketCount (fun item bit => affineEval seed.1 (variableCode item) (nodeGroup.1, bit))
            nodeGroup.2)
        ((Fintype.card Item : ℚ) / Fintype.card (Bit → K))) ≤
      Fintype.card (AffineSeed Input (Node × Bit) K × AffineSeed Input (Node × Bit) K) *
        ((Fintype.card Node : ℚ) * Fintype.card Item) := by
  have h := affine_group_second_moment_le (Node := Node) (Bit := Bit) variableCode injective_code
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    Fintype.card_prod, Nat.cast_mul]
  have hscaled := mul_le_mul_of_nonneg_left h
    (show (0 : ℚ) ≤ Fintype.card (AffineSeed Input (Node × Bit) K) by positivity)
  simp only [Fintype.card_prod, Nat.cast_mul] at hscaled
  nlinarith

end AffineGroups

section BalancedAffineSchedules

variable {Incidence Variable Factor Input Node Bit K : Type*}
variable [Fintype Incidence] [Nonempty Incidence] [Fintype Variable] [Nonempty Variable]
variable [Fintype Input] [Fintype Node] [Nonempty Node] [Fintype Bit]
variable [Field K] [Fintype K]
variable [DecidableEq Variable] [DecidableEq Factor] [DecidableEq Input]
variable [DecidableEq Node] [DecidableEq Bit] [DecidableEq K]

/-- The algebraic existence assertion of the hashed-schedule lemma, now for
concrete affine schedules and with both moment bounds discharged.

The original incidence endpoints have degree at most three and are encoded
injectively as vectors. The finite field may in particular be `ZMod 2`.
The two parameter inequalities use the actual cardinalities of the node,
group, and joint-label spaces. No independence or expected-variance hypothesis
is assumed. This proves existence, without a machine or a space bound for
finding or representing the seed.
-/
theorem exists_balanced_affine_seed
    (variableOf : Incidence → Variable) (factorOf : Incidence → Factor)
    (variableCode : Variable → Input → K) (factorCode : Factor → Input → K)
    (variable_injective : Function.Injective variableCode)
    (factor_injective : Function.Injective factorCode)
    (variable_degree : ∀ variableIndex, bucketCount variableOf variableIndex ≤ 3)
    (factor_degree : ∀ factorIndex, bucketCount factorOf factorIndex ≤ 3)
    (incidence_parameter :
      12 * (Fintype.card (((Node × Bit) → K) × ((Node × Bit) → K)) : ℚ) ^ 2 ≤
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
  have incidence_moment := affine_incidence_second_moment_le_six
    (Output := Node × Bit) (variableCode ∘ variableOf) (factorCode ∘ factorOf)
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
  obtain ⟨seed, _, incidence_bound, group_bound⟩ := exists_balanced_seed
    Finset.univ Finset.univ_nonempty Finset.univ Finset.univ
    (fun seed => bucketCount (productHash affineEval affineEval
      (variableCode ∘ variableOf) (factorCode ∘ factorOf) seed))
    (fun seed (nodeGroup : Node × (Bit → K)) => bucketCount
      (fun variableIndex bit => affineEval seed.1 (variableCode variableIndex) (nodeGroup.1, bit))
      nodeGroup.2)
    (Fintype.card Incidence)
    (Fintype.card (((Node × Bit) → K) × ((Node × Bit) → K)))
    (Fintype.card Node) (Fintype.card Variable) (Fintype.card (Bit → K))
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    incidence_parameter group_parameter
    (by simpa only [Finset.card_univ] using incidence_moment)
    (by simpa only [Finset.card_univ] using group_moment)
  exact ⟨seed, fun label => incidence_bound label (Finset.mem_univ _),
    fun node group => group_bound (node, group) (Finset.mem_univ _)⟩

end BalancedAffineSchedules

end NtimeDspace.HashVariance
