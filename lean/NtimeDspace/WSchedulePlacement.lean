import NtimeDspace.SchedulePlacement
import NtimeDspace.WGroupedCounter
import NtimeDspace.WHashVariance

/-!
# Affine schedules and ranked placement for weighted constraint systems

The CNF version (`SchedulePlacement`) adds a dummy incidence for each unused
variable and uses degree-three occurrence bounds. For a weighted constraint
system the incidences are the actual scope positions; variables may occur in at
most `a` incidences and constraints may have at most `b` of them. The schedules
are the same affine hashes of binary identifiers, the labels are the same node
blocks, and each incidence's copy is its rank among earlier incidences with the
same label. The resulting grouped counter recovers the weighted count.
-/

namespace NtimeDspace.WSchedulePlacement

noncomputable section

open scoped BigOperators
open HashSchedules SchedulePlacement WeightedSystem

variable {n : ℕ} {Node : Type*} [Fintype Node] [DecidableEq Node]

def inputBits (S : System n) : ℕ := identifierBits n S.constraints.length

def variableCode (S : System n) : Fin n → Fin (inputBits S) → ZMod 2 :=
  binaryCode ((Nat.le_max_left _ _).trans (identifier_capacity _ _))

def factorCode (S : System n) : Fin S.constraints.length → Fin (inputBits S) → ZMod 2 :=
  binaryCode ((Nat.le_max_right _ _).trans (identifier_capacity _ _))

theorem variableCode_injective (S : System n) : Function.Injective (variableCode S) :=
  binaryCode_injective _

theorem factorCode_injective (S : System n) : Function.Injective (factorCode S) :=
  binaryCode_injective _

abbrev Seed (S : System n) (Node : Type*) (bits : ℕ) :=
  AffineSeed (Fin (inputBits S)) (Node × Fin bits) (ZMod 2) ×
    AffineSeed (Fin (inputBits S)) (Node × Fin bits) (ZMod 2)

def variableGroup (S : System n) (bits : ℕ) (seed : Seed S Node bits)
    (node : Node) (v : Fin n) : Fin (2 ^ bits) :=
  (binaryEquiv bits).symm (fun bit => affineEval seed.1 (variableCode S v) (node, bit))

def constraintGroup (S : System n) (bits : ℕ) (seed : Seed S Node bits)
    (node : Node) (e : Fin S.constraints.length) : Fin (2 ^ bits) :=
  (binaryEquiv bits).symm (fun bit => affineEval seed.2 (factorCode S e) (node, bit))

def rawLabel (S : System n) (bits : ℕ) (seed : Seed S Node bits) :
    Incidence S → RawLabel Node bits :=
  HashVariance.productHash affineEval affineEval
    (variableCode S ∘ incidenceVariable S) (factorCode S ∘ fun inc => inc.1) seed

def incidenceLabel (S : System n) (bits : ℕ) (seed : Seed S Node bits) :
    Incidence S → SchedulePlacement.Label Node bits :=
  labelEquiv Node bits ∘ rawLabel S bits seed

theorem card_incidence (S : System n) : Fintype.card (Incidence S) = incidenceCount S := by
  simp [Incidence, incidenceCount, Fintype.card_sigma]

/-- Simultaneous bucket and group bounds. -/
def Balanced (S : System n) (bits : ℕ) (seed : Seed S Node bits) : Prop :=
  (∀ label, HashVariance.bucketCount (incidenceLabel S bits seed) label ≤
    2 * (incidenceCount S : ℚ) / (2 ^ bits) ^ (2 * Fintype.card Node)) ∧
  (∀ node group, HashVariance.bucketCount (variableGroup S bits seed node) group ≤
    2 * (n : ℚ) / 2 ^ bits)

/-- **A balanced schedule exists** for occurrence bound `a` and arity bound `b`. -/
theorem exists_balanced_schedule [Nonempty Node] (S : System n) (a b : ℚ)
    (degrees_positive : 0 < a + b)
    (occurrences : ∀ v, HashVariance.bucketCount (incidenceVariable S) v ≤ a)
    (arity : ∀ e, HashVariance.bucketCount (fun inc : Incidence S => inc.1) e ≤ b)
    (positive : 0 < n) (incidences_positive : 0 < incidenceCount S) (bits : ℕ)
    (incidence_parameter :
      2 * (a + b) * ((2 ^ bits : ℕ) ^ (2 * Fintype.card Node) : ℚ) ^ 2 ≤ incidenceCount S)
    (group_parameter : 2 * (Fintype.card Node : ℚ) * (2 ^ bits : ℕ) ^ 2 ≤ n) :
    ∃ seed : Seed S Node bits, Balanced S bits seed := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, positive⟩⟩
  let : Nonempty (Incidence S) :=
    Fintype.card_pos_iff.mp (by rw [card_incidence]; exact incidences_positive)
  have hincidence :
      2 * (a + b) * (Fintype.card (RawLabel Node bits) : ℚ) ^ 2 ≤
        Fintype.card (Incidence S) := by
    simpa only [label_card, card_incidence, Nat.cast_pow] using incidence_parameter
  have hgroup : 2 * (Fintype.card Node : ℚ) *
      (Fintype.card (Fin bits → ZMod 2) : ℚ) ^ 2 ≤ Fintype.card (Fin n) := by
    simpa using group_parameter
  obtain ⟨seed, labels, groups⟩ := WHashVariance.exists_balanced_affine_seed
    (Node := Node) (Bit := Fin bits)
    (incidenceVariable S) (fun inc : Incidence S => inc.1)
    (variableCode S) (factorCode S)
    (variableCode_injective S) (factorCode_injective S)
    a b degrees_positive occurrences arity hincidence hgroup
  refine ⟨seed, ?_, ?_⟩
  · intro label
    have same := HashVariance.bucketCount_comp_injective
      (rawLabel S bits seed) (labelEquiv Node bits) (labelEquiv Node bits).injective
      ((labelEquiv Node bits).symm label)
    simp only [Equiv.apply_symm_apply] at same
    change HashVariance.bucketCount (labelEquiv Node bits ∘ rawLabel S bits seed) label ≤ _
    rw [same]
    simpa only [rawLabel, label_card, card_incidence, Nat.cast_pow,
      Nat.cast_ofNat] using labels ((labelEquiv Node bits).symm label)
  · intro node group
    have same := HashVariance.bucketCount_comp_injective
      (fun v bit => affineEval seed.1 (variableCode S v) (node, bit))
      (binaryEquiv bits).symm (binaryEquiv bits).symm.injective (binaryEquiv bits group)
    simp only [Equiv.symm_apply_apply] at same
    change HashVariance.bucketCount ((binaryEquiv bits).symm ∘
      (fun v bit => affineEval seed.1 (variableCode S v) (node, bit))) group ≤ _
    rw [same]
    simpa using groups node (binaryEquiv bits group)

/-- The copy capacity. -/
def copyCount (S : System n) (Node : Type*) [Fintype Node] (bits : ℕ) : ℕ :=
  ⌊2 * (incidenceCount S : ℚ) / (2 ^ bits) ^ (2 * Fintype.card Node)⌋₊

omit [DecidableEq Node] in
theorem balanced_copy_bound (S : System n) (bits : ℕ) (seed : Seed S Node bits)
    (balanced : Balanced S bits seed) (label : SchedulePlacement.Label Node bits) :
    HashVariance.bucketCount (incidenceLabel S bits seed) label ≤ (copyCount S Node bits : ℚ) := by
  have h := balanced.1 label
  rw [← enumerated_bucket_card] at h ⊢
  have bound : (CanonicalPlacement.bucket
      (enumeratedLabel (incidenceLabel S bits seed)) label).card ≤ copyCount S Node bits :=
    (Nat.le_floor_iff (by positivity)).mpr h
  exact_mod_cast bound

omit [DecidableEq Node] in
/-- The copy-label slots number at most twice the incidences. -/
theorem copy_slots_le (S : System n) (bits : ℕ) :
    copyCount S Node bits * (2 ^ bits) ^ (2 * Fintype.card Node) ≤ 2 * incidenceCount S := by
  have bound := Nat.floor_le (show (0 : ℚ) ≤
    2 * (incidenceCount S : ℚ) / (2 ^ bits) ^ (2 * Fintype.card Node) by positivity)
  have multiplied := (le_div_iff₀
    (by positivity : (0 : ℚ) < (2 ^ bits) ^ (2 * Fintype.card Node))).mp bound
  change (copyCount S Node bits : ℚ) * (2 ^ bits) ^ (2 * Fintype.card Node) ≤
    2 * (incidenceCount S : ℚ) at multiplied
  exact_mod_cast multiplied

/-- An incidence's copy is its rank in its label bucket. -/
def incidenceCopy (S : System n) (bits : ℕ) (seed : Seed S Node bits)
    (balanced : Balanced S bits seed) : Incidence S → Fin (copyCount S Node bits) :=
  rankedCopy (incidenceLabel S bits seed) (copyCount S Node bits)
    (balanced_copy_bound S bits seed balanced)

omit [DecidableEq Node] in
theorem placement_injective (S : System n) (bits : ℕ) (seed : Seed S Node bits)
    (balanced : Balanced S bits seed) :
    Function.Injective (fun inc =>
      (incidenceCopy S bits seed balanced inc, incidenceLabel S bits seed inc)) :=
  rankedCopy_injective _ _ _

omit [Fintype Node] [DecidableEq Node] in
theorem variables_match (S : System n) (bits : ℕ) (seed : Seed S Node bits)
    (node : Node) (inc : Incidence S) :
    variableGroup S bits seed node (WIncidenceDeformation.incidenceVariable S inc) =
      (incidenceLabel S bits seed inc node).1 := rfl

omit [Fintype Node] [DecidableEq Node] in
theorem constraints_match (S : System n) (bits : ℕ) (seed : Seed S Node bits)
    (node : Node) (inc : Incidence S) :
    (incidenceLabel S bits seed inc node).2 = constraintGroup S bits seed node inc.1 := rfl

/-- **The grouped counter with the constructed schedules recovers the
weighted count.** Only balance and the interpolation parameters remain. -/
theorem grouped_counter_correct {p : ℕ} [Fact p.Prime]
    (S : System n) (fallback : Fin n) (bits : ℕ) (seed : Seed S Node bits)
    (balanced : Balanced S bits seed)
    (two_nonzero : (2 : ZMod p) ≠ 0)
    (nodeValue : Node → ZMod p) (distinct_nodes : Function.Injective nodeValue)
    (nonzero_nodes : ∀ node, nodeValue node ≠ 0)
    (start : ℤ) (width order : ℕ) (small : width < p)
    (positive_order : 0 < order) (below_prime : order < p)
    (interpolation_capacity : incidenceCount S * (width - 1) < Fintype.card Node * order)
    (no_alias : incidenceCount S * (width - 1) ≤ p - 2) :
    WGroupedCounter.groupedScalarExpression S fallback
      (incidenceCopy S bits seed balanced) (incidenceLabel S bits seed)
      (variableGroup S bits seed) (constraintGroup S bits seed)
      nodeValue start width order = (S.count : ZMod p) :=
  WGroupedCounter.groupedScalarExpression_correct S fallback
    (incidenceCopy S bits seed balanced) (incidenceLabel S bits seed)
    (placement_injective S bits seed balanced)
    (variableGroup S bits seed) (constraintGroup S bits seed)
    nodeValue distinct_nodes nonzero_nodes start width order
    (variables_match S bits seed) (constraints_match S bits seed)
    two_nonzero small positive_order below_prime interpolation_capacity no_alias

end

end NtimeDspace.WSchedulePlacement
