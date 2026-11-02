import NtimeDspace.FormulaIncidences
import NtimeDspace.CanonicalPlacement
import NtimeDspace.GroupedCounter
import NtimeDspace.ParameterChoice
import NtimeDspace.TailParameters

/-!
# Affine schedules and ranked incidence placement

Binary identifiers are the actual low-order bits of finite enumeration indices.
The affine schedules operate on the full incidence population, including dummy
incidences for unused declared variables. Their row blocks become the two
coordinates of the deformation labels. Each label bucket is placed by the
number of earlier equal-label incidences, as in `CanonicalPlacement`.

Finite enumeration and the existence of a balanced seed are mathematical
constructions here. No machine implementation or workspace bound is asserted.
-/

namespace NtimeDspace.SchedulePlacement

noncomputable section

open scoped BigOperators
open HashSchedules

/-- The actual binary digits of an index, represented in the binary field. -/
def binaryCode {size bits : ℕ} (_fits : size ≤ 2 ^ bits) (index : Fin size) :
    Fin bits → ZMod 2 :=
  fun bit => if index.val.testBit bit.val then 1 else 0

theorem binaryCode_injective {size bits : ℕ} (fits : size ≤ 2 ^ bits) :
    Function.Injective (binaryCode fits) := by
  intro first second same
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases inside : bit < bits
  · have equal := congrFun same ⟨bit, inside⟩
    change (if first.val.testBit bit then (1 : ZMod 2) else 0) =
      (if second.val.testBit bit then 1 else 0) at equal
    cases hf : first.val.testBit bit <;> cases hs : second.val.testBit bit <;>
      simp_all
  · have lower : bits ≤ bit := Nat.le_of_not_gt inside
    have hp : 2 ^ bits ≤ 2 ^ bit := Nat.pow_le_pow_right (by decide) lower
    rw [Nat.testBit_lt_two_pow (first.isLt.trans_le (fits.trans hp)),
      Nat.testBit_lt_two_pow (second.isLt.trans_le (fits.trans hp))]

/-- Binary vectors and ordinary group indices describe the same group set. -/
def binaryEquiv (bits : ℕ) : Fin (2 ^ bits) ≃ (Fin bits → ZMod 2) :=
  Equiv.ofBijective (binaryCode (Nat.le_refl (2 ^ bits)))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨binaryCode_injective _, by simp⟩)

def identifierBits (variableCount factorCount : ℕ) : ℕ :=
  (max variableCount factorCount).log2 + 1

theorem identifier_capacity (variableCount factorCount : ℕ) :
    max variableCount factorCount ≤ 2 ^ identifierBits variableCount factorCount := by
  exact Nat.lt_log2_self.le

variable {n : ℕ} {Node : Type*} [Fintype Node] [DecidableEq Node]

def inputBits (formula : Formula n) : ℕ :=
  identifierBits n (Fintype.card (FormulaIncidences.Factor formula))

def variableCode (formula : Formula n) : Fin n → Fin (inputBits formula) → ZMod 2 :=
  binaryCode ((Nat.le_max_left _ _).trans (identifier_capacity _ _))

def factorCode (formula : Formula n) :
    FormulaIncidences.Factor formula → Fin (inputBits formula) → ZMod 2 :=
  binaryCode ((Nat.le_max_right _ _).trans (identifier_capacity _ _)) ∘
    Fintype.equivFin (FormulaIncidences.Factor formula)

theorem variableCode_injective (formula : Formula n) :
    Function.Injective (variableCode formula) := binaryCode_injective _

theorem factorCode_injective (formula : Formula n) :
    Function.Injective (factorCode formula) :=
  (binaryCode_injective _).comp (Fintype.equivFin _).injective

private theorem clause_count_le (clauses : List (Clause n)) :
    clauses.length ≤ (clauses.map (fun clause => clause.literals.length)).sum +
      (clauses.filter (fun clause => clause.literals.isEmpty)).length := by
  induction clauses with
  | nil => simp
  | cons clause clauses ih =>
    cases h : clause.literals with
    | nil =>
      simp only [List.length_cons, List.map_cons, h, List.length_nil, List.sum_cons,
        zero_add, List.filter_cons, List.isEmpty_nil, ↓reduceIte, List.length_cons]
      omega
    | cons literal literals =>
      simp only [List.length_cons, List.map_cons, h, List.sum_cons, List.filter_cons,
        List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      omega

/-- The one permitted empty clause is the only factor not charged to an
incidence; dummy factors already have their own incidences. -/
theorem factor_count_le_population_add_one (formula : Formula n)
    (bounded : formula.BoundedOccurrence) :
    Fintype.card (FormulaIncidences.Factor formula) ≤ FormulaIncidences.population formula + 1 := by
  have h := clause_count_le formula.clauses
  rw [← FormulaIncidences.sum_positions_eq_list formula.clauses
    (fun clause => clause.literals.length)] at h
  change formula.clauses.length ≤ FormulaCounter.incidenceCount formula + _ at h
  have empties := bounded.2.1
  rw [FormulaIncidences.population_eq_literals_add_unused]
  simp only [FormulaIncidences.Factor, Fintype.card_sum, Fintype.card_fin]
  omega

/-- The actual identifiers have logarithmic length in the declared-variable
count, including the empty-clause and unused-variable conventions. -/
theorem inputBits_le (formula : Formula n) (bounded : formula.BoundedOccurrence) :
    inputBits formula ≤ (3 * n + 1).log2 + 1 := by
  have factors := (factor_count_le_population_add_one formula bounded).trans
    (Nat.add_le_add_right (FormulaIncidences.population_le_three_variables formula bounded) 1)
  have upper : max n (Fintype.card (FormulaIncidences.Factor formula)) ≤ 3 * n + 1 :=
    max_le (by omega) factors
  apply Nat.add_le_add_right
  apply (Nat.le_log2 (by omega : 3 * n + 1 ≠ 0)).mpr
  change 2 ^ (max n (Fintype.card (FormulaIncidences.Factor formula))).log2 ≤ 3 * n + 1
  by_cases hzero : max n (Fintype.card (FormulaIncidences.Factor formula)) = 0
  · rw [hzero]
    simp
  · exact (Nat.log2_self_le hzero).trans upper

abbrev Seed (formula : Formula n) (Node : Type*) (bits : ℕ) :=
  AffineSeed (Fin (inputBits formula)) (Node × Fin bits) (ZMod 2) ×
    AffineSeed (Fin (inputBits formula)) (Node × Fin bits) (ZMod 2)

abbrev RawLabel (Node : Type*) (bits : ℕ) :=
  ((Node × Fin bits) → ZMod 2) × ((Node × Fin bits) → ZMod 2)

abbrev Label (Node : Type*) (bits : ℕ) := Node → Fin (2 ^ bits) × Fin (2 ^ bits)

/-- Split the two output vectors into their node blocks and decode each block. -/
def labelEquiv (Node : Type*) (bits : ℕ) : RawLabel Node bits ≃ Label Node bits where
  toFun pair node :=
    ((binaryEquiv bits).symm (fun bit => pair.1 (node, bit)),
      (binaryEquiv bits).symm (fun bit => pair.2 (node, bit)))
  invFun label :=
    (fun coordinate => binaryEquiv bits (label coordinate.1).1 coordinate.2,
      fun coordinate => binaryEquiv bits (label coordinate.1).2 coordinate.2)
  left_inv pair := by
    apply Prod.ext <;> funext coordinate <;> rcases coordinate with ⟨node, bit⟩ <;>
      simp
  right_inv label := by
    funext node
    apply Prod.ext <;> simp

def variableGroup (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits)
    (node : Node) (variableIndex : Fin n) : Fin (2 ^ bits) :=
  (binaryEquiv bits).symm (fun bit => affineEval seed.1 (variableCode formula variableIndex) (node, bit))

def factorGroup (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits)
    (node : Node) (factor : FormulaIncidences.Factor formula) : Fin (2 ^ bits) :=
  (binaryEquiv bits).symm (fun bit => affineEval seed.2 (factorCode formula factor) (node, bit))

def rawLabel (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits) :
    FormulaIncidences.Incidence formula → RawLabel Node bits :=
  HashVariance.productHash affineEval affineEval
    (variableCode formula ∘ FormulaIncidences.variableOf formula)
    (factorCode formula ∘ FormulaIncidences.factorOf formula) seed

def incidenceLabel (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits) :
    FormulaIncidences.Incidence formula → Label Node bits :=
  labelEquiv Node bits ∘ rawLabel formula bits seed

omit [Fintype Node] [DecidableEq Node] in
theorem incidenceLabel_apply (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits)
    (incidence : FormulaIncidences.Incidence formula) (node : Node) :
    incidenceLabel formula bits seed incidence node =
      (variableGroup formula bits seed node (FormulaIncidences.variableOf formula incidence),
        factorGroup formula bits seed node (FormulaIncidences.factorOf formula incidence)) := rfl

theorem label_card (bits : ℕ) :
    Fintype.card (RawLabel Node bits) = (2 ^ bits) ^ (2 * Fintype.card Node) := by
  simp only [RawLabel, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← pow_add, ← pow_mul]
  congr 1
  ring

/-- The simultaneous bucket and group bounds, in the actual deformation
coordinates, for the full literal-plus-dummy population. -/
def Balanced (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits) : Prop :=
  (∀ label, HashVariance.bucketCount (incidenceLabel formula bits seed) label ≤
    2 * (FormulaIncidences.population formula : ℚ) / (2 ^ bits) ^ (2 * Fintype.card Node)) ∧
  (∀ node group, HashVariance.bucketCount (variableGroup formula bits seed node) group ≤
    2 * (n : ℚ) / 2 ^ bits)

theorem exists_balanced_schedule [Nonempty Node] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (positive : 0 < n) (bits : ℕ)
    (incidence_parameter :
      12 * ((2 ^ bits : ℕ) ^ (2 * Fintype.card Node) : ℚ) ^ 2 ≤
        FormulaIncidences.population formula)
    (group_parameter : 2 * (Fintype.card Node : ℚ) * (2 ^ bits : ℕ) ^ 2 ≤ n) :
    ∃ seed : Seed formula Node bits, Balanced formula bits seed := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, positive⟩⟩
  let : Nonempty (FormulaIncidences.Incidence formula) :=
    Fintype.card_pos_iff.mp (positive.trans_le (FormulaIncidences.variables_le_population formula))
  have hincidence :
      12 * (Fintype.card (RawLabel Node bits) : ℚ) ^ 2 ≤
        Fintype.card (FormulaIncidences.Incidence formula) := by
    simpa only [label_card, FormulaIncidences.population, Nat.cast_pow] using incidence_parameter
  have hgroup : 2 * (Fintype.card Node : ℚ) *
      (Fintype.card (Fin bits → ZMod 2) : ℚ) ^ 2 ≤ Fintype.card (Fin n) := by
    simpa using group_parameter
  obtain ⟨seed, labels, groups⟩ := HashVariance.exists_balanced_affine_seed
    (Node := Node) (Bit := Fin bits)
    (FormulaIncidences.variableOf formula) (FormulaIncidences.factorOf formula)
    (variableCode formula) (factorCode formula)
    (variableCode_injective formula) (factorCode_injective formula)
    (FormulaIncidences.variable_bucketCount_le_three formula bounded)
    (FormulaIncidences.factor_bucketCount_le_three formula)
    hincidence hgroup
  refine ⟨seed, ?_, ?_⟩
  · intro label
    have same := HashVariance.bucketCount_comp_injective
      (rawLabel formula bits seed) (labelEquiv Node bits) (labelEquiv Node bits).injective
      ((labelEquiv Node bits).symm label)
    simp only [Equiv.apply_symm_apply] at same
    change HashVariance.bucketCount (labelEquiv Node bits ∘ rawLabel formula bits seed) label ≤ _
    rw [same]
    simpa only [rawLabel, label_card, FormulaIncidences.population, Nat.cast_pow,
      Nat.cast_ofNat] using labels ((labelEquiv Node bits).symm label)
  · intro node group
    have same := HashVariance.bucketCount_comp_injective
      (fun variableIndex bit => affineEval seed.1 (variableCode formula variableIndex) (node, bit))
      (binaryEquiv bits).symm (binaryEquiv bits).symm.injective (binaryEquiv bits group)
    simp only [Equiv.symm_apply_apply] at same
    change HashVariance.bucketCount ((binaryEquiv bits).symm ∘
      (fun variableIndex bit => affineEval seed.1 (variableCode formula variableIndex) (node, bit))) group ≤ _
    rw [same]
    simpa using groups node (binaryEquiv bits group)

section RankedCopies

variable {Item Value : Type*} [Fintype Item] [DecidableEq Value]

/-- The population is enumerated once; copy ranks use this same order. -/
def enumeratedLabel (label : Item → Value) : Fin (Fintype.card Item) → Value :=
  label ∘ (Fintype.equivFin Item).symm

theorem enumerated_bucket_card (label : Item → Value) (value : Value) :
    ((CanonicalPlacement.bucket (enumeratedLabel label) value).card : ℚ) =
      HashVariance.bucketCount label value := by
  calc
    _ = ∑ index : Fin (Fintype.card Item),
        if enumeratedLabel label index = value then (1 : ℚ) else 0 := by
      simp only [CanonicalPlacement.bucket, Finset.card_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ = _ := (Fintype.equivFin Item).symm.sum_comp
      (fun item => if label item = value then (1 : ℚ) else 0)

def rankedCopy (label : Item → Value) (copies : ℕ)
    (occupancy : ∀ value, HashVariance.bucketCount label value ≤ (copies : ℚ)) : Item → Fin copies :=
  CanonicalPlacement.copyIndex (enumeratedLabel label) copies
    (fun value => by
      have h := occupancy value
      rw [← enumerated_bucket_card label value] at h
      exact_mod_cast h) ∘ Fintype.equivFin Item

theorem rankedCopy_injective (label : Item → Value) (copies : ℕ)
    (occupancy : ∀ value, HashVariance.bucketCount label value ≤ (copies : ℚ)) :
    Function.Injective (fun item => (rankedCopy label copies occupancy item, label item)) := by
  intro first second same
  apply (Fintype.equivFin Item).injective
  apply CanonicalPlacement.bounded_placement_injective (enumeratedLabel label) copies
    (fun value => by
      have h := occupancy value
      rw [← enumerated_bucket_card label value] at h
      exact_mod_cast h)
  simpa only [rankedCopy, enumeratedLabel, Function.comp_apply, Equiv.symm_apply_apply] using same

end RankedCopies

/-- Integer bucket occupancies fit the floor of the rational bound. Using the
floor also ensures that the total number of copy-label slots is at most `2M`. -/
def copyCount (formula : Formula n) (Node : Type*) [Fintype Node] (bits : ℕ) : ℕ :=
  ⌊2 * (FormulaIncidences.population formula : ℚ) /
    (2 ^ bits) ^ (2 * Fintype.card Node)⌋₊

omit [DecidableEq Node] in
theorem balanced_copy_bound (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits)
    (balanced : Balanced formula bits seed) (label : Label Node bits) :
    HashVariance.bucketCount (incidenceLabel formula bits seed) label ≤
      (copyCount formula Node bits : ℚ) := by
  have h := balanced.1 label
  rw [← enumerated_bucket_card] at h ⊢
  have bound : (CanonicalPlacement.bucket
      (enumeratedLabel (incidenceLabel formula bits seed)) label).card ≤
      copyCount formula Node bits :=
    (Nat.le_floor_iff (by positivity)).mpr h
  exact_mod_cast bound

omit [DecidableEq Node] in
/-- The integral copy capacity preserves `hD ≤ 2M`, without a divisibility
assumption on the incidence population. The label dimension is always positive. -/
theorem copy_slots_le (formula : Formula n) (bits : ℕ) :
    copyCount formula Node bits * (2 ^ bits) ^ (2 * Fintype.card Node) ≤
      2 * FormulaIncidences.population formula := by
  have bound := Nat.floor_le (show (0 : ℚ) ≤
    2 * (FormulaIncidences.population formula : ℚ) /
      (2 ^ bits) ^ (2 * Fintype.card Node) by positivity)
  have multiplied := (le_div_iff₀
    (by positivity : (0 : ℚ) < (2 ^ bits) ^ (2 * Fintype.card Node))).mp bound
  change (copyCount formula Node bits : ℚ) * (2 ^ bits) ^ (2 * Fintype.card Node) ≤
    2 * (FormulaIncidences.population formula : ℚ) at multiplied
  exact_mod_cast multiplied

/-- The exact occupancy input expected by the parameterized spectral-tail
row-count theorem. -/
theorem parameter_copy_occupancy (formula : Formula n) (bits : ℕ) :
    copyCount formula (Fin (Parameters.Q bits)) bits * Parameters.D bits ≤
      2 * FormulaIncidences.population formula := by
  simpa only [Fintype.card_fin, Parameters.D, Parameters.s] using
    copy_slots_le (Node := Fin (Parameters.Q bits)) formula bits

/-- D3's row budget for the actual rounded copy capacity; its occupancy premise
is now proved rather than supplied by the caller. -/
theorem measurementRow_scaled (formula : Formula n) (bounded : formula.BoundedOccurrence)
    (bits : ℕ) (positive : 0 < bits) :
    Fintype.card (TailParameters.MeasurementRow bits
      (copyCount formula (Fin (Parameters.Q bits)) bits)) * Parameters.s bits ^ 4 ≤ 2 * n :=
  TailParameters.measurementRow_scaled bits _ (FormulaIncidences.population formula) n positive
    (parameter_copy_occupancy formula bits)
    (FormulaIncidences.population_le_three_variables formula bounded)

/-- An incidence's copy is its explicit predecessor rank in its label bucket. -/
def incidenceCopy (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits)
    (balanced : Balanced formula bits seed) :
    FormulaIncidences.Incidence formula → Fin (copyCount formula Node bits) :=
  rankedCopy (incidenceLabel formula bits seed) (copyCount formula Node bits)
    (balanced_copy_bound formula bits seed balanced)

omit [DecidableEq Node] in
theorem incidence_placement_injective (formula : Formula n) (bits : ℕ)
    (seed : Seed formula Node bits) (balanced : Balanced formula bits seed) :
    Function.Injective (fun incidence =>
      (incidenceCopy formula bits seed balanced incidence, incidenceLabel formula bits seed incidence)) :=
  rankedCopy_injective _ _ _

def literalCopy (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits)
    (balanced : Balanced formula bits seed) :
    FormulaCounter.Incidence formula → Fin (copyCount formula Node bits) :=
  incidenceCopy formula bits seed balanced ∘ Sum.inl

def literalLabel (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits) :
    FormulaCounter.Incidence formula → Label Node bits :=
  incidenceLabel formula bits seed ∘ Sum.inl

def clauseGroup (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits)
    (node : Node) : Fin formula.clauses.length → Fin (2 ^ bits) :=
  factorGroup formula bits seed node ∘ Sum.inl

omit [DecidableEq Node] in
theorem literal_placement_injective (formula : Formula n) (bits : ℕ)
    (seed : Seed formula Node bits) (balanced : Balanced formula bits seed) :
    Function.Injective (fun incidence =>
      (literalCopy formula bits seed balanced incidence, literalLabel formula bits seed incidence)) :=
  (incidence_placement_injective formula bits seed balanced).comp Sum.inl_injective

omit [Fintype Node] [DecidableEq Node] in
theorem variables_match (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits)
    (node : Node) (incidence : FormulaCounter.Incidence formula) :
    variableGroup formula bits seed node (IncidenceDeformation.incidenceVariable formula incidence) =
      (literalLabel formula bits seed incidence node).1 := rfl

omit [Fintype Node] [DecidableEq Node] in
theorem clauses_match (formula : Formula n) (bits : ℕ) (seed : Seed formula Node bits)
    (node : Node) (incidence : FormulaCounter.Incidence formula) :
    (literalLabel formula bits seed incidence node).2 =
      clauseGroup formula bits seed node incidence.1 := rfl

/-- The combined counter now uses derived placement and schedule compatibility.
Only balance and the scalar interpolation parameters remain as inputs. -/
theorem grouped_counter_correct {p : ℕ} [Fact p.Prime]
    (formula : Formula n) (fallback : Fin n) (bits : ℕ) (seed : Seed formula Node bits)
    (balanced : Balanced formula bits seed)
    (two_nonzero : (2 : ZMod p) ≠ 0)
    (nodeValue : Node → ZMod p) (distinct_nodes : Function.Injective nodeValue)
    (nonzero_nodes : ∀ node, nodeValue node ≠ 0)
    (start : ℤ) (width order : ℕ) (small : width < p)
    (positive_order : 0 < order) (below_prime : order < p)
    (interpolation_capacity : FormulaCounter.incidenceCount formula * (width - 1) <
      Fintype.card Node * order)
    (no_alias : FormulaCounter.incidenceCount formula * (width - 1) ≤ p - 2) :
    GroupedCounter.groupedScalarExpression formula fallback
      (literalCopy formula bits seed balanced) (literalLabel formula bits seed)
      (variableGroup formula bits seed) (clauseGroup formula bits seed)
      nodeValue start width order = (satisfyingCount formula : ZMod p) := by
  exact GroupedCounter.groupedScalarExpression_correct formula fallback
    (literalCopy formula bits seed balanced) (literalLabel formula bits seed)
    (literal_placement_injective formula bits seed balanced)
    (variableGroup formula bits seed) (clauseGroup formula bits seed)
    nodeValue distinct_nodes nonzero_nodes start width order
    (variables_match formula bits seed) (clauses_match formula bits seed)
    two_nonzero small positive_order below_prime interpolation_capacity no_alias

/-- The manuscript's integer parameter budget discharges both simultaneous
balance inequalities for the normalized formula population. -/
theorem exists_parameter_schedule (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (positive : 0 < n) (bits : ℕ)
    (six_le : 6 ≤ bits)
    (budget : ParameterChoice.cost bits ≤ n.log2) :
    ∃ seed : Seed formula (Fin (Parameters.Q bits)) bits,
      Balanced formula bits seed := by
  let : Nonempty (Fin (Parameters.Q bits)) :=
    ⟨⟨0, Parameters.Q_pos bits (by omega)⟩⟩
  apply exists_balanced_schedule formula bounded positive bits
  · have h := Parameters.construction_incidence_budget n (FormulaIncidences.population formula)
      bits six_le positive budget (FormulaIncidences.variables_le_population formula)
    simp only [Parameters.D, Parameters.s] at h
    simp only [Fintype.card_fin]
    exact_mod_cast h
  · have h := Parameters.construction_schedule_budget n bits six_le positive budget
    simp only [Parameters.s] at h
    simp only [Fintype.card_fin]
    exact_mod_cast h

/-- In particular, the actual bounded parameter search has a balanced schedule
whenever its first admissible large-input case is available. -/
theorem exists_selected_schedule (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (positive : 0 < n)
    (large : ParameterChoice.cost 6 ≤ n.log2) :
    ∃ seed : Seed formula (Fin (Parameters.Q (ParameterChoice.choose n))) (ParameterChoice.choose n),
      Balanced formula (ParameterChoice.choose n) seed :=
  exists_parameter_schedule formula bounded positive (ParameterChoice.choose n)
    (ParameterChoice.six_le_selected n large) (ParameterChoice.admissible n)

/-- A complete finite-algebra existence bridge: the seed, incidence placement,
and grouping coordinates are constructed, rather than assumed independently. -/
theorem exists_correct_grouped_schedule {p : ℕ} [Fact p.Prime] [Nonempty Node]
    (formula : Formula n) (bounded : formula.BoundedOccurrence) (positive : 0 < n)
    (bits : ℕ)
    (incidence_parameter :
      12 * ((2 ^ bits : ℕ) ^ (2 * Fintype.card Node) : ℚ) ^ 2 ≤
        FormulaIncidences.population formula)
    (group_parameter : 2 * (Fintype.card Node : ℚ) * (2 ^ bits : ℕ) ^ 2 ≤ n)
    (two_nonzero : (2 : ZMod p) ≠ 0)
    (nodeValue : Node → ZMod p) (distinct_nodes : Function.Injective nodeValue)
    (nonzero_nodes : ∀ node, nodeValue node ≠ 0)
    (start : ℤ) (width order : ℕ) (small : width < p)
    (positive_order : 0 < order) (below_prime : order < p)
    (interpolation_capacity : FormulaCounter.incidenceCount formula * (width - 1) <
      Fintype.card Node * order)
    (no_alias : FormulaCounter.incidenceCount formula * (width - 1) ≤ p - 2) :
    ∃ seed : Seed formula Node bits, ∃ balanced : Balanced formula bits seed,
      GroupedCounter.groupedScalarExpression formula ⟨0, positive⟩
        (literalCopy formula bits seed balanced) (literalLabel formula bits seed)
        (variableGroup formula bits seed) (clauseGroup formula bits seed)
        nodeValue start width order = (satisfyingCount formula : ZMod p) := by
  obtain ⟨seed, balanced⟩ := exists_balanced_schedule formula bounded positive bits
    incidence_parameter group_parameter
  exact ⟨seed, balanced, grouped_counter_correct formula ⟨0, positive⟩ bits seed balanced
    two_nonzero nodeValue distinct_nodes nonzero_nodes start width order
    small positive_order below_prime interpolation_capacity no_alias⟩

end

end NtimeDspace.SchedulePlacement
