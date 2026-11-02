import NtimeDspace.UniformSchedules
import NtimeDspace.AffineSeedEncoding
import NtimeDspace.SpectralIndexing

/-!
Explicit bounded search for a balanced pair of affine schedules. Each seed is
represented by one binary counter. The balance test scans all radix-encoded
labels and all node/group pairs, using scalar population counts and natural
cross-products. The decoder supplies seed bits on demand; no seed list, affine
matrix table, label list, or occupancy table is constructed.

The search is total, returning counter zero if no seed passes. Its balance
guarantee requires existence; the final theorems discharge that requirement
from the manuscript's integer parameter budget. These are functional results
and a bound on the seed counter, not a machine-time or machine-space theorem.
-/

namespace NtimeDspace.ScheduleSearch

open UniformSchedules

variable {n Q : ℕ}

/-- Test every tensor-label bucket and every variable group by bounded scalar
loops. Only comparisons of natural numbers occur in the test. -/
def test (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits) : Bool :=
  let population := PopulationAccess.populationCount formula
  GroupedInnerLoop.scanAll (fun mask : Fin (((2 ^ bits) * (2 ^ bits)) ^ Q) =>
    decide (RankedPopulationPlacement.bucketSize formula (incidenceLabel formula bits seed)
        (SpectralIndexing.label (2 ^ bits) Q (Nat.two_pow_pos bits) mask.val) *
      (2 ^ bits) ^ (2 * Q) ≤ 2 * population)) &&
  GroupedInnerLoop.scanAll (fun node : Fin Q =>
    GroupedInnerLoop.scanAll (fun group : Fin (2 ^ bits) =>
      decide (LocalAssignmentLoop.groupSize (variableGroup formula bits seed node) group *
        2 ^ bits ≤ 2 * n)))

theorem test_correct (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits) :
    test formula bits seed = true ↔ Balanced formula bits seed := by
  simp only [test, Bool.and_eq_true, GroupedInnerLoop.scanAll_correct, decide_eq_true_eq]
  constructor
  · rintro ⟨labels, groups⟩
    refine ⟨?_, groups⟩
    intro value
    obtain ⟨mask, same⟩ :=
      (SpectralIndexing.label_bijective (2 ^ bits) Q (Nat.two_pow_pos bits)).surjective value
    simpa only [same] using labels mask
  · rintro ⟨labels, groups⟩
    exact ⟨fun mask => labels _, groups⟩

/-- The exact number of joint affine-seed counters. -/
def seedCount (formula : Formula n) (Q bits : ℕ) : ℕ :=
  2 ^ AffineSeedEncoding.totalBits (PopulationAccess.inputBits formula) Q bits

theorem seedCount_pos (formula : Formula n) (Q bits : ℕ) : 0 < seedCount formula Q bits :=
  Nat.two_pow_pos _

/-- Decode an unrestricted natural candidate by reducing it to the fixed seed
width. No runtime proof guard or finite-family enumeration is needed. -/
def candidate (formula : Formula n) (Q bits mask : ℕ) : Seed formula Q bits :=
  AffineSeedEncoding.seedDecode
    ⟨mask % seedCount formula Q bits, Nat.mod_lt _ (seedCount_pos formula Q bits)⟩

theorem candidate_encode (formula : Formula n) (bits : ℕ) (seed : Seed formula Q bits) :
    candidate formula Q bits (AffineSeedEncoding.seedEncode seed).val = seed := by
  have within : (AffineSeedEncoding.seedEncode seed).val < seedCount formula Q bits :=
    (AffineSeedEncoding.seedEncode seed).isLt
  unfold candidate
  simp only [Nat.mod_eq_of_lt within]
  exact AffineSeedEncoding.seedDecode_encode seed

/-- A bounded descending search for a passing encoded seed. The predicate runs
the displayed scalar test, not a decidable universal proposition over seeds. -/
def selectedMask (formula : Formula n) (Q bits : ℕ) : ℕ :=
  Nat.findGreatest (fun mask => test formula bits (candidate formula Q bits mask) = true)
    (seedCount formula Q bits - 1)

theorem selectedMask_lt (formula : Formula n) (Q bits : ℕ) :
    selectedMask formula Q bits < seedCount formula Q bits := by
  have bound : selectedMask formula Q bits ≤ seedCount formula Q bits - 1 :=
    Nat.findGreatest_le _
  have positive := seedCount_pos formula Q bits
  omega

/-- Return affine coefficient accessors backed by the one selected counter. -/
def select (formula : Formula n) (Q bits : ℕ) : Seed formula Q bits :=
  candidate formula Q bits (selectedMask formula Q bits)

/-- Every existing balanced seed has an explicit encoding visited by the
bounded search, so the selected candidate passes the complete balance test. -/
theorem select_balanced (formula : Formula n) (bits : ℕ)
    (exists_seed : ∃ seed : Seed formula Q bits, Balanced formula bits seed) :
    Balanced formula bits (select formula Q bits) := by
  obtain ⟨seed, balanced⟩ := exists_seed
  have within : (AffineSeedEncoding.seedEncode seed).val ≤ seedCount formula Q bits - 1 := by
    have := (AffineSeedEncoding.seedEncode seed).isLt
    change (AffineSeedEncoding.seedEncode seed).val < seedCount formula Q bits at this
    omega
  have accepted : test formula bits
      (candidate formula Q bits (AffineSeedEncoding.seedEncode seed).val) = true := by
    rw [candidate_encode]
    exact (test_correct formula bits seed).mpr balanced
  apply (test_correct formula bits (select formula Q bits)).mp
  exact Nat.findGreatest_spec
    (P := fun mask => test formula bits (candidate formula Q bits mask) = true)
    (m := (AffineSeedEncoding.seedEncode seed).val) (n := seedCount formula Q bits - 1)
    within accepted

/-- Under the manuscript's two construction inequalities the explicitly
searched seed is balanced for the full literal-plus-dummy population. -/
theorem select_balanced_of_budgets (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (positive : 0 < n) (nodes_positive : 0 < Q)
    (bits : ℕ)
    (incidence_parameter : 12 * (((2 ^ bits) ^ (2 * Q) : ℕ) : ℚ) ^ 2 ≤
      FormulaIncidences.population formula)
    (group_parameter : 2 * (Q : ℚ) * ((2 ^ bits : ℕ) : ℚ) ^ 2 ≤ n) :
    Balanced formula bits (select formula Q bits) :=
  select_balanced formula bits
    (exists_balanced_schedule formula bounded positive nodes_positive bits
      incidence_parameter group_parameter)

/-- The single discrete log budget discharges both schedule-existence bounds;
no balanced seed is left as an assumption of this theorem. -/
theorem select_parameter_balanced (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (positive : 0 < n) (bits : ℕ)
    (six_le : 6 ≤ bits) (budget : ParameterChoice.cost bits ≤ n.log2) :
    Balanced formula bits (select formula (Parameters.Q bits) bits) := by
  apply select_balanced_of_budgets formula bounded positive
    (Parameters.Q_pos bits (by omega)) bits
  · have inequality := Parameters.construction_incidence_budget n
      (FormulaIncidences.population formula) bits six_le positive budget
      (FormulaIncidences.variables_le_population formula)
    simp only [Parameters.D, Parameters.s] at inequality
    exact_mod_cast inequality
  · have inequality := Parameters.construction_schedule_budget n bits six_le positive budget
    simp only [Parameters.s] at inequality
    exact_mod_cast inequality

/-- In the large-input branch, both the growing parameter and the affine seed
are obtained by explicit bounded searches. Small inputs remain a separate
branch of the final counting algorithm. -/
theorem select_chosen_balanced (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (positive : 0 < n)
    (large : ParameterChoice.cost 6 ≤ n.log2) :
    Balanced formula (ParameterChoice.choose n)
      (select formula (Parameters.Q (ParameterChoice.choose n)) (ParameterChoice.choose n)) :=
  select_parameter_balanced formula bounded positive (ParameterChoice.choose n)
    (ParameterChoice.six_le_selected n large) (ParameterChoice.admissible n)

end NtimeDspace.ScheduleSearch
