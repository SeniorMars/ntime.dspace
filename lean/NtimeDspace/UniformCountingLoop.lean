import NtimeDspace.ConcreteCountingLoop
import NtimeDspace.ScheduleSearch
import NtimeDspace.IntegerWindow
import NtimeDspace.SelectedCounter

/-!
The large-input scalar modular counter with internally selected parameters,
affine schedules, and ranked placement. All choices used by the executing
counter are bounded searches or integer arithmetic. The formula is supplied
as its ordered clause/literal data; no seed, placement, group map, polynomial
oracle, or real-valued endpoint is supplied by the caller.

The two proof arguments restrict this entry point to bounded-occurrence,
large inputs. Small inputs and the implementation and resource bounds of a
uniform Turing machine remain separate obligations.
-/

namespace NtimeDspace.UniformCountingLoop

open Parameters

variable {n : ℕ}

/-- Consecutive nonzero nodes, implemented by natural-number field casting. -/
def nodeValue {p nodes : ℕ} (node : Fin nodes) : ZMod p :=
  ((node.val + 1 : ℕ) : ZMod p)

theorem nodeValue_eq_selected {p nodes : ℕ} :
    nodeValue (p := p) (nodes := nodes) = SelectedCounter.nodeValue := rfl

/-- The seed is selected by testing explicit binary seed counters. -/
def chosenSeed (formula : Formula n) :
    UniformSchedules.Seed formula (Q (ParameterChoice.choose n)) (ParameterChoice.choose n) :=
  ScheduleSearch.select formula (Q (ParameterChoice.choose n)) (ParameterChoice.choose n)

theorem chosenSeed_balanced (formula : Formula n) (bounded : formula.BoundedOccurrence)
    (large : ParameterChoice.cost 6 ≤ n.log2) :
    UniformSchedules.Balanced formula (ParameterChoice.choose n) (chosenSeed formula) :=
  ScheduleSearch.select_chosen_balanced formula bounded (SelectedCounter.input_positive large) large

/-- The number of copies uses the scalar population count and natural division. -/
def copies (formula : Formula n) : ℕ :=
  RankedPopulationPlacement.copyCount formula (s (ParameterChoice.choose n))
    (Q (ParameterChoice.choose n))

theorem bucket_bound (formula : Formula n) (bounded : formula.BoundedOccurrence)
    (large : ParameterChoice.cost 6 ≤ n.log2)
    (value : TensorEvaluation.Label (s (ParameterChoice.choose n)) (Q (ParameterChoice.choose n))) :
    RankedPopulationPlacement.bucketSize formula
      (UniformSchedules.incidenceLabel formula (ParameterChoice.choose n) (chosenSeed formula)) value ≤
      copies formula :=
  RankedPopulationPlacement.balanced_bucket_bound formula _ (s_pos _)
    (chosenSeed_balanced formula bounded large).1 value

/-- Each literal's copy is its predecessor rank in the selected full-population
label bucket. The balancing proof is erased; no inverse table is executed. -/
def literalCopy (formula : Formula n) (bounded : formula.BoundedOccurrence)
    (large : ParameterChoice.cost 6 ≤ n.log2) :
    FormulaCounter.Incidence formula → Fin (copies formula) :=
  RankedPopulationPlacement.literalCopy formula
    (UniformSchedules.incidenceLabel formula (ParameterChoice.choose n) (chosenSeed formula))
    (copies formula) (bucket_bound formula bounded large)

theorem literal_placement_injective (formula : Formula n) (bounded : formula.BoundedOccurrence)
    (large : ParameterChoice.cost 6 ≤ n.log2) :
    Function.Injective (fun inc =>
      (literalCopy formula bounded large inc,
        UniformSchedules.literalLabel formula (ParameterChoice.choose n) (chosenSeed formula) inc)) :=
  RankedPopulationPlacement.literal_placement_injective formula _ _ (bucket_bound formula bounded large)

/-- The large-input scalar procedure has no externally supplied construction
maps. Its window endpoint uses only signed integer arithmetic. -/
def countModP (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (large : ParameterChoice.cost 6 ≤ n.log2) : ZMod p :=
  ConcreteCountingLoop.countModP p (s_pos (ParameterChoice.choose n)) formula
    (literalCopy formula bounded large)
    (UniformSchedules.literalLabel formula (ParameterChoice.choose n) (chosenSeed formula))
    (UniformSchedules.variableGroup formula (ParameterChoice.choose n) (chosenSeed formula))
    (UniformSchedules.clauseGroup formula (ParameterChoice.choose n) (chosenSeed formula))
    nodeValue (ParameterChoice.choose n) (IntegerWindow.start (ParameterChoice.choose n))
    (R (ParameterChoice.choose n))

/-- Functional correctness of the internally constructed scalar counter.
Only the input restriction, explicit large-input threshold, and prime lower
bound remain; no assumed schedule, accessor, or counting identity occurs. -/
theorem countModP_correct (p : ℕ) [Fact p.Prime] (formula : Formula n)
    (bounded : formula.BoundedOccurrence) (large : ParameterChoice.cost 6 ≤ n.log2)
    (prime_lower : 4 * n ^ 2 < p) :
    countModP p formula bounded large = (satisfyingCount formula : ZMod p) := by
  have positive := SelectedCounter.input_positive large
  have six_le := ParameterChoice.six_le_selected n large
  have selected_positive : 0 < ParameterChoice.choose n := by omega
  obtain ⟨nodes_small, width_small, order_small, degree_small⟩ :=
    scalar_parameter_bounds n (ParameterChoice.choose n) p six_le positive
      (ParameterChoice.admissible n) prime_lower
  have prime_large : 2 < p := by nlinarith
  have incidences : FormulaCounter.incidenceCount formula ≤ 3 * n :=
    (FormulaIncidences.literalCount_le_population formula).trans
      (FormulaIncidences.population_le_three_variables formula bounded)
  have degree : FormulaCounter.incidenceCount formula * (R (ParameterChoice.choose n) - 1) ≤
      3 * n * R (ParameterChoice.choose n) :=
    Nat.mul_le_mul incidences (Nat.sub_le _ _)
  have capacity := degree.trans_lt (degree_below_QJ n (ParameterChoice.choose n) selected_positive)
  unfold countModP
  exact ConcreteCountingLoop.countModP_correct p (s_pos _) (SelectedCounter.two_nonzero prime_large)
    formula ⟨0, positive⟩ (literalCopy formula bounded large)
    (UniformSchedules.literalLabel formula (ParameterChoice.choose n) (chosenSeed formula))
    (literal_placement_injective formula bounded large)
    (UniformSchedules.variableGroup formula (ParameterChoice.choose n) (chosenSeed formula))
    (UniformSchedules.clauseGroup formula (ParameterChoice.choose n) (chosenSeed formula))
    nodeValue (SelectedCounter.nodeValue_injective nodes_small)
    (SelectedCounter.nodeValue_nonzero nodes_small) (ParameterChoice.choose n) six_le
    (IntegerWindow.start (ParameterChoice.choose n)) (R (ParameterChoice.choose n)) width_small
    order_small (UniformSchedules.variables_match formula _ _) (UniformSchedules.clauses_match formula _ _)
    capacity (degree.trans degree_small)

end NtimeDspace.UniformCountingLoop
