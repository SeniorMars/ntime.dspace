import NtimeDspace.HermiteCoefficientMachine
import NtimeDspace.SelectedCounter

/-!
# Compiled coefficients are coefficients of the actual Hermite weight

The machine's modular coefficient program agrees with the truncated reciprocal
weight when the nodes are distinct and nonzero and the queried degree is below
both the truncation order and the prime. For consecutive nodes these conditions
follow from `Q < p`, positive order at most `p`, and index below the order.

Lists and balanced trees below are proof witnesses only. The machine endpoint
is transported by equality of its encoded output; its runtime is unchanged.
-/

namespace NtimeDspace.HermiteCoefficientCorrectness

open Turing Turing.MultiTapeTM HermiteRecovery

theorem indexedCoefficient_eq_nodeWeight {p Q : ℕ} [Fact p.Prime]
    (nodeValue : Fin Q → ZMod p) (distinct : Function.Injective nodeValue)
    (node : Fin Q) (nonzero : nodeValue node ≠ 0)
    (order : ℕ) (positive : 0 < order) (within : order ≤ p)
    (index : ℕ) (below : index < order) :
    IntervalCoefficients.allCoefficient
      (ScalarRecoveryLoop.factorAccessor nodeValue node order) Q index =
      (nodeWeight (Finset.univ.image nodeValue) (nodeValue node) order).coeff index := by
  classical
  let others := ScalarRecoveryLoop.otherNodes nodeValue node
  let entries := (nodeValue node, 1) :: others.map (fun other => (nodeValue node - other, order))
  have enumerates : others.toFinset = (Finset.univ.image nodeValue).erase (nodeValue node) :=
    ScalarRecoveryLoop.otherNodes_toFinset nodeValue distinct node
  have nodup : others.Nodup := ScalarRecoveryLoop.otherNodes_nodup nodeValue distinct node
  have length : entries.length = Q := by
    simp only [entries, List.length_cons, List.length_map, others,
      ScalarRecoveryLoop.otherNodes, List.length_ofFn]
    have bound := node.isLt
    omega
  have reads : ∀ slot : Fin entries.length,
      ScalarRecoveryLoop.factorAccessor nodeValue node order slot.val = entries[slot.val] :=
    ScalarRecoveryLoop.factorAccessor_reads nodeValue node order
  have entriesValid : ∀ entry ∈ entries, entry.1 ≠ 0 ∧ 0 < entry.2 :=
    nodeFactors_valid (Finset.univ.image nodeValue) (nodeValue node) nonzero
      order positive others (by
        ext value
        simpa only [List.mem_toFinset, Finset.mem_erase] using Finset.ext_iff.mp enumerates value)
  have valid : IntervalCoefficients.Valid
      (ScalarRecoveryLoop.factorAccessor nodeValue node order) entries.length := by
    intro slot inside
    rw [reads ⟨slot, inside⟩]
    exact entriesValid _ (List.getElem_mem inside)
  have balanced := IntervalCoefficients.allCoefficient_eq_balanced
    (ScalarRecoveryLoop.factorAccessor nodeValue node order) entries valid reads index
      (below.trans_le within)
  have weight := balancedNodeCoefficientTree_correct
    (Finset.univ.image nodeValue) (nodeValue node) nonzero order positive
      others nodup (by
        ext value
        simpa only [List.mem_toFinset, Finset.mem_erase] using Finset.ext_iff.mp enumerates value)
      index below
  have othersLength : others.length + 1 = Q := by simpa only [entries, List.length_cons,
    List.length_map] using length
  rw [length] at balanced
  exact balanced.trans (by
    simpa only [balancedNodeCoefficientTree, entries, List.length_cons, List.length_map, othersLength]
      using weight)

/-- The polynomial appearing in the multi-node Hermite recovery identity for
the exact consecutive nodes used by the compiled accessor. -/
noncomputable def weightPolynomial (input : HermiteCoefficientMachine.Input) :
    Polynomial (ZMod input.val.1) := by
  let : Fact input.val.1.Prime := ⟨input.property.1⟩
  exact nodeWeight
    (Finset.univ.image (SelectedCounter.nodeValue (p := input.val.1) (nodes := input.val.2.1)))
    (SelectedCounter.nodeValue (p := input.val.1)
      (⟨input.val.2.2.1, input.property.2⟩ : Fin input.val.2.1)) input.val.2.2.2.1

/-- Exact natural output equality, not merely congruence modulo the prime. -/
theorem coefficient_eq_nodeWeight (input : HermiteCoefficientMachine.Input)
    (nodes : input.val.2.1 < input.val.1)
    (positive : 0 < input.val.2.2.2.1) (within : input.val.2.2.2.1 ≤ input.val.1)
    (below : input.val.2.2.2.2 < input.val.2.2.2.1) :
    HermiteCoefficientMachine.coefficient input =
      ((weightPolynomial input).coeff input.val.2.2.2.2).val := by
  let : Fact input.val.1.Prime := ⟨input.property.1⟩
  have correct := indexedCoefficient_eq_nodeWeight
    (SelectedCounter.nodeValue (p := input.val.1) (nodes := input.val.2.1))
    (SelectedCounter.nodeValue_injective nodes)
    ⟨input.val.2.2.1, input.property.2⟩
    (SelectedCounter.nodeValue_nonzero nodes ⟨input.val.2.2.1, input.property.2⟩)
    input.val.2.2.2.1 positive within input.val.2.2.2.2 below
  exact congrArg ZMod.val correct

/-- The bounded machine domain already supplies `order ≤ p`. These additional
conditions identify coefficients inside the truncated Hermite weight. -/
def WeightValid (input : HermiteCoefficientMachine.BoundedInput) : Prop :=
  input.val.val.2.1 < input.val.val.1 ∧ 0 < input.val.val.2.2.2.1 ∧
    input.val.val.2.2.2.2 < input.val.val.2.2.2.1

abbrev WeightInput := {input : HermiteCoefficientMachine.BoundedInput // WeightValid input}

def encWeightInput : WeightInput ↪ List Bool :=
  (⟨Subtype.val, Subtype.val_injective⟩ : WeightInput ↪ HermiteCoefficientMachine.BoundedInput).trans
    HermiteCoefficientMachine.encBoundedInput

noncomputable def weightCoefficient (input : WeightInput) : ℕ :=
  ((weightPolynomial input.val.val).coeff input.val.val.val.2.2.2.2).val

theorem weightCoefficient_eq_compiled (input : WeightInput) :
    weightCoefficient input = HermiteCoefficientMachine.coefficient input.val.val :=
  (coefficient_eq_nodeWeight input.val.val input.property.1 input.property.2.1
    input.val.property.2.1 input.property.2.2).symm

/-- The already compiled machine computes the actual Hermite-weight
coefficient in quadratic binary workspace. No new machine is assumed. -/
theorem weightCoefficient_inSpace :
    ComputableInSpace weightCoefficient encWeightInput encNat
      (fun input => HermiteCoefficientMachine.bitBudget input.val) := by
  have compiled := HermiteCoefficientMachine.coefficient_inSpace_bits.of_encIn_eq
    (encIn' := encWeightInput)
    (fun input : WeightInput => input.val) (fun _ => rfl)
  apply compiled.of_enc_eq
  intro input
  rw [weightCoefficient_eq_compiled]

theorem weightCoefficient_simultaneous_bounds :
    ∃ C, ComputableInTimeAndSpace weightCoefficient encWeightInput encNat
      (fun input => 2 ^ (C * HermiteCoefficientMachine.bitBudget input.val))
      (fun input => C * HermiteCoefficientMachine.bitBudget input.val) := by
  obtain ⟨C, k, State, finiteState, machine, compiled⟩ :=
    HermiteCoefficientMachine.coefficient_simultaneous_bits
  refine ⟨C, k, State, finiteState, machine, ?_⟩
  intro input
  rw [weightCoefficient_eq_compiled]
  exact compiled input.val

end NtimeDspace.HermiteCoefficientCorrectness
