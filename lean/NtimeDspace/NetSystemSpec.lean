import NtimeDspace.NetSystemTerm

/-!
# The constraint system of a block-counting network

For the network `d` of input `x`, clock `t` and schedule `σ`, the constraint
`v` of `NetworkSystem.toSystem d` has scope the ports `explicitPortsNum` of
vertex `v` and weight the table entries `tableEntryNum`. These are the facts
the counter's accessor contracts need.
-/

namespace NtimeDspace.LocalSim

open Cslib.Complexity.CountingSimulation Cslib.Circuits.Frontier Turing Turing.MultiTapePTM
  NetworkSystem WeightedSystem

variable {k s : ℕ} {State : Type} [DecidableEq State] (machine : MultiTapePTM k Bool State)
  (e : State ≃ Fin s)

/-- The ports of vertex `v` of the network of clock `t` and schedule `σ`. -/
def netPorts (k s t σ v : ℕ) : List ℕ :=
  explicitPortsNum k (numBlocks t) (letterBits k s (blockLength t)) σ v

theorem lt_numEdges_of_mem_netPorts {t σ v j : ℕ} (h : j ∈ netPorts k s t σ v) :
    j < 2 * (numBlocks t * (3 * k + 1) * letterBits k s (blockLength t)) := by
  unfold netPorts explicitPortsNum at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

theorem length_constraints_toSystem (x : List Bool) (t σ : ℕ)
    (pos : 0 < (blockNetworkOf machine e (x, t, σ)).2.numEdges) :
    (toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints.length =
      numBlocks t * (3 * k + 2) + numBlocks t * (3 * k + 1) * letterBits k s (blockLength t) := by
  simp [toSystem, length_vertices_blockNetworkOf]

theorem constraint_toSystem (x : List Bool) (t σ : ℕ)
    (pos : 0 < (blockNetworkOf machine e (x, t, σ)).2.numEdges) (v : ℕ)
    (hv : v < (toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints.length) :
    (toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints[v] =
      vertexConstraint (blockNetworkOf machine e (x, t, σ)).2 pos
        (netPorts k s t σ v, (List.range (2 ^ (netPorts k s t σ v).length)).map
          (tableEntryNum e (blockLength t) machine x (numBlocks t) σ v (netPorts k s t σ v))) := by
  have hv' : v < numBlocks t * (3 * k + 2) +
      numBlocks t * (3 * k + 1) * letterBits k s (blockLength t) := by
    rwa [length_constraints_toSystem] at hv
  have hget := vertex_blockNetworkOf machine e x t σ v hv'
  simp only [toSystem, List.getElem_map]
  congr 1
  have hlen : v < (blockNetworkOf machine e (x, t, σ)).2.vertices.length := by
    rw [length_vertices_blockNetworkOf]; exact hv'
  rw [List.getElem?_eq_getElem hlen] at hget
  exact Option.some.inj hget

theorem scope_length_toSystem (x : List Bool) (t σ : ℕ)
    (pos : 0 < (blockNetworkOf machine e (x, t, σ)).2.numEdges) (v : ℕ)
    (hv : v < (toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints.length) :
    ((toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints[v]).scope.length =
      (netPorts k s t σ v).length := by
  rw [constraint_toSystem machine e x t σ pos v hv]
  simp [vertexConstraint]

theorem scope_get_toSystem (x : List Bool) (t σ : ℕ)
    (pos : 0 < (blockNetworkOf machine e (x, t, σ)).2.numEdges) (v : ℕ)
    (hv : v < (toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints.length) (i : ℕ)
    (hi : i < ((toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints[v]).scope.length) :
    (((toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints[v]).scope[i] : ℕ) =
      (netPorts k s t σ v).getD i 0 := by
  have hl := scope_length_toSystem machine e x t σ pos v hv
  have hi' : i < (netPorts k s t σ v).length := by rw [← hl]; exact hi
  have hmem : (netPorts k s t σ v)[i] ∈ netPorts k s t σ v := List.getElem_mem hi'
  have hlt := lt_numEdges_of_mem_netPorts hmem
  rw [List.getD_eq_getElem _ _ hi']
  simp only [constraint_toSystem machine e x t σ pos v hv, vertexConstraint, List.getElem_map]
  have hlt' : (netPorts k s t σ v)[i] < (blockNetworkOf machine e (x, t, σ)).2.numEdges := by
    rw [numEdges_blockNetworkOf]; exact hlt
  exact Nat.mod_eq_of_lt hlt'

theorem weight_toSystem (x : List Bool) (t σ : ℕ)
    (pos : 0 < (blockNetworkOf machine e (x, t, σ)).2.numEdges) (v : ℕ)
    (hv : v < (toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints.length) (A : ℕ) :
    ((toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints[v]).weight
        (AssignmentLoop.assignment _ A) =
      tableEntryNum e (blockLength t) machine x (numBlocks t) σ v (netPorts k s t σ v)
        (A % 2 ^ (netPorts k s t σ v).length) := by
  have hc := constraint_toSystem machine e x t σ pos v hv
  generalize (toSystem (blockNetworkOf machine e (x, t, σ)).2 pos).constraints[v] = c at hc ⊢
  subst hc
  simp only [vertexConstraint, ExplicitTensorNetwork.entry]
  have ha : ∀ m, AssignmentLoop.assignment m A = fun i : Fin m => A.testBit i := fun m => rfl
  rw [ha, lsbValue_ofFn_testBit, List.length_map]
  have hlt : A % 2 ^ (netPorts k s t σ v).length < 2 ^ (netPorts k s t σ v).length :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range]

end NtimeDspace.LocalSim
