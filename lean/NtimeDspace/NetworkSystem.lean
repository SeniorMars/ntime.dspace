import NtimeDspace.WeightedSystem
import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit

/-!
# Explicit tensor networks as weighted constraint systems

An explicit tensor network is a weighted constraint system: the edges are the
variables, each vertex is a constraint whose scope is its list of ports, and
its weight is the table entry at the bits on the ports. When every port names
an edge, which holds for every admissible network, the weighted count is the
contraction.
-/

namespace NtimeDspace.NetworkSystem

open Cslib.Circuits.Frontier ExplicitTensorNetwork WeightedSystem

variable (d : ExplicitTensorNetwork ℕ)

/-- The constraint of a vertex. Ports are reduced modulo the number of edges,
which changes nothing when every port names an edge. -/
def vertexConstraint (positive : 0 < d.numEdges) (v : List ℕ × List ℕ) :
    Constraint d.numEdges where
  scope := v.1.map fun i => ⟨i % d.numEdges, Nat.mod_lt _ positive⟩
  weight a := entry v.2 (List.ofFn a)

/-- The weighted constraint system of a network. -/
def toSystem (positive : 0 < d.numEdges) : System d.numEdges where
  constraints := d.vertices.map (vertexConstraint d positive)

theorem prod_fin_eq_list {α : Type*} (l : List α) (g : α → ℕ) :
    ∏ e : Fin l.length, g l[e] = (l.map g).prod := by
  rw [← List.prod_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map l g

theorem vertexWeight_eq (positive : 0 < d.numEdges) (x : Fin d.numEdges → Bool)
    (v : List ℕ × List ℕ) (valid : ∀ i ∈ v.1, i < d.numEdges) :
    (vertexConstraint d positive v).weight ((vertexConstraint d positive v).restrict x) =
      entry v.2 (d.portBits x v.1) := by
  show entry v.2 (List.ofFn fun i => x ((v.1.map fun i =>
    (⟨i % d.numEdges, Nat.mod_lt _ positive⟩ : Fin d.numEdges))[i])) = entry v.2 (d.portBits x v.1)
  congr 1
  apply List.ext_getElem
  · simp [portBits]
  · intro i h₁ h₂
    have hi : i < v.1.length := by simpa using h₁
    have hlt := valid _ (List.getElem_mem hi)
    simp [portBits, hlt, Nat.mod_eq_of_lt hlt]

/-- **The weighted count of a network is its contraction**, when every port
names an edge. -/
theorem count_toSystem (positive : 0 < d.numEdges)
    (valid : ∀ v ∈ d.vertices, ∀ i ∈ v.1, i < d.numEdges) :
    (toSystem d positive).count = d.contraction := by
  unfold System.count contraction
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [prod_fin_eq_list (toSystem d positive).constraints
    (fun c => c.weight (c.restrict x))]
  simp only [toSystem, List.map_map]
  congr 1
  exact List.map_congr_left fun v hv => vertexWeight_eq d positive x v (valid v hv)

theorem sum_fin_eq_list {α : Type*} (l : List α) (g : α → ℕ) :
    ∑ e : Fin l.length, g l[e] = (l.map g).sum := by
  rw [← List.sum_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map l g

theorem incidenceCount_eq {m : ℕ} (S : System m) :
    incidenceCount S = (S.constraints.map fun c => c.scope.length).sum :=
  sum_fin_eq_list S.constraints (fun c => c.scope.length)

/-- The number of incidences is the total number of ports. -/
theorem incidenceCount_toSystem (positive : 0 < d.numEdges) :
    incidenceCount (toSystem d positive) = (d.vertices.map fun v => v.1.length).sum := by
  rw [incidenceCount_eq]
  simp [toSystem, vertexConstraint, Function.comp_def]

end NtimeDspace.NetworkSystem
