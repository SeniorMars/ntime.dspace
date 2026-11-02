import NtimeDspace.NetworkSystem
import NtimeDspace.HashVariance
import NtimeDspace.WSchedulePlacement

/-!
# Degrees of a rows-first bipartite network

For a network whose ports all name edges and which is rows-first bipartite,
every edge lies in exactly two port lists. So in its weighted system every
variable has two incidences (`bucketCount_variable`), there are `2N`
incidences (`incidenceCount_eq_two_mul`), and every constraint has at most
`maxDegree` incidences (`bucketCount_constraint_le`).
-/

namespace NtimeDspace.NetworkSystem

open Cslib.Circuits.Frontier ExplicitTensorNetwork WeightedSystem

variable (d : ExplicitTensorNetwork ℕ)

theorem sum_map_ite_eq_count {α : Type*} [DecidableEq α] (l : List α) (a : α) :
    (l.map fun x => if x = a then 1 else 0 : List ℕ).sum = l.count a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons]
    by_cases h : x = a
    · subst h; simp; omega
    · simp [h]

theorem sum_fin_ite_eq_count {α : Type*} [DecidableEq α] (l : List α) (a : α) :
    ∑ i : Fin l.length, (if l[i] = a then 1 else 0 : ℕ) = l.count a :=
  (sum_fin_eq_list l (fun x => if x = a then 1 else 0)).trans (sum_map_ite_eq_count l a)

theorem count_map_mod {N : ℕ} (hN : 0 < N) (l : List ℕ) (hl : ∀ i ∈ l, i < N) (v : Fin N) :
    (l.map fun i => (⟨i % N, Nat.mod_lt _ hN⟩ : Fin N)).count v = l.count v.val := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.count_cons, List.count_cons,
      ih fun i hi => hl i (List.mem_cons_of_mem _ hi)]
    have hx : x % N = x := Nat.mod_eq_of_lt (hl x (List.mem_cons_self))
    congr 1
    simp only [beq_iff_eq, Fin.ext_iff, hx]

theorem sum_count_eq_two {r : ℕ} (hb : d.IsRowsFirstBipartite r) {i : ℕ} (hi : i < d.numEdges) :
    (d.vertices.map fun v => v.1.count i).sum = 2 := by
  obtain ⟨h1, h2⟩ := (hb.2 i hi)
  rw [← List.take_append_drop r d.vertices, List.map_append, List.sum_append, h1, h2]

variable (positive : 0 < d.numEdges)

/-- Every variable has exactly two incidences. -/
theorem variable_count {r : ℕ} (hb : d.IsRowsFirstBipartite r) (v : Fin d.numEdges) :
    (∑ inc : Incidence (toSystem d positive),
      if incidenceVariable (toSystem d positive) inc = v then 1 else 0 : ℕ) = 2 := by
  rw [Fintype.sum_sigma]
  rw [Finset.sum_congr rfl fun e _ => sum_fin_ite_eq_count ((toSystem d positive).constraints[e]).scope v]
  rw [sum_fin_eq_list (toSystem d positive).constraints (fun c => c.scope.count v)]
  simp only [toSystem, List.map_map]
  rw [List.map_congr_left (g := fun x => x.1.count v.val) (fun x hx => by
    simp only [Function.comp_apply, vertexConstraint]
    exact count_map_mod positive x.1 (hb.1 x hx) v)]
  exact sum_count_eq_two d hb v.isLt

/-- The network has `2N` incidences. -/
theorem incidenceCount_eq_two_mul {r : ℕ} (hb : d.IsRowsFirstBipartite r) :
    incidenceCount (toSystem d positive) = 2 * d.numEdges := by
  rw [← WSchedulePlacement.card_incidence, Fintype.card_eq_sum_ones]
  have h1 : ∀ inc : Incidence (toSystem d positive),
      (1 : ℕ) = ∑ v : Fin d.numEdges, if incidenceVariable (toSystem d positive) inc = v then 1 else 0 :=
    fun inc => by simp
  rw [Finset.sum_congr rfl fun inc _ => h1 inc, Finset.sum_comm,
    Finset.sum_congr rfl fun v _ => variable_count d positive hb v]
  simp [mul_comm]

theorem bucketCount_variable {r : ℕ} (hb : d.IsRowsFirstBipartite r) (v : Fin d.numEdges) :
    HashVariance.bucketCount (incidenceVariable (toSystem d positive)) v = 2 := by
  unfold HashVariance.bucketCount
  have := variable_count d positive hb v
  exact_mod_cast this

theorem scope_length_le_maxDegree (e : Fin (toSystem d positive).constraints.length) :
    ((toSystem d positive).constraints[e]).scope.length ≤ d.maxDegree := by
  have he : (e : ℕ) < d.vertices.length := by simpa [toSystem] using e.isLt
  simp only [toSystem, List.getElem_map, vertexConstraint, List.length_map]
  unfold ExplicitTensorNetwork.maxDegree
  have key : ∀ (l : List (List ℕ × List ℕ)) (j : ℕ) (hj : j < l.length),
      l[j].1.length ≤ (l.map fun v => v.1.length).foldr max 0 := by
    intro l
    induction l with
    | nil => intro j hj; simp at hj
    | cons x xs ih =>
      intro j hj
      rcases j with _ | j
      · simp
      · simp only [List.getElem_cons_succ, List.map_cons, List.foldr_cons]
        exact (ih j (by simpa using hj)).trans (le_max_right _ _)
  show ((List.map (vertexConstraint d positive) d.vertices)[(e : ℕ)]'(by simpa using he)).scope.length ≤ _
  rw [List.getElem_map]
  simp only [vertexConstraint, List.length_map]
  exact key _ _ he

theorem bucketCount_constraint_le (e : Fin (toSystem d positive).constraints.length) :
    HashVariance.bucketCount (fun inc : Incidence (toSystem d positive) => inc.1) e ≤ d.maxDegree := by
  unfold HashVariance.bucketCount
  have : (∑ inc : Incidence (toSystem d positive), if inc.1 = e then (1 : ℚ) else 0) =
      ((toSystem d positive).constraints[e]).scope.length := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [this]
  exact_mod_cast scope_length_le_maxDegree d positive e

end NtimeDspace.NetworkSystem
