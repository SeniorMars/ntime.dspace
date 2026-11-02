import Complexity.Computability.Complexity.Classes.CountingSimulation.BlockNetworks

/-!
# From nondeterministic time to weighted constraint systems

Complexitylib's explicit tensor networks are weighted Boolean constraint
systems: the edges are the variables, each vertex is a constraint whose ports
are its scope, its table has natural-number entries, and the contraction is
the weighted count `∑_x ∏_v table_v(x|ports)`. An admissible network is
rows-first bipartite, so every variable lies in exactly two scopes; it has
between `t` and `C*t` variables, at most `C*t` constraints, and arity at most
`C*log₂ t`.

This module combines Complexitylib's accept-count characterization of `NTIME`
with its block-network counting identity. A problem in `NTIME[T]` is decided by
whether some schedule's network has a positive weighted count, at a clock
linear in `T`, and every such network is admissible. No counting algorithm is
assumed.
-/

namespace NtimeDspace.SemanticReduction

open Cslib.Complexity Cslib.Complexity.CountingSimulation Turing Cslib.Circuits.Frontier

/-- **The semantic reduction.** Membership in `NTIME[T]` is the positivity of
the weighted count of some schedule's admissible constraint system, at the
clock `t = c * T n + c`. -/
theorem exists_networks_of_mem_NTIME {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}
    {A : Set α} (h : A ∈ NTIME enc T) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State)
      (s : ℕ) (e : State ≃ Fin s) (c : ℕ), 2 ≤ c ∧ ∀ a,
        (a ∈ A ↔ ∃ σ < scheduleCount (k + 1) (c * T (enc a).length + c),
          0 < (blockNetworkOf machine e (enc a, c * T (enc a).length + c, σ)).2.contraction) ∧
        ∀ σ, ExplicitAdmissible (6 * (3 * k + 1) * (s + k + 4)) (c * T (enc a).length + c)
          (blockNetworkOf machine e (enc a, c * T (enc a).length + c, σ)) := by
  obtain ⟨k, State, _, machine, c₁, c₂, hM⟩ := exists_acceptCount_of_mem_NTIME h
  let e := Finite.equivFin State
  refine ⟨k, State, inferInstance, machine, Nat.card State, e, c₁ + c₂ + 2, by omega,
    fun a => ⟨?_, fun σ => explicitAdmissible_blockNetworkOf machine e (enc a) σ (by nlinarith)⟩⟩
  set t := (c₁ + c₂ + 2) * T (enc a).length + (c₁ + c₂ + 2)
  have ht : 2 ≤ t := by simp only [t]; nlinarith
  have hτ : c₁ * T (enc a).length + c₂ ≤ paddedTime t :=
    le_trans (by simp only [t]; nlinarith) (le_paddedTime t)
  rw [hM a _ hτ, ← sum_contraction_blockNetworkOf machine e (enc a) ht, Finset.sum_pos_iff]
  simp only [Finset.mem_range]

end NtimeDspace.SemanticReduction
