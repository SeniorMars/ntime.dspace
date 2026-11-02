/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.WSchedulePlacement

-- upstream: local-only (normalization of the weighted counting application's inputs)

/-!
# Give every variable an incidence without changing the count

`normalize S` appends exactly one weight-one constraint per declared variable.
For an unused variable its scope is the singleton containing that variable;
for a used variable its scope is empty. Thus the weighted count is unchanged,
the number of constraints becomes `m + n`, and every variable occurs at least
once. An occurrence bound of three is preserved, giving `n ≤ M ≤ 3*n`.

Occurrences count scope positions, including repeated variables within a scope.
The normalization therefore uses the same incidence convention as the counter
and its balanced-seed theorem.
-/

namespace NtimeDspace.WeightedNormalization

open WeightedSystem
open scoped BigOperators

variable {n : ℕ}

/-- Number of actual scope positions occupied by a variable. -/
def occurrences (S : System n) (v : Fin n) : ℕ :=
  ∑ e : Fin S.constraints.length, ∑ i : Fin S.constraints[e].scope.length,
    if S.constraints[e].scope[i] = v then 1 else 0

def addedConstraint (S : System n) (v : Fin n) : Constraint n where
  scope := if occurrences S v = 0 then [v] else []
  weight := fun _ => 1

def normalize (S : System n) : System n where
  constraints := S.constraints ++ List.ofFn (addedConstraint S)

@[simp] theorem constraint_count (S : System n) :
    (normalize S).constraints.length = S.constraints.length + n := by
  simp [normalize]

private theorem product_positions (cs : List (Constraint n)) (x : Fin n → Bool) :
    (∏ e : Fin cs.length, cs[e].weight (cs[e].restrict x)) =
      (cs.map fun c => c.weight (c.restrict x)).prod := by
  rw [← List.prod_ofFn]
  congr 1
  simpa only [Fin.getElem_fin] using
    List.ofFn_getElem_eq_map cs (fun c => c.weight (c.restrict x))

/-- Appending the normalization constraints changes no assignment's weight. -/
theorem assignment_weight (S : System n) (x : Fin n → Bool) :
    (∏ e : Fin (normalize S).constraints.length,
      (normalize S).constraints[e].weight ((normalize S).constraints[e].restrict x)) =
      ∏ e : Fin S.constraints.length, S.constraints[e].weight (S.constraints[e].restrict x) := by
  rw [product_positions, product_positions]
  simp [normalize, List.map_append, List.prod_append, List.map_ofFn, Function.comp_def,
    addedConstraint]

/-- The exact natural weighted count, not just its residue, is preserved. -/
theorem count_eq (S : System n) : (normalize S).count = S.count := by
  unfold System.count
  exact Finset.sum_congr rfl fun x _ => assignment_weight S x

theorem occurrences_eq_list (S : System n) (v : Fin n) :
    occurrences S v = (S.constraints.map fun c =>
      (c.scope.map fun u => if u = v then 1 else 0).sum).sum := by
  unfold occurrences
  have hscope (c : Constraint n) :
      (∑ i : Fin c.scope.length, if c.scope[i] = v then 1 else 0) =
        (c.scope.map fun u => if u = v then 1 else 0).sum := by
    simpa only [Fin.getElem_fin] using
      FormulaIncidences.sum_positions_eq_list c.scope (fun u => if u = v then 1 else 0)
  simp_rw [hscope]
  simpa only [Fin.getElem_fin] using FormulaIncidences.sum_positions_eq_list S.constraints
    (fun c => (c.scope.map fun u => if u = v then 1 else 0).sum)

theorem bucketCount_eq_occurrences (S : System n) (v : Fin n) :
    HashVariance.bucketCount (incidenceVariable S) v = (occurrences S v : ℚ) := by
  simp only [HashVariance.bucketCount, Incidence, Fintype.sum_sigma,
    incidenceVariable, occurrences, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rfl

private theorem added_occurrences (S : System n) (u v : Fin n) :
    (((addedConstraint S u).scope.map fun x => if x = v then 1 else 0).sum : ℕ) =
      if u = v then if occurrences S v = 0 then 1 else 0 else 0 := by
  by_cases huv : u = v
  · subst u
    by_cases h : occurrences S v = 0 <;> simp [addedConstraint, h]
  · by_cases h : occurrences S u = 0 <;> simp [addedConstraint, h, huv]

/-- An unused variable gains exactly one occurrence; all others keep theirs. -/
theorem occurrences_normalize (S : System n) (v : Fin n) :
    occurrences (normalize S) v = occurrences S v + if occurrences S v = 0 then 1 else 0 := by
  rw [occurrences_eq_list, occurrences_eq_list]
  simp only [normalize, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
    Function.comp_def]
  simp_rw [added_occurrences]
  simp [← occurrences_eq_list S v]

theorem occurrences_normalize_pos (S : System n) (v : Fin n) :
    1 ≤ occurrences (normalize S) v := by
  rw [occurrences_normalize]
  split_ifs <;> omega

theorem occurrences_normalize_le (S : System n) {d : ℕ} (hd : 1 ≤ d)
    (bound : ∀ v, occurrences S v ≤ d) (v : Fin n) :
    occurrences (normalize S) v ≤ d := by
  rw [occurrences_normalize]
  have := bound v
  split_ifs <;> omega

/-- The sum of variable occurrence counts is the number of incidences. -/
theorem incidenceCount_eq_sum_occurrences (S : System n) :
    incidenceCount S = ∑ v, occurrences S v := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_sum]
  simp_rw [← bucketCount_eq_occurrences]
  rw [HashVariance.sum_bucketCount, WSchedulePlacement.card_incidence]

theorem incidenceCount_lower (S : System n) : n ≤ incidenceCount (normalize S) := by
  rw [incidenceCount_eq_sum_occurrences]
  calc
    n = ∑ _v : Fin n, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun v _ => occurrences_normalize_pos S v

theorem incidenceCount_upper (S : System n) {d : ℕ} (hd : 1 ≤ d)
    (bound : ∀ v, occurrences S v ≤ d) : incidenceCount (normalize S) ≤ d * n := by
  rw [incidenceCount_eq_sum_occurrences]
  calc
    _ ≤ ∑ _v : Fin n, d := Finset.sum_le_sum fun v _ => occurrences_normalize_le S hd bound v
    _ = d * n := by simp [Nat.mul_comm]

theorem arity_bound (S : System n) {Δ : ℕ}
    (bound : ∀ c ∈ S.constraints, c.scope.length ≤ Δ) :
    ∀ c ∈ (normalize S).constraints, c.scope.length ≤ max Δ 1 := by
  intro c hc
  simp only [normalize, List.mem_append, List.mem_ofFn] at hc
  rcases hc with hc | ⟨v, rfl⟩
  · exact (bound c hc).trans (le_max_left _ _)
  · have hv : (addedConstraint S v).scope.length ≤ 1 := by
      change (if occurrences S v = 0 then [v] else []).length ≤ 1
      split_ifs <;> simp_all
    exact hv.trans (le_max_right _ _)

/-- Normalization also preserves the set-like scope convention of the paper. -/
theorem scopes_nodup (S : System n)
    (nodup : ∀ c ∈ S.constraints, c.scope.Nodup) :
    ∀ c ∈ (normalize S).constraints, c.scope.Nodup := by
  intro c hc
  simp only [normalize, List.mem_append, List.mem_ofFn] at hc
  rcases hc with hc | ⟨v, rfl⟩
  · exact nodup c hc
  · change (if occurrences S v = 0 then [v] else []).Nodup
    split_ifs <;> simp

/-- The occurrence hypothesis used by the balanced-seed theorem is preserved. -/
theorem bucketCount_normalize_le_three (S : System n)
    (bound : ∀ v, HashVariance.bucketCount (incidenceVariable S) v ≤ 3) :
    ∀ v, HashVariance.bucketCount (incidenceVariable (normalize S)) v ≤ 3 := by
  intro v
  rw [bucketCount_eq_occurrences]
  have hn : ∀ v, occurrences S v ≤ 3 := by
    intro v
    have hv := bound v
    rw [bucketCount_eq_occurrences] at hv
    exact_mod_cast hv
  exact_mod_cast occurrences_normalize_le S (by omega : 1 ≤ 3) hn v

theorem incidenceCount_between (S : System n)
    (bound : ∀ v, HashVariance.bucketCount (incidenceVariable S) v ≤ 3) :
    n ≤ incidenceCount (normalize S) ∧ incidenceCount (normalize S) ≤ 3 * n := by
  refine ⟨incidenceCount_lower S, incidenceCount_upper S (by omega) ?_⟩
  intro v
  have hv := bound v
  rw [bucketCount_eq_occurrences] at hv
  exact_mod_cast hv

/-- Zero constraints and unused variables satisfy the normalization contract. -/
example : incidenceCount (normalize (⟨[]⟩ : System 3)) = 3 := by decide

/-- A repeated variable counts once per position, not once per constraint. -/
example : occurrences (⟨[⟨[0, 0, 0], fun _ => 1⟩]⟩ : System 1) 0 = 3 := by decide

end NtimeDspace.WeightedNormalization
