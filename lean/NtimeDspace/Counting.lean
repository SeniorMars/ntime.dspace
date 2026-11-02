import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-!
# Counting semantics and a reference modular counter

This file specifies the manuscript's declared-variable convention and proves
functional correctness of a reference counter. Clauses have **at most** three
literals, including the empty clause; unused declared variables are retained.

The reference counter enumerates all `2^n` assignments. Its tail-recursive
accumulator is useful as a correctness specification, but its assignment list
is materialized: this is not the new grouped algorithm and proves no small-space
bound. In particular, an accumulator bound is not a work-tape-space theorem.
-/

namespace NtimeDspace

open scoped BigOperators

abbrev Assignment (n : ℕ) := Fin n → Bool

/-- `positive = true` denotes the variable; `false` denotes its negation. -/
structure Literal (n : ℕ) where
  index : Fin n
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : ℕ} (literal : Literal n) (assignment : Assignment n) : Bool :=
  if literal.positive then assignment literal.index else !(assignment literal.index)

/-- The empty clause is legal, as are unit and binary clauses. -/
structure Clause (n : ℕ) where
  literals : List (Literal n)
  width_le_three : literals.length ≤ 3

def Clause.eval {n : ℕ} (clause : Clause n) (assignment : Assignment n) : Bool :=
  clause.literals.any (fun literal => literal.eval assignment)

structure Formula (n : ℕ) where
  clauses : List (Clause n)

def Formula.eval {n : ℕ} (formula : Formula n) (assignment : Assignment n) : Bool :=
  formula.clauses.all (fun clause => clause.eval assignment)

/-- Semantic satisfaction explicitly requires one true literal in each clause. -/
def Formula.Satisfies {n : ℕ} (formula : Formula n) (assignment : Assignment n) : Prop :=
  ∀ clause ∈ formula.clauses,
    ∃ literal ∈ clause.literals, literal.eval assignment = true

theorem Formula.eval_eq_true_iff {n : ℕ} (formula : Formula n)
    (assignment : Assignment n) :
    formula.eval assignment = true ↔ formula.Satisfies assignment := by
  simp [Formula.eval, Formula.Satisfies, Clause.eval]

instance {n : ℕ} (formula : Formula n) (assignment : Assignment n) :
    Decidable (formula.Satisfies assignment) :=
  decidable_of_iff (formula.eval assignment = true)
    (formula.eval_eq_true_iff assignment)

/-- An independent cardinality specification, with every declared variable present. -/
def satisfyingCount {n : ℕ} (formula : Formula n) : ℕ :=
  (Finset.univ.filter formula.Satisfies).card

/-- An explicit enumeration: extend every shorter assignment by both Boolean values. -/
def assignmentList : (n : ℕ) → List (Assignment n)
  | 0 => [Fin.elim0]
  | n + 1 =>
      (assignmentList n).map (Fin.cons false) ++
      (assignmentList n).map (Fin.cons true)

theorem assignmentList_complete (n : ℕ) (assignment : Assignment n) :
    assignment ∈ assignmentList n := by
  induction n with
  | zero =>
      have h : assignment = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simp [assignmentList, h]
  | succ n ih =>
      have htail : Fin.tail assignment ∈ assignmentList n := ih (Fin.tail assignment)
      have hrebuild := Fin.cons_self_tail assignment
      cases hhead : assignment 0 with
      | false =>
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨Fin.tail assignment, htail, by simpa [hhead] using hrebuild⟩
      | true =>
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨Fin.tail assignment, htail, by simpa [hhead] using hrebuild⟩

theorem assignmentList_nodup (n : ℕ) : (assignmentList n).Nodup := by
  induction n with
  | zero => simp [assignmentList]
  | succ n ih =>
      have hinjective (value : Bool) : Function.Injective
          (fun assignment : Assignment n =>
            (Fin.cons value assignment : Assignment (n + 1))) := by
        intro a b h
        exact (Fin.cons_inj.mp h).2
      apply List.nodup_append.mpr
      refine ⟨(List.nodup_map_iff (hinjective false)).mpr ih,
        (List.nodup_map_iff (hinjective true)).mpr ih, ?_⟩
      intro a ha b hb hab
      obtain ⟨a', _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', _, rfl⟩ := List.mem_map.mp hb
      have h := congrFun hab 0
      simp at h

theorem assignmentList_length (n : ℕ) : (assignmentList n).length = 2 ^ n := by
  induction n with
  | zero => simp [assignmentList]
  | succ n ih => simp [assignmentList, ih, pow_succ, Nat.mul_two]

theorem assignmentList_toFinset (n : ℕ) :
    (assignmentList n).toFinset = Finset.univ := by
  ext assignment
  simp [assignmentList_complete]

/-- One contribution per satisfying assignment, evaluated from the formula. -/
def Formula.contribution {n : ℕ} (formula : Formula n) (assignment : Assignment n) : ℕ :=
  if formula.eval assignment = true then 1 else 0

theorem satisfyingCount_eq_sum {n : ℕ} (formula : Formula n) :
    satisfyingCount formula = ∑ assignment, formula.contribution assignment := by
  simp only [satisfyingCount, Formula.contribution, formula.eval_eq_true_iff]
  exact Finset.card_filter _ _

theorem assignmentList_contribution_sum {n : ℕ} (formula : Formula n) :
    ((assignmentList n).map formula.contribution).sum = satisfyingCount formula := by
  rw [← List.sum_toFinset formula.contribution (assignmentList_nodup n),
    assignmentList_toFinset, satisfyingCount_eq_sum]

/-- Reduce after each contribution, retaining only a residue in the accumulator.
The explicit list supplied to this procedure is not a machine-space model. -/
def modularAccumulator {α : Type*} (contribution : α → ℕ) (modulus : ℕ) :
    List α → ℕ → ℕ
  | [], accumulator => accumulator % modulus
  | value :: remaining, accumulator =>
      modularAccumulator contribution modulus remaining
        ((accumulator + contribution value) % modulus)

/-- Loop invariant: the accumulator plus the unprocessed exact sum determines
the final residue. This holds even for modulus zero under Lean's convention. -/
theorem modularAccumulator_invariant {α : Type*} (contribution : α → ℕ)
    (modulus : ℕ) (values : List α) (accumulator : ℕ) :
    modularAccumulator contribution modulus values accumulator =
      (accumulator + (values.map contribution).sum) % modulus := by
  induction values generalizing accumulator with
  | nil => simp [modularAccumulator]
  | cons value remaining ih =>
      simp [modularAccumulator, ih, Nat.add_assoc]

/-- The accumulator's value is bounded; no bound on the whole program follows. -/
theorem modularAccumulator_lt {α : Type*} (contribution : α → ℕ)
    (modulus : ℕ) (positive : 0 < modulus) (values : List α) (accumulator : ℕ) :
    modularAccumulator contribution modulus values accumulator < modulus := by
  rw [modularAccumulator_invariant]
  exact Nat.mod_lt _ positive

/-- A reference implementation, exponential enumeration and no space claim. -/
def countModP {n : ℕ} (formula : Formula n) (modulus : ℕ) : ℕ :=
  modularAccumulator formula.contribution modulus (assignmentList n) 0

/-- Functional correctness against the independent satisfying-set cardinality. -/
theorem countModP_correct {n : ℕ} (formula : Formula n) (modulus : ℕ) :
    countModP formula modulus = satisfyingCount formula % modulus := by
  simp [countModP, modularAccumulator_invariant, assignmentList_contribution_sum]

theorem countModP_lt {n : ℕ} (formula : Formula n) (modulus : ℕ)
    (positive : 0 < modulus) : countModP formula modulus < modulus := by
  rw [countModP_correct]
  exact Nat.mod_lt _ positive

end NtimeDspace
