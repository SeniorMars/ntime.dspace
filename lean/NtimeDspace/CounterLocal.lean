import NtimeDspace.ProgPieces
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

/-!
# Program pieces: ranks and local assignments

Terms for `LocalAssignmentLoop.countBefore`, `groupSize` and the bits of a
local assignment, parametrized by a term for the group map. The group map is
supplied as a Lean function on argument terms whose meaning is a fixed
function `G : ℕ → ℕ` of the argument's meaning (`ImplementsFun`).
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- `1` if the arguments are equal, `0` otherwise. -/
def eqT (a b : Term) : Term := sub (const 1) (add (lt a b) (lt b a))

@[simp] theorem denote_eqT (a b : Term) (env : List ℕ) :
    (eqT a b).denote w env = if a.denote w env = b.denote w env then 1 else 0 := by
  simp only [eqT, denote_sub, denote_const, denote_add, denote_lt]
  split_ifs <;> omega

theorem StableAt.eqT {a b : Term} {env : List ℕ} (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (eqT a b) env := fun extra => by simp [ha extra, hb extra]

/-- A term function implements `G` on environments extending `base`. -/
def ImplementsFun (w : List Bool) (base : List ℕ) (f : Term → Term) (G : ℕ → ℕ) : Prop :=
  ∀ (extra : List ℕ) (a : Term), StableAt w a (extra ++ base) →
    (f a).denote w (extra ++ base) = G (a.denote w (extra ++ base)) ∧
      StableAt w (f a) (extra ++ base)

theorem foldl_add_eq_sum (g : ℕ → ℕ) (n init : ℕ) :
    (List.range n).foldl (fun acc k => acc + g k) init = init + ∑ k ∈ Finset.range n, g k := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Finset.sum_range_succ, Nat.add_assoc]

/-- The number of variables below `limit` in `group`. -/
def countBeforeT (n : Term) (g : Term → Term) (group limit : Term) : Term :=
  foldT n (const 0) fun acc i => add acc (mul (lt i limit) (eqT (g i) group))

end NtimeDspace.ProgTerm
