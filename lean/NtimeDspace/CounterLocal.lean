import NtimeDspace.ProgPieces
import NtimeDspace.LocalAssignmentLoop

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

theorem countBeforeT_denote {base : List ℕ} {n : ℕ} {Group : Type*} [DecidableEq Group]
    (groupOf : Fin n → Group) (code : Group → ℕ) (code_injective : Function.Injective code)
    (g : Term → Term) (G : ℕ → ℕ) (hG : ImplementsFun w base g G)
    (hGcode : ∀ i (h : i < n), G i = code (groupOf ⟨i, h⟩))
    (nT group limit : Term) (extra : List ℕ)
    (hn : StableAt w nT (extra ++ base)) (hgroup : StableAt w group (extra ++ base))
    (hlimit : StableAt w limit (extra ++ base))
    (hnv : nT.denote w (extra ++ base) = n) (target : Group)
    (hgv : group.denote w (extra ++ base) = code target) :
    (countBeforeT nT g group limit).denote w (extra ++ base) =
      LocalAssignmentLoop.countBefore groupOf target (limit.denote w (extra ++ base)) := by
  set env := extra ++ base
  simp only [countBeforeT, denote_foldT, denote_const]
  rw [foldAcc_eq _ env (fun acc k => acc +
      (if k < limit.denote w env then 1 else 0) * (if G k = code target then 1 else 0)) ?_,
    foldl_add_eq_sum, hnv, LocalAssignmentLoop.countBefore, NtimeDspace.sumLoop_correct]
  · simp only [Nat.zero_add, Nat.add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.mp hk
    rw [dif_pos hk', hGcode k hk']
    by_cases h1 : k < limit.denote w env <;>
      by_cases h2 : groupOf ⟨k, hk'⟩ = target <;>
      simp [h1, h2, code_injective.eq_iff]
  · intro acc k
    have hk : StableAt w (lvl env.length) ((acc :: k :: extra) ++ base) :=
      stableAt_lvl (by simp [env])
    have hGk := (hG (acc :: k :: extra) (lvl env.length) hk).1
    rw [show (acc :: k :: extra) ++ base = acc :: k :: env from rfl] at hGk
    have hlv : (lvl env.length).denote w (acc :: k :: env) = k := by
      simp [Term.denote_lvl, Nat.add_assoc, Nat.add_sub_cancel_left]
    have hacc : (lvl (env.length + 1)).denote w (acc :: k :: env) = acc := by
      simp [Term.denote_lvl, Nat.add_assoc, Nat.add_sub_add_left]
    simp only [denote_add, denote_mul, denote_lt, denote_eqT, hGk, hlv, hacc, hlimit.cons₂,
      hgroup.cons₂, hgv]

end NtimeDspace.ProgTerm
