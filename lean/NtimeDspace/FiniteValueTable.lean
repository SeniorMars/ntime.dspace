/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.SmallTable

-- upstream: local-only (finite exceptions for the application's program compiler)

/-!
# Natural-valued lookup tables

`valueTableT` extends the Boolean lookup routine to natural outputs. It handles
finitely many exceptional inputs in a function-computation theorem. The input
length is supplied in register zero, as in `SmallTable`.
-/

namespace NtimeDspace.ProgTerm

open Term

/-- Look up a natural value, returning zero outside the table. Duplicate keys
contribute repeatedly; correctness as a lookup uses a duplicate-free key list. -/
def valueTableT (value : List Bool → ℕ) : List (List Bool) → Term
  | [] => const 0
  | v :: vs => add (mul (matchT v) (const (value v))) (valueTableT value vs)

theorem valueTableT_denote (value : List Bool → ℕ) (vs : List (List Bool))
    (nodup : vs.Nodup) (w : List Bool) (env : List ℕ) :
    (valueTableT value vs).denote w (env ++ [w.length]) =
      if w ∈ vs then value w else 0 := by
  induction vs with
  | nil => simp [valueTableT]
  | cons v vs ih =>
    obtain ⟨hv, ht⟩ := List.nodup_cons.mp nodup
    simp only [valueTableT, denote_add, denote_mul, denote_const, matchT_denote, ih ht,
      List.mem_cons]
    by_cases heq : w = v
    · subst w
      simp [hv]
    · simp [heq]

theorem valueTableT_le (value : List Bool → ℕ) (vs : List (List Bool))
    (w : List Bool) (env : List ℕ) :
    (valueTableT value vs).denote w env ≤ (vs.map value).sum := by
  induction vs with
  | nil => simp [valueTableT]
  | cons v vs ih =>
    simp only [valueTableT, denote_add, denote_mul, denote_const, List.map_cons, List.sum_cons]
    have hmatch := Nat.mul_le_mul_right (value v) (matchT_le (w := w) v env)
    simpa only [one_mul] using Nat.add_le_add hmatch ih

theorem tm_valueTableT (value : List Bool → ℕ) (vs : List (List Bool))
    {w : List Bool} {L : ℕ} {env : List ℕ} (hL : 2 ≤ L)
    (hlen : ∀ v ∈ vs, v.length < 2 ^ L) (hvalues : (vs.map value).sum < 2 ^ L)
    (hx : Tm w L 1 (lvl 0) env) : Tm w L 1 (valueTableT value vs) env := by
  induction vs with
  | nil => exact t_const (lit_lt_two_pow (by omega) hL)
  | cons v vs ih =>
    have hsum : value v + (vs.map value).sum < 2 ^ L := by
      simpa only [List.map_cons, List.sum_cons] using hvalues
    have htail := ih (fun u hu => hlen u (List.mem_cons_of_mem _ hu)) (by omega)
    have hmatch := tm_matchT (w := w) v hL (hlen v List.mem_cons_self) hx
    have hvalue : Tm w L 1 (const (value v)) env := t_const (by omega)
    have hmul : Tm w L 2 (mul (matchT v) (const (value v))) env :=
      t_mul hmatch hvalue (by omega)
    refine Tm.of_le (d := 3) (t_add hmul htail (by omega) (by omega)) fun env' => ?_
    simpa only [one_mul] using lt_of_le_of_lt (valueTableT_le value (v :: vs) w env') hvalues

end NtimeDspace.ProgTerm
