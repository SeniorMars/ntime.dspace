import NtimeDspace.WeightTerm
import NtimeDspace.TameTac

/-!
Regression checks for the running flat-weight term and its tame-loop rule.
The first example distinguishes the new product from the old globally
truncated weight; the other examples test zero order and an empty factor list.
-/

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term

-- Factors (1+z)⁻¹ and (2+z)⁻², each truncated at order two, evaluated at z=3.
-- Their flat product is 1 modulo 7; truncating the product first would give 4.
example : (weightT (const 7) (const 2) (const 2)
    (fun i => add i (const 1)) (fun i => add i (const 1)) (const 3)).denote [] [] = 1 := by
  decide

example : (weightT (const 7) (const 0) (const 2)
    (fun _ => const 1) (fun _ => const 1) (const 3)).denote [] [] = 0 := by
  decide

example : (weightT (const 7) (const 0) (const 0)
    (fun _ => const 1) (fun _ => const 1) (const 3)).denote [] [] = 1 := by
  decide

-- A representative client uses the registered modular-fold rule to certify
-- the Horner accumulator.
example {w : List Bool} {L : ℕ} {env : List ℕ} {p x a m z : Term}
    (hL : 8 ≤ L) (hp : Tm w L 1 p env) (hpos : Pos w L p env)
    (hx : Tm w L 1 x env) (ha : Tm w L 1 a env)
    (hm : Tm w L 1 m env) (hz : Tm w L 1 z env) :
    Tm w L 1 (factorWeightT p x a m z) env := by
  tame
