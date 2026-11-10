import NtimeDspace.DeciderValues
import NtimeDspace.NetSystemSpec
import NtimeDspace.TameIte
import NtimeDspace.TameV
import Mathlib.NumberTheory.Chebyshev

/-!
# Tier of stable powers

`tm_powT_stable`: a power of stable terms has tier `1` when its value is below `2^L`.
-/

namespace NtimeDspace.ProgTerm

open Term Cslib.Complexity.CountingSimulation LocalSim

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : Turing.MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool} {L : ℕ}

/-- Stable powers have tier `1` when their values are below `2^L`. -/
theorem tm_powT_stable {x y : Term} {env : List ℕ} {dx dy : ℕ} (hL : 8 ≤ L)
    (hx : Tm w L dx x env) (hxs : StableAt w x env) (hy : Tm w L dy y env) (hys : StableAt w y env)
    (hdy : dy ≤ 32) (hdx : dx ≤ 100)
    (hv : x.denote w env ^ y.denote w env < 2 ^ L) : Tm w L 1 (powT x y) env :=
  t_powT hx hxs hy hdy le_rfl (by omega) (fun pre _ => by rw [hxs pre, hys pre, one_mul]; exact hv)
    (by omega) (by omega)

end NtimeDspace.ProgTerm
