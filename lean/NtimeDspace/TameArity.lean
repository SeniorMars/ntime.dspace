import NtimeDspace.TameGraph
import NtimeDspace.TameIte
import NtimeDspace.NetValueBound

/-!
# Tier `1` for the arity and the ports

The arity is at most the number of edges and a port is below its square, so
both have tier `1` once these are below `2^L`.
-/

namespace NtimeDspace.ProgTerm

open Term LocalSim Turing

variable {w : List Bool} {L : ℕ} {env : List ℕ} {k s : ℕ}

section

variable {qT bT σT : Term} (hL : 8 ≤ L) (hq : Tm w L 1 qT env) (hb : Tm w L 1 bT env)
  (hσ : Tm w L 1 σT env) (hm1 : Tm w L 1 (letterBitsT k s bT) env) (hconst : 4 * k + 100 < 2 ^ L)
  (hEs : StableAt w (edgesT k s qT bT) env)
  (hE : (edgesT k s qT bT).denote w env * (edgesT k s qT bT).denote w env < 2 ^ L)
include hL hq hb hσ hm1 hconst hEs hE

set_option maxHeartbeats 0 in
theorem tm_arityNT1 : TmF w L (arityNT k s qT bT σT) 4 1 env := by
  have hpc := tm_portCountT (k := k) hL hq hm1 hσ hconst
  refine TmF.retier (d := 20) (fun env' he x hx => ?_) (fun env' he x => ?_)
  · unfold arityNT
    have hEt : Tm w L 4 (edgesT k s qT bT) env' := by unfold edgesT halvesT; tame1
    exact hpc.app he (hx.mono (by omega)) (hEt.mono (by omega))
  · have h1 := arityNT_le (w := w) (k := k) (s := s) qT bT σT x env'
    rw [hEs.extend'_eq he] at h1
    have : (edgesT k s qT bT).denote w env ≤ (edgesT k s qT bT).denote w env *
        (edgesT k s qT bT).denote w env := Nat.le_mul_self _
    rw [one_mul]; omega

set_option maxHeartbeats 0 in
theorem tm_portAtT1 : TmF2 w L (portAtT k s qT bT σT) 4 4 1 env := by
  have hpc := tm_portCountT (k := k) hL hq hm1 hσ hconst
  have hpp := tm_portPredT (k := k) hL hq hm1 hσ hconst
  refine TmF2.retier (d := 40) (fun env' he x y hx hy => ?_) (fun env' he x y => ?_)
  · unfold portAtT
    tame1
  · have h1 := portAtT_le (w := w) (k := k) (s := s) qT bT σT x y env'
    rw [hEs.extend'_eq he] at h1
    rw [one_mul]; omega

end

end NtimeDspace.ProgTerm
