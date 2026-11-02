/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.WeightedCounterTerm
import NtimeDspace.TameIte

-- upstream: local-only (register bounds for the selected weighted counter)

/-!
# Tiers of the weighted counter's parameters

Stable variable and constraint counts supply the selected arithmetic parameters
without a machine encoding. The hypotheses bound the actual register values;
the separate weighted budget discharges these inequalities asymptotically.
The arity sum counts ordered incidences, so repeated scope positions are included.
-/

namespace NtimeDspace.WeightedCounterTerm

open ProgTerm ProgTerm.Term Parameters WeightedSystem Placement

variable {w : List Bool} {env : List ℕ} {nT mT : Term} {N L : ℕ}

private theorem retier_cube {t : Term} {d : ℕ} (hcube : N ^ 3 < 2 ^ L)
    (ht : Tm w L d t env) (hs : StableAt w t env) (hv : t.denote w env ≤ N ^ 3) :
    Tm w L 1 t env :=
  tm_retier ht hs (by rw [one_mul]; exact hv.trans_lt hcube)

private theorem linear_le_cube (h72 : 72 ≤ N) {v : ℕ} (hv : v ≤ 72 * N) :
    v ≤ N ^ 3 := by
  have h1 : 72 * N ≤ N * N := Nat.mul_le_mul_right _ h72
  have h2 : N * N ≤ N ^ 3 := by
    rw [← pow_two]
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  exact hv.trans (h1.trans h2)

private theorem log_lt_self (h72 : 72 ≤ N) : N.log2 < N :=
  Nat.lt_two_pow_self.trans_le (Nat.log2_self_le (by omega))

theorem selected_lt_L (h72 : 72 ≤ N) (hcube : N ^ 3 < 2 ^ L) : ParameterChoice.choose N < L := by
  have hbound : N < 2 ^ L := (Nat.le_self_pow (by norm_num) N).trans_lt hcube
  exact (ParameterChoice.selected_le_log2 N).trans_lt
    ((Nat.log2_lt (by omega)).mpr hbound)


section Parameters

variable (hL : 8 ≤ L) (hn : StableAt w nT env) (hnv : nT.denote w env = N)
    (hN : Tm w L 1 nT env) (h72 : 72 ≤ N) (hcube : N ^ 3 < 2 ^ L)
    (hk6 : 6 ≤ ParameterChoice.choose N)
include hL hn hnv hN h72 hcube

theorem tm_lgT : Tm w L 1 (lgT nT) env := by
  refine retier_cube (d := 100) hcube ?_ (stable_lgT hn) ?_
  · unfold lgT log2T; tame
  · rw [denote_lgT hn, hnv]
    exact linear_le_cube h72 (by have := log_lt_self h72; omega)

theorem tm_kT : Tm w L 1 (kT nT) env := by
  refine retier_cube (d := 100) hcube ?_ (stable_kT hn) ?_
  · unfold kT chooseT lgT log2T; tame
  · rw [denote_kT hn, hnv]
    exact linear_le_cube h72 (by
      have := ParameterChoice.selected_le_log2 N
      have := log_lt_self h72
      omega)


theorem tm_sT : Tm w L 1 (sT nT) env := by
  refine t_pow2_stable (tm_kT hL hn hnv hN h72 hcube) (by omega) (stable_kT hn)
    ?_ (by omega) (by omega)
  rw [denote_kT hn, hnv, one_mul]
  exact selected_lt_L h72 hcube

include hk6

theorem tm_QT : Tm w L 1 (QT nT) env := by
  have hk := tm_kT hL hn hnv hN h72 hcube
  have hs := tm_sT hL hn hnv hN h72 hcube
  refine retier_cube (d := 100) hcube ?_ (stable_QT hn) ?_
  · unfold QT; tame
  · rw [denote_QT hn, hnv]
    exact (Q_le_log2 _ _ (by omega) (ParameterChoice.admissible N)).trans
      (linear_le_cube h72 (by have := log_lt_self h72; omega))

theorem tm_RT : Tm w L 1 (RT nT) env := by
  have hk := tm_kT hL hn hnv hN h72 hcube
  have hs := tm_sT hL hn hnv hN h72 hcube
  refine retier_cube (d := 100) hcube ?_ (stable_RT hn) ?_
  · unfold RT; tame
  · rw [denote_RT hn, hnv]
    exact (R_le_log2 _ _ (by omega) (ParameterChoice.admissible N)).trans
      (linear_le_cube h72 (by have := log_lt_self h72; omega))

theorem tm_qT : Tm w L 1 (qT nT) env := by
  have hQ := tm_QT hL hn hnv hN h72 hcube hk6
  have hR := tm_RT hL hn hnv hN h72 hcube hk6
  refine retier_cube (d := 100) hcube ?_ (stable_qT hn) ?_
  · unfold qT; tame
  · rw [denote_qT hn, hnv]
    exact linear_le_cube h72 (by have := q_le_half N _ hk6; omega)

theorem tm_orderT : Tm w L 1 (add (qT nT) (const 1)) env := by
  have hq := tm_qT hL hn hnv hN h72 hcube hk6
  refine retier_cube (d := 100) hcube ?_ ((stable_qT hn).add (stableAt_const _ _)) ?_
  · tame
  · rw [denote_add, denote_qT hn, hnv, denote_const]
    exact linear_le_cube h72 (by have := q_le_half N _ hk6; omega)

theorem tm_radixT : Tm w L 1 (radixT nT) env := by
  have hq := tm_qT hL hn hnv hN h72 hcube hk6
  have hlg := tm_lgT hL hn hnv hN h72 hcube
  refine retier_cube (d := 100) hcube ?_ (stable_radixT hn) ?_
  · unfold radixT; tame
  · rw [denote_radixT hn, hnv]
    unfold ParserFold.radix
    exact linear_le_cube h72 (by
      have := q_le_half N _ hk6
      have := log_lt_self h72
      omega)

omit hk6 in
theorem tm_limitT : Tm w L 1 (limitT nT) env := by
  have hk := tm_kT hL hn hnv hN h72 hcube
  have hs := tm_sT hL hn hnv hN h72 hcube
  refine retier_cube (d := 100) hcube ?_ (stable_limitT hn) ?_
  · unfold limitT; tame
  · rw [denote_limitT hn, hnv]
    have hkN := (ParameterChoice.selected_le_log2 N).trans_lt (log_lt_self h72)
    have hsN : s (ParameterChoice.choose N) ≤ N :=
      (Nat.pow_le_pow_right (by norm_num) (ParameterChoice.selected_le_log2 N)).trans
        (Nat.log2_self_le (by omega))
    have hkk : 2 * ParameterChoice.choose N + 1 ≤ 2 * N := by omega
    have h24 : 24 * N * (2 * ParameterChoice.choose N + 1) ≤ 48 * (N * N) := by
      calc 24 * N * (2 * ParameterChoice.choose N + 1) ≤ 24 * N * (2 * N) :=
            Nat.mul_le_mul_left _ hkk
        _ = 48 * (N * N) := by ring
    have hNsq : N ≤ N * N := Nat.le_mul_self _
    have h72sq : 72 * (N * N) ≤ N ^ 3 := by
      calc 72 * (N * N) ≤ N * (N * N) := Nat.mul_le_mul_right _ h72
        _ = N ^ 3 := by ring
    unfold SupportBudget.limit
    exact (Nat.div_le_self _ _).trans (by omega)

theorem tm_startT : Tm w L 1 (startT nT) env := by
  have hk := tm_kT hL hn hnv hN h72 hcube
  have hs := tm_sT hL hn hnv hN h72 hcube
  refine retier_cube (d := 100) hcube ?_ (stable_startT hn) ?_
  · unfold startT; tame
  · rw [denote_startT hn, hnv]
    have hle : (s (ParameterChoice.choose N) * ParameterChoice.choose N *
        (s (ParameterChoice.choose N) - 9) + 1) / 2 ≤ Q (ParameterChoice.choose N) := by
      have h1 := Nat.mul_le_mul_left (s (ParameterChoice.choose N) * ParameterChoice.choose N)
        (Nat.sub_le (s (ParameterChoice.choose N)) 9)
      have h2 : s (ParameterChoice.choose N) * ParameterChoice.choose N *
          s (ParameterChoice.choose N) = Q (ParameterChoice.choose N) := by unfold Q; ring
      have h3 : 1 ≤ Q (ParameterChoice.choose N) := by
        unfold Q
        have := Nat.one_le_pow 2 _ (s_pos (ParameterChoice.choose N))
        nlinarith
      omega
    exact hle.trans ((Q_le_log2 _ _ (by omega) (ParameterChoice.admissible N)).trans
      (linear_le_cube h72 (by have := log_lt_self h72; omega)))

end Parameters

/-- The identifier width is small even when the constraint count exceeds the
variable count. Only the two supplied tier-one count terms are needed. -/
theorem tm_inputBitsT (hL : 8 ≤ L) (hn : StableAt w nT env) (hm : StableAt w mT env)
    (hN : Tm w L 1 nT env) (hM : Tm w L 1 mT env) :
    Tm w L 1 (inputBitsT nT mT) env := by
  refine tm_retier (d := 100) ?_ (stable_inputBitsT hn hm) ?_
  · unfold inputBitsT lgT maxT log2T; tame
  · rw [denote_inputBitsT hn hm, one_mul]
    have hmax : max (nT.denote w env) (mT.denote w env) < 2 ^ L := by
      have h1 := hN.lt
      have h2 := hM.lt
      simpa only [one_mul, max_lt_iff] using And.intro h1 h2
    have hlog : (max (nT.denote w env) (mT.denote w env)).log2 < L := by
      rcases Nat.eq_zero_or_pos (max (nT.denote w env) (mT.denote w env)) with h0 | hpos
      · simp only [h0, Nat.log2_zero]; omega
      · exact (Nat.log2_lt (by omega)).mpr hmax
    exact (by omega : (max (nT.denote w env) (mT.denote w env)).log2 + 1 ≤ L).trans_lt
      Nat.lt_two_pow_self

/-- The label-space power is evaluated under its explicit magnitude bound. -/
theorem tm_DT (hL : 8 ≤ L) (hn : StableAt w nT env) (hnv : nT.denote w env = N)
    (hN : Tm w L 1 nT env) (h72 : 72 ≤ N) (hcube : N ^ 3 < 2 ^ L)
    (hk6 : 6 ≤ ParameterChoice.choose N)
    (hD : (2 ^ ParameterChoice.choose N * 2 ^ ParameterChoice.choose N) ^
      Q (ParameterChoice.choose N) < 2 ^ L) : Tm w L 1 (DT nT) env := by
  have hs := tm_sT hL hn hnv hN h72 hcube
  have hQ := tm_QT hL hn hnv hN h72 hcube hk6
  refine t_powT (t_mul hs hs (by omega)) ((stable_sT hn).mul (stable_sT hn))
    hQ (by omega) le_rfl (by omega) (fun pre _ => ?_) (by omega) (by omega)
  change (mul (sT nT) (sT nT)).denote w (pre ++ env) ^
    (QT nT).denote w (pre ++ env) < 2 ^ (1 * L)
  rw [((stable_sT hn).mul (stable_sT hn)) pre, stable_QT hn pre, denote_mul,
    denote_sT hn, denote_QT hn, hnv, one_mul]
  exact hD

/-- The incidence scan and its copy count use the supplied arity accessor,
including constraints of arity zero and repeated variable positions. -/
theorem tm_copiesT (S : System N) {arity : Term → Term} {AR : ℕ → ℕ}
    (hL : 8 ≤ L) (hn : StableAt w nT env) (hnv : nT.denote w env = N)
    (hm : StableAt w mT env) (hmv : mT.denote w env = S.constraints.length)
    (hN : Tm w L 1 nT env) (hM : Tm w L 1 mT env) (h72 : 72 ≤ N)
    (hcube : N ^ 3 < 2 ^ L) (hk6 : 6 ≤ ParameterChoice.choose N)
    (hD : (2 ^ ParameterChoice.choose N * 2 ^ ParameterChoice.choose N) ^
      Q (ParameterChoice.choose N) < 2 ^ L)
    (hinc : incidenceCount S ≤ 3 * N)
    (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = S.constraints[e].scope.length)
    (har : TmF w L arity 4 1 env) : Tm w L 1 (copiesT nT mT arity) env := by
  have hI : Tm w L 2 (incidenceT mT arity) env :=
    t_sumT hM (har.mono_in (by omega)) (by omega) (by omega)
  have hDT := tm_DT hL hn hnv hN h72 hcube hk6 hD
  refine retier_cube (d := 100) hcube ?_ (stable_copiesT S hn hm hmv iAR hAR) ?_
  · unfold copiesT; tame
  · simp only [copiesT, denote_div, denote_mul, denote_const, denote_incidenceT S hmv iAR hAR]
    exact (Nat.div_le_self _ _).trans (linear_le_cube h72 (by omega))

end NtimeDspace.WeightedCounterTerm
