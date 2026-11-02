import NtimeDspace.BudgetValues
import NtimeDspace.TameIte

/-!
# Tiers of the decider's parameters

At input length `n` (on the environment), each parameter term has tier `1`
under any scale `L` with `n < 2^L`, `N³ < 2^L` and the machine constants
below `2^L`: `tame` bounds its evaluation and its value is at most `N³`.
-/

namespace NtimeDspace.ProgTerm

open Term Budget Parameters Cslib.Complexity.CountingSimulation

variable {w : List Bool} {k s c n L : ℕ}

theorem hx_stable : StableAt w (lvl 0) [n] := stableAt_lvl (by simp)
theorem hx_value : (lvl 0).denote w [n] = n := by simp [denote_lvl]

theorem tm_x (hn : n < 2 ^ L) : Tm w L 1 (lvl 0) [n] :=
  tm_lvl (by simp) (by rw [hx_value, one_mul]; exact hn)

/-- A stable parameter at most `N³` has tier `1`. -/
theorem tm_param {t : Term} {d : ℕ} (hcube : NN k s c n ^ 3 < 2 ^ L) (htm : Tm w L d t [n])
    (hs : StableAt w t [n]) (hv : t.denote w [n] ≤ NN k s c n ^ 3) : Tm w L 1 t [n] :=
  tm_retier htm hs (by rw [one_mul]; omega)

theorem N_le_cube : NN k s c n ≤ NN k s c n ^ 3 := Nat.le_self_pow (by norm_num) _

theorem tm_edgesNT (hL : 8 ≤ L) (hn : n < 2 ^ L) (hcube : NN k s c n ^ 3 < 2 ^ L)
    (hconst : 4 * k + s + c + 100 < 2 ^ L) : Tm w L 1 (edgesNT k s c (lvl 0)) [n] := by
  have hx := tm_x (w := w) hn
  refine tm_param (d := 16) hcube ?_ (StableAt.edgesNT hx_stable hx_value)
    (by rw [denote_edgesNT hx_stable hx_value]; exact N_le_cube)
  unfold edgesNT numBlocksT blockLenT clockT clogT ceilDivT
  tame

theorem stable_of_value {t : Term} {v : ℕ} (h : ∀ pre : List ℕ, t.denote w (pre ++ [n]) = v) :
    StableAt w t [n] := fun extra => by rw [h extra, ← h []]; rfl

section Values

variable (hL : 8 ≤ L) (hn : n < 2 ^ L) (hcube : NN k s c n ^ 3 < 2 ^ L)
  (hconst : 4 * k + s + c + 100 < 2 ^ L) (hc : 2 ≤ c)
  (hlarge : ParameterChoice.cost 6 ≤ lgN k s c n) (hN72 : 72 ≤ NN k s c n)
include hL hn hcube hconst hc hlarge hN72

theorem six_le_kN : 6 ≤ kN k s c n := ParameterChoice.six_le_selected _ hlarge

theorem lgN_le_N : lgN k s c n ≤ NN k s c n := by
  have h1 : lgN k s c n < 2 ^ lgN k s c n := Nat.lt_two_pow_self
  have h2 : 2 ^ lgN k s c n ≤ NN k s c n := Nat.log2_self_le (by omega)
  omega

theorem kN_le_lgN : kN k s c n ≤ lgN k s c n := ParameterChoice.selected_le_log2 _

theorem Q_le_lgN : Q (kN k s c n) ≤ lgN k s c n :=
  Q_le_log2 _ _ (by have := six_le_kN hL hn hcube hconst hc hlarge hN72; omega)
    (ParameterChoice.admissible _)

theorem R_le_lgN : R (kN k s c n) ≤ lgN k s c n :=
  R_le_log2 _ _ (by have := six_le_kN hL hn hcube hconst hc hlarge hN72; omega)
    (ParameterChoice.admissible _)

theorem q_le_N : q (NN k s c n) (kN k s c n) ≤ NN k s c n / 2 :=
  q_le_half _ _ (six_le_kN hL hn hcube hconst hc hlarge hN72)

theorem N_sq_le : NN k s c n * NN k s c n ≤ NN k s c n ^ 3 := by
  have : 1 ≤ NN k s c n := by omega
  calc NN k s c n * NN k s c n = NN k s c n ^ 2 := by ring
    _ ≤ NN k s c n ^ 3 := Nat.pow_le_pow_right this (by norm_num)

theorem cube_ge {x : ℕ} (hx : x ≤ 72 * NN k s c n) : x ≤ NN k s c n ^ 3 := by
  have h := N_sq_le hL hn hcube hconst hc hlarge hN72
  have : 72 * NN k s c n ≤ NN k s c n * NN k s c n := Nat.mul_le_mul_right _ hN72
  omega

theorem tm_kpT : Tm w L 1 (kpT k s c (lvl 0)) [n] := by
  have hx := tm_x (w := w) hn
  have hN := tm_edgesNT (w := w) hL hn hcube hconst
  refine tm_param (d := 100) hcube ?_ (StableAt.kpT hx_stable hx_value) ?_
  · unfold kpT chooseT lgNT log2T; tame
  · rw [denote_kpT hx_stable hx_value]
    exact cube_ge hL hn hcube hconst hc hlarge hN72
      (by have h1 := kN_le_lgN hL hn hcube hconst hc hlarge hN72
          have h2 := lgN_le_N hL hn hcube hconst hc hlarge hN72
          simp only [NN, tN, lgN, kN, kp] at *
          omega)

theorem tm_lgNT : Tm w L 1 (lgNT k s c (lvl 0)) [n] := by
  have hx := tm_x (w := w) hn
  have hN := tm_edgesNT (w := w) hL hn hcube hconst
  refine tm_param (d := 100) hcube ?_ (StableAt.lgNT hx_stable hx_value) ?_
  · unfold lgNT log2T; tame
  · rw [denote_lgNT hx_stable hx_value]
    exact cube_ge hL hn hcube hconst hc hlarge hN72
      (by have h2 := lgN_le_N hL hn hcube hconst hc hlarge hN72
          simp only [NN, tN, lgN, kN, kp] at *
          omega)

theorem lgN_lt_L : lgN k s c n < L := by
  have h := Nat.lt_log2_self (n := NN k s c n)
  have hN : NN k s c n < 2 ^ L := lt_of_le_of_lt (N_le_cube) hcube
  exact (Nat.log2_lt (by omega)).mpr hN

theorem tm_spT : Tm w L 1 (pow2 (kpT k s c (lvl 0))) [n] := by
  have hk := tm_kpT (w := w) hL hn hcube hconst hc hlarge hN72
  refine t_pow2_stable hk (by omega) (StableAt.kpT hx_stable hx_value) ?_ (by omega) (by omega)
  rw [denote_kpT hx_stable hx_value, one_mul]
  have h1 := kN_le_lgN hL hn hcube hconst hc hlarge hN72
  have h2 := lgN_lt_L hL hn hcube hconst hc hlarge hN72
  simp only [NN, tN, lgN, kN, kp] at *
  omega

theorem tm_QpT : Tm w L 1 (QpT k s c (lvl 0)) [n] := by
  have hk := tm_kpT (w := w) hL hn hcube hconst hc hlarge hN72
  have hs := tm_spT (w := w) hL hn hcube hconst hc hlarge hN72
  have hQs : StableAt w (QpT k s c (lvl 0)) [n] := fun extra => by
    rw [denote_QpT ((hx_stable).extend extra) (by rw [hx_stable extra, hx_value]),
      denote_QpT hx_stable hx_value]
  refine tm_param (d := 100) hcube ?_ hQs ?_
  · unfold QpT spT; tame
  · rw [denote_QpT hx_stable hx_value]
    have h1 := Q_le_lgN hL hn hcube hconst hc hlarge hN72
    have h2 := lgN_le_N hL hn hcube hconst hc hlarge hN72
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by simp only [NN, tN, lgN, kN, kp] at *; omega)

theorem tm_RpT : Tm w L 1 (RpT k s c (lvl 0)) [n] := by
  have hk := tm_kpT (w := w) hL hn hcube hconst hc hlarge hN72
  have hs := tm_spT (w := w) hL hn hcube hconst hc hlarge hN72
  have hRs : StableAt w (RpT k s c (lvl 0)) [n] := fun extra => by
    rw [denote_RpT ((hx_stable).extend extra) (by rw [hx_stable extra, hx_value]),
      denote_RpT hx_stable hx_value]
  refine tm_param (d := 100) hcube ?_ hRs ?_
  · unfold RpT spT; tame
  · rw [denote_RpT hx_stable hx_value]
    have h1 := R_le_lgN hL hn hcube hconst hc hlarge hN72
    have h2 := lgN_le_N hL hn hcube hconst hc hlarge hN72
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by simp only [NN, tN, lgN, kN, kp] at *; omega)

theorem tm_qpT1 : Tm w L 1 (add (qpT k s c (lvl 0)) (const 1)) [n] := by
  have hk := tm_kpT (w := w) hL hn hcube hconst hc hlarge hN72
  have hs := tm_spT (w := w) hL hn hcube hconst hc hlarge hN72
  have hN := tm_edgesNT (w := w) hL hn hcube hconst
  have hval : ∀ pre : List ℕ, (add (qpT k s c (lvl 0)) (const 1)).denote w (pre ++ [n]) =
      q (NN k s c n) (kN k s c n) + 1 := fun pre => by
    rw [denote_add, denote_qpT ((hx_stable).extend pre) (by rw [hx_stable pre, hx_value]),
      denote_const]
  refine tm_param (d := 100) hcube ?_ (stable_of_value hval) ?_
  · unfold qpT RpT QpT spT; tame
  · have := hval []; simp only [List.nil_append] at this; rw [this]
    have h1 := q_le_N hL hn hcube hconst hc hlarge hN72
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by omega)

theorem tm_qpT : Tm w L 1 (qpT k s c (lvl 0)) [n] := by
  have hk := tm_kpT (w := w) hL hn hcube hconst hc hlarge hN72
  have hs := tm_spT (w := w) hL hn hcube hconst hc hlarge hN72
  have hN := tm_edgesNT (w := w) hL hn hcube hconst
  have hval : ∀ pre : List ℕ, (qpT k s c (lvl 0)).denote w (pre ++ [n]) =
      q (NN k s c n) (kN k s c n) := fun pre =>
    denote_qpT ((hx_stable).extend pre) (by rw [hx_stable pre, hx_value])
  refine tm_param (d := 100) hcube ?_ (stable_of_value hval) ?_
  · unfold qpT RpT QpT spT; tame
  · have := hval []; simp only [List.nil_append] at this; rw [this]
    have h1 := q_le_N hL hn hcube hconst hc hlarge hN72
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by omega)

theorem tm_radixPT : Tm w L 1 (radixPT k s c (lvl 0)) [n] := by
  have hq := tm_qpT (w := w) hL hn hcube hconst hc hlarge hN72
  have hlg := tm_lgNT (w := w) hL hn hcube hconst hc hlarge hN72
  have hN := tm_edgesNT (w := w) hL hn hcube hconst
  have hval : ∀ pre : List ℕ, (radixPT k s c (lvl 0)).denote w (pre ++ [n]) =
      ParserFold.radix (NN k s c n) (q (NN k s c n) (kN k s c n)) := fun pre =>
    denote_radixPT ((hx_stable).extend pre) (by rw [hx_stable pre, hx_value])
  refine tm_param (d := 100) hcube ?_ (stable_of_value hval) ?_
  · unfold radixPT; tame
  · have := hval []; simp only [List.nil_append] at this; rw [this]
    have h1 := q_le_N hL hn hcube hconst hc hlarge hN72
    have h2 := lgN_le_N hL hn hcube hconst hc hlarge hN72
    unfold ParserFold.radix
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by simp only [NN, tN, lgN, kN, kp] at *; omega)

theorem verticesN_le : verticesN k s (tN c n) ≤ NN k s c n := by
  simp only [verticesN, NN, edgesN, tN, Turing.MultiTapePTM.letterBits]
  have hb : 1 ≤ blockLength (clk c n) := Cslib.Complexity.CountingSimulation.one_le_blockLength _
  set P := (3 * k + 1) * ((s + k + 4) * blockLength (clk c n))
  have hlb : 4 ≤ (s + k + 4) * blockLength (clk c n) :=
    le_trans (by omega : 4 ≤ s + k + 4) (Nat.le_mul_of_pos_right _ hb)
  have h1 : 3 * k + 2 ≤ P := le_trans (by omega : 3 * k + 2 ≤ (3 * k + 1) * 4) (Nat.mul_le_mul_left _ hlb)
  have h2 : numBlocks (clk c n) * (3 * k + 2) ≤ numBlocks (clk c n) * P := Nat.mul_le_mul_left _ h1
  have e : numBlocks (clk c n) * (3 * k + 1) * ((s + k + 4) * blockLength (clk c n)) =
      numBlocks (clk c n) * P := by simp only [P]; ring
  rw [e]
  omega

theorem tm_verticesT : Tm w L 1 (verticesT k s c (lvl 0)) [n] := by
  have hx := tm_x (w := w) hn
  refine tm_param (d := 100) hcube ?_ (StableAt.verticesT hx_stable hx_value) ?_
  · unfold verticesT numBlocksT blockLenT clockT clogT ceilDivT; tame
  · rw [denote_verticesT hx_stable hx_value]
    have := verticesN_le hL hn hcube hconst hc hlarge hN72
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by simp only [NN, tN] at *; omega)

theorem tm_numBlocksT : Tm w L 1 (numBlocksT c (lvl 0)) [n] := by
  have hx := tm_x (w := w) hn
  refine tm_param (d := 100) hcube ?_ (StableAt.numBlocksT hx_stable hx_value) ?_
  · unfold numBlocksT blockLenT clockT clogT ceilDivT; tame
  · rw [denote_numBlocksT hx_stable hx_value]
    have ht : 2 ≤ clk c n := by unfold clk; nlinarith
    have hb : 1 ≤ blockLength (clk c n) := Cslib.Complexity.CountingSimulation.one_le_blockLength _
    have h1 : numBlocks (clk c n) ≤ clk c n := by
      unfold numBlocks
      rw [Nat.ceilDiv_eq_add_pred_div, Nat.div_le_iff_le_mul_add_pred (by omega)]
      have : clk c n ≤ blockLength (clk c n) * clk c n := Nat.le_mul_of_pos_left _ hb
      omega
    have h2 : clk c n ≤ NN k s c n :=
      (le_paddedTime _).trans (paddedTime_le_edgesN k s _)
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by simp only [NN, tN] at *; omega)

theorem tm_blockLenT : Tm w L 1 (blockLenT c (lvl 0)) [n] := by
  have hx := tm_x (w := w) hn
  refine tm_param (d := 100) hcube ?_ (StableAt.blockLenT hx_stable hx_value) ?_
  · unfold blockLenT clockT clogT; tame
  · rw [denote_blockLenT hx_stable hx_value]
    have ht : 2 ≤ clk c n := by unfold clk; nlinarith
    have h1 := blockLength_le_self (clk c n) ht
    have h2 : clk c n ≤ NN k s c n :=
      (le_paddedTime _).trans (paddedTime_le_edgesN k s _)
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by simp only [NN, tN] at *; omega)

theorem tm_limitT : Tm w L 1 (limitT k s c (lvl 0)) [n] := by
  have hk := tm_kpT (w := w) hL hn hcube hconst hc hlarge hN72
  have hs := tm_spT (w := w) hL hn hcube hconst hc hlarge hN72
  have hN := tm_edgesNT (w := w) hL hn hcube hconst
  have hval : ∀ pre : List ℕ, (limitT k s c (lvl 0)).denote w (pre ++ [n]) =
      SupportBudget.limit (NN k s c n) (kN k s c n) := fun pre =>
    denote_limitT ((hx_stable).extend pre) (by rw [hx_stable pre, hx_value])
  refine tm_param (d := 100) hcube ?_ (stable_of_value hval) ?_
  · unfold limitT spT; tame
  · have := hval []; simp only [List.nil_append] at this; rw [this]
    have h1 := kN_le_lgN hL hn hcube hconst hc hlarge hN72
    have h2 := lgN_le_N hL hn hcube hconst hc hlarge hN72
    have h3 := lgN_lt_L hL hn hcube hconst hc hlarge hN72
    have hsN : Parameters.s (kN k s c n) ≤ NN k s c n := by
      have : Parameters.s (kN k s c n) ≤ 2 ^ lgN k s c n := Nat.pow_le_pow_right (by norm_num) h1
      exact this.trans (Nat.log2_self_le (by omega))
    have hsq := N_sq_le hL hn hcube hconst hc hlarge hN72
    have hlim : SupportBudget.limit (NN k s c n) (kN k s c n) ≤ 72 * (NN k s c n * NN k s c n) := by
      unfold SupportBudget.limit
      have hlt : lgN k s c n < NN k s c n :=
        lt_of_lt_of_le Nat.lt_two_pow_self (Nat.log2_self_le (by omega))
      have hkk : 2 * kN k s c n + 1 ≤ 2 * NN k s c n := by omega
      have h24 : 24 * NN k s c n * (2 * kN k s c n + 1) ≤ 48 * (NN k s c n * NN k s c n) := by
        calc 24 * NN k s c n * (2 * kN k s c n + 1) ≤ 24 * NN k s c n * (2 * NN k s c n) :=
              Nat.mul_le_mul_left _ hkk
          _ = 48 * (NN k s c n * NN k s c n) := by ring
      have hNsq : NN k s c n ≤ NN k s c n * NN k s c n := Nat.le_mul_self _
      calc (24 * NN k s c n * (2 * kN k s c n + 1) + Parameters.s (kN k s c n) - 1) /
            Parameters.s (kN k s c n)
          ≤ 24 * NN k s c n * (2 * kN k s c n + 1) + Parameters.s (kN k s c n) - 1 := Nat.div_le_self _ _
        _ ≤ 72 * (NN k s c n * NN k s c n) := by omega
    have h72 : 72 * (NN k s c n * NN k s c n) ≤ NN k s c n ^ 3 := by
      calc 72 * (NN k s c n * NN k s c n) ≤ NN k s c n * (NN k s c n * NN k s c n) :=
            Nat.mul_le_mul_right _ hN72
        _ = NN k s c n ^ 3 := by ring
    exact hlim.trans h72

theorem tm_inputBitsT : Tm w L 1 (inputBitsT k s c (lvl 0)) [n] := by
  have hN := tm_edgesNT (w := w) hL hn hcube hconst
  have hV := tm_verticesT (w := w) hL hn hcube hconst hc hlarge hN72
  have hpos : 0 < edgesN k s (clk c n) := by simp only [NN, tN] at hN72; omega
  have hval : ∀ pre : List ℕ, (inputBitsT k s c (lvl 0)).denote w (pre ++ [n]) =
      (max (edgesN k s (clk c n)) (verticesN k s (clk c n))).log2 + 1 := fun pre =>
    denote_inputBitsT ((hx_stable).extend pre) (by rw [hx_stable pre, hx_value]) hpos
  refine tm_param (d := 100) hcube ?_ (stable_of_value hval) ?_
  · unfold inputBitsT maxT log2T; tame
  · have := hval []; simp only [List.nil_append] at this; rw [this]
    have hv := verticesN_le hL hn hcube hconst hc hlarge hN72
    have h2 := lgN_le_N hL hn hcube hconst hc hlarge hN72
    simp only [NN, tN, lgN] at *
    rw [max_eq_left hv]
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by simp only [NN, tN]; omega)

theorem tm_startPT : Tm w L 1 (startPT k s c (lvl 0)) [n] := by
  have hk := tm_kpT (w := w) hL hn hcube hconst hc hlarge hN72
  have hs := tm_spT (w := w) hL hn hcube hconst hc hlarge hN72
  have hval : ∀ pre : List ℕ, (startPT k s c (lvl 0)).denote w (pre ++ [n]) =
      (Parameters.s (kN k s c n) * kN k s c n * (Parameters.s (kN k s c n) - 9) + 1) / 2 := fun pre => by
    have hxp : StableAt w (lvl 0) (pre ++ [n]) := (hx_stable (w := w) (n := n)).extend pre
    have hxv : (lvl 0).denote w (pre ++ [n]) = n := by rw [hx_stable pre, hx_value]
    simp only [startPT, denote_div, denote_add, denote_mul, denote_sub, denote_const]
    rw [denote_spT (k := k) (s := s) (c := c) hxp hxv, denote_kpT (k := k) (s := s) (c := c) hxp hxv]
  refine tm_param (d := 100) hcube ?_ (stable_of_value hval) ?_
  · unfold startPT spT; tame
  · have := hval []; simp only [List.nil_append] at this; rw [this]
    have hQ := Q_le_lgN hL hn hcube hconst hc hlarge hN72
    have h2 := lgN_le_N hL hn hcube hconst hc hlarge hN72
    have hle : (Parameters.s (kN k s c n) * kN k s c n * (Parameters.s (kN k s c n) - 9) + 1) / 2 ≤
        Q (kN k s c n) := by
      unfold Q
      have h1 : Parameters.s (kN k s c n) - 9 ≤ Parameters.s (kN k s c n) := Nat.sub_le _ _
      have h3 : Parameters.s (kN k s c n) * kN k s c n * (Parameters.s (kN k s c n) - 9) ≤
          Parameters.s (kN k s c n) * kN k s c n * Parameters.s (kN k s c n) := Nat.mul_le_mul_left _ h1
      have h4 : Parameters.s (kN k s c n) * kN k s c n * Parameters.s (kN k s c n) =
          Parameters.s (kN k s c n) ^ 2 * kN k s c n := by ring
      have h5 : 1 ≤ Parameters.s (kN k s c n) ^ 2 * kN k s c n := by
        have := six_le_kN hL hn hcube hconst hc hlarge hN72
        have : 1 ≤ Parameters.s (kN k s c n) ^ 2 := Nat.one_le_pow _ _ (s_pos _)
        nlinarith
      omega
    exact cube_ge hL hn hcube hconst hc hlarge hN72 (by simp only [NN, tN, lgN, kN] at *; omega)

/-- With the label space below `2^L`, the number of copies has tier `1`. -/
theorem tm_copiesT (hD : (2 ^ kN k s c n * 2 ^ kN k s c n) ^ Q (kN k s c n) < 2 ^ L) :
    Tm w L 1 (copiesT k s c (lvl 0)) [n] := by
  have hk := tm_kpT (w := w) hL hn hcube hconst hc hlarge hN72
  have hs := tm_spT (w := w) hL hn hcube hconst hc hlarge hN72
  have hQ := tm_QpT (w := w) hL hn hcube hconst hc hlarge hN72
  have hN := tm_edgesNT (w := w) hL hn hcube hconst
  have hks := StableAt.kpT (w := w) (k := k) (s := s) (c := c) (hx_stable (n := n)) (hx_value (n := n))
  have hQs : StableAt w (QpT k s c (lvl 0)) [n] := fun extra => by
    rw [denote_QpT ((hx_stable).extend extra) (by rw [hx_stable extra, hx_value]),
      denote_QpT hx_stable hx_value]
  have hpow : Tm w L 1 (powT (mul (pow2 (kpT k s c (lvl 0))) (pow2 (kpT k s c (lvl 0))))
      (QpT k s c (lvl 0))) [n] := by
    refine t_powT (t_mul hs hs (by omega)) (hks.pow2.mul hks.pow2) hQ (by omega) le_rfl (by omega)
      (fun pre _ => ?_) (by omega) (by omega)
    rw [((hks.pow2.mul hks.pow2)) pre, hQs pre, denote_mul, denote_pow2, denote_kpT hx_stable hx_value,
      denote_QpT hx_stable hx_value, one_mul]
    exact hD
  refine tm_param (d := 100) hcube ?_ (StableAt.copiesT hx_stable hx_value) ?_
  · unfold copiesT; tame
  · rw [denote_copiesT hx_stable hx_value]
    exact cube_ge hL hn hcube hconst hc hlarge hN72
      (le_trans (Nat.div_le_self _ _) (by simp only [NN, tN, kN, kp] at *; omega))

/-- With the local radix below `2^L`, the local radix term has tier `1`. -/
theorem tm_localRadixT (hRl : LocalSim.radix (blockLength (clk c n)) n s < 2 ^ L) :
    Tm w L 1 (localRadixT s c (lvl 0)) [n] := by
  have hx := tm_x (w := w) hn
  have hb := tm_blockLenT (w := w) hL hn hcube hconst hc hlarge hN72
  have hbs := StableAt.blockLenT (w := w) (c := c) (hx_stable (n := n)) (hx_value (n := n))
  have hpow : Tm w L 1 (powT (const 3) (mul (const 4) (blockLenT c (lvl 0)))) [n] := by
    refine t_powT (t_const (lit_lt_two_pow (by omega) (by omega))) (stableAt_const _ _)
      (t_mul (t_const (lit_lt_two_pow_big (by omega) (by omega))) hb (by omega)) (by omega) le_rfl
      (by omega) (fun pre _ => ?_) (by omega) (by omega)
    rw [denote_const, denote_mul, denote_const, hbs pre, denote_blockLenT hx_stable hx_value, one_mul]
    unfold LocalSim.radix at hRl
    omega
  refine tm_retier (d := 100) ?_ (StableAt.localRadixT hx_stable hx_value) ?_
  · unfold localRadixT; tame
  · rw [denote_localRadixT hx_stable hx_value, one_mul]; exact hRl

end Values

end NtimeDspace.ProgTerm
