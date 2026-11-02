import NtimeDspace.MainFacts
import NtimeDspace.MainLarge
import NtimeDspace.Domination

/-!
# The budget satisfies the main loop's numeric facts

`eventually_mainFacts`: once `C0` bounds the machine constants (`bigC`), the
budget `L k s c C0 n` satisfies `MainFacts` for all large `n`, with degree
bound `C · log₂ N`.
-/

namespace NtimeDspace.Budget

open Parameters Cslib.Complexity.CountingSimulation ProgTerm Filter Turing LocalSim Placement

/-- A bound for the machine constants used by the decider. -/
def bigC (k s c C : ℕ) : ℕ :=
  keyCount k s * k + keyCount k s + width k + 3 ^ k + 4 * k + 3 * s + c + C + 100

variable {k s c C0 n : ℕ}

theorem poly_ge1 : (C0 + 8) * (lgN k s c n + 3) ^ 3 ≤ polyPart k s c C0 n := Nat.le_add_right _ _

theorem poly_ge2 : 8 * (bN c n + 1) * (C0 + 1) * (lgN k s c n + C0 + 3) ≤ polyPart k s c C0 n :=
  Nat.le_add_left _ _

theorem poly_add_le_L : polyPart k s c C0 n + C0 + 8 ≤ L k s c C0 n := by
  rw [L_eq]; omega

theorem pow3_le (m : ℕ) : 3 ^ m ≤ 2 ^ (2 * m) := by
  calc 3 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ (2 * m) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

set_option maxHeartbeats 1000000 in
-- Many independent arithmetic facts.
theorem mainFacts_of_large {C : ℕ} (hc : 2 ≤ c) (hlarge : ParameterChoice.cost 6 ≤ lgN k s c n)
    (hN72 : 72 ≤ NN k s c n) (hC0 : bigC k s c C ≤ C0) :
    MainFacts k s c n (L k s c C0 n) (C * lgN k s c n) := by
  unfold bigC at hC0
  have h3k : 0 < 3 ^ k := by positivity
  set N := NN k s c n with hN_def
  set lg := lgN k s c n with hlg_def
  set kk := kN k s c n with hkk_def
  set b := bN c n with hb_def
  set LL := L k s c C0 n with hLL_def
  have hLL : polyPart k s c C0 n + C0 + 8 ≤ LL := poly_add_le_L
  have hP1 : (C0 + 8) * (lg + 3) ^ 3 ≤ polyPart k s c C0 n := poly_ge1
  have hP2 : 8 * (b + 1) * (C0 + 1) * (lg + C0 + 3) ≤ polyPart k s c C0 n := poly_ge2
  have hconst0 : ∀ x ≤ C0, x < 2 ^ LL := fun x hx => const_lt (lt_of_le_of_lt hx Nat.lt_two_pow_self)
  have hL : 8 ≤ LL := by omega
  have hn : n < 2 ^ LL := lt_two_pow_L k s c C0 n (by omega)
  have hcube1 : N ^ 3 + 1 < 2 ^ LL := N_cube_lt
  have hcube : N ^ 3 < 2 ^ LL := by omega
  have hconst : 4 * k + s + c + 100 < 2 ^ LL := hconst0 _ (by omega)
  have hQ : Q kk ≤ lg := Q_le_lgN (L := LL) hL hn hcube hconst hc hlarge hN72
  have hk : kk ≤ lg := kN_le_lgN (L := LL) hL hn hcube hconst hc hlarge hN72
  have hq : q N kk ≤ N / 2 := q_le_N (L := LL) hL hn hcube hconst hc hlarge hN72
  have h6 : 6 ≤ kk := six_le_kN (L := LL) hL hn hcube hconst hc hlarge hN72
  have hV : verticesN k s (tN c n) ≤ N := verticesN_le (L := LL) hL hn hcube hconst hc hlarge hN72
  have hbpos : 1 ≤ b := one_le_blockLength _
  have hlgN : N.log2 = lg := rfl
  have hcub : (lg + 3) ^ 3 = (lg + 3) * (lg + 3) * (lg + 3) := by ring
  -- the label space
  have hD : (2 ^ kk * 2 ^ kk) ^ Q kk < 2 ^ LL := by
    have e1 : (2 ^ kk * 2 ^ kk) ^ Q kk = D kk := by
      rw [D, Parameters.s, ← pow_add, ← pow_mul, ← pow_mul]; congr 1; ring
    rw [e1]; exact D_lt
  have hDr : (2 ^ kk) ^ (2 * Q kk) < 2 ^ LL := D_lt
  -- the seed range
  have hblk : 2 ^ (2 * blk (Q kk) kk ((max N (verticesN k s (tN c n))).log2 + 1)) < 2 ^ LL := by
    rw [max_eq_left hV]
    refine Nat.pow_lt_pow_right (by norm_num) ?_
    unfold blk
    rw [hlgN]
    have hm : Q kk * kk ≤ lg * lg := Nat.mul_le_mul hQ hk
    have h1 : Q kk * kk * (lg + 1 + 1) ≤ lg * lg * (lg + 2) := Nat.mul_le_mul hm (by omega)
    have h2 : 2 * (lg * lg * (lg + 2)) < 8 * (lg + 3) ^ 3 := by
      have a1 : lg * lg * (lg + 2) ≤ (lg + 3) * (lg + 3) * (lg + 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      have a2 : 0 < (lg + 3) * (lg + 3) * (lg + 3) := by positivity
      rw [hcub]; omega
    have h3 : 8 * (lg + 3) ^ 3 ≤ (C0 + 8) * (lg + 3) ^ 3 := Nat.mul_le_mul_right _ (by omega)
    omega
  -- the parser capacity
  have hqL : q N kk < LL := by
    have hk0 : 0 < kk := by omega
    have hs0 : 0 < Parameters.s kk := s_pos kk
    have e : q N kk = 24 * N / Parameters.s kk := by
      unfold Parameters.q Parameters.R Parameters.Q
      rw [show 3 * N * (8 * Parameters.s kk * kk) = 24 * N * (Parameters.s kk * kk) by ring,
        show Parameters.s kk ^ 2 * kk = Parameters.s kk * (Parameters.s kk * kk) by ring]
      exact Nat.mul_div_mul_right _ _ (Nat.mul_pos hs0 hk0)
    have h1 : 24 * N / Parameters.s kk ≤ SupportBudget.limit N kk := by
      unfold SupportBudget.limit
      apply Nat.div_le_div_right
      have : 24 * N ≤ 24 * N * (2 * kk + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have h2 : SupportBudget.limit N kk + 1 < LL := limit_lt_L
    omega
  -- the measurement tuples
  have htup : (2 * (2 ^ kk) ^ (2 * Q kk) + 1) ^ tupleWidth k s c n < 2 ^ LL := by
    have hW : tupleWidth k s c n * ((2 * D kk + 1).log2 + 1) ≤ LL := tuple_le_L
    show (2 * D kk + 1) ^ tupleWidth k s c n < 2 ^ LL
    rcases Nat.eq_zero_or_pos (tupleWidth k s c n) with h0 | hpos
    · rw [h0, pow_zero]; exact Nat.one_lt_two_pow (by omega)
    · calc (2 * D kk + 1) ^ tupleWidth k s c n
          < (2 ^ ((2 * D kk + 1).log2 + 1)) ^ tupleWidth k s c n :=
            Nat.pow_lt_pow_left Nat.lt_log2_self (by omega)
        _ = 2 ^ (((2 * D kk + 1).log2 + 1) * tupleWidth k s c n) := (pow_mul _ _ _).symm
        _ ≤ 2 ^ LL := Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hW)
  -- the machine constants
  have hkey : keyCount k s * k + keyCount k s + width k + 3 ^ k < 2 ^ LL := hconst0 _ (by omega)
  -- the local radix
  have hRw : LocalSim.radix b n s ^ width k < 2 ^ LL := by
    set E' := 8 * b + lg + C0 + 1 with hE'
    have hb2 : 3 ^ (4 * b) ≤ 2 ^ (8 * b) := by
      have := pow3_le (4 * b); rw [show 2 * (4 * b) = 8 * b by ring] at this; exact this
    have hX1 : 2 ^ (8 * b) ≤ 2 ^ E' := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hnN : n ≤ N := (show n ≤ clk c n from
        Nat.le_add_right_of_le (Nat.le_mul_of_pos_left n (by omega))).trans
      ((le_paddedTime _).trans (paddedTime_le_edgesN k s _))
    have hNl : N < 2 ^ (lg + 1) := Nat.lt_log2_self
    have hX2 : n < 2 ^ E' := lt_of_le_of_lt hnN (lt_of_lt_of_le hNl
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have hX3 : s + 3 < 2 ^ E' := lt_of_lt_of_le (lt_of_le_of_lt (show s + 3 ≤ C0 by omega)
      Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : 2 ^ (E' + 2) = 4 * 2 ^ E' := by rw [pow_add]; ring
    have hrad : LocalSim.radix b n s < 2 ^ (E' + 2) := by unfold LocalSim.radix; omega
    have hw : width k ≤ C0 + 1 := by unfold width; omega
    have hwpos : width k ≠ 0 := by unfold width; omega
    have hEL : (E' + 2) * width k ≤ LL := by
      have h1 : (E' + 2) * width k ≤ (E' + 2) * (C0 + 1) := Nat.mul_le_mul_left _ hw
      have h2 : E' + 2 ≤ 8 * (b + 1) * (lg + C0 + 3) := by
        have a1 : 8 * (b + 1) * (lg + C0 + 3) = 8 * b * (lg + C0 + 3) + 8 * (lg + C0 + 3) := by ring
        have a2 : 8 * b ≤ 8 * b * (lg + C0 + 3) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h3 : (E' + 2) * (C0 + 1) ≤ 8 * (b + 1) * (C0 + 1) * (lg + C0 + 3) := by
        calc (E' + 2) * (C0 + 1) ≤ 8 * (b + 1) * (lg + C0 + 3) * (C0 + 1) := Nat.mul_le_mul_right _ h2
          _ = 8 * (b + 1) * (C0 + 1) * (lg + C0 + 3) := by ring
      omega
    calc LocalSim.radix b n s ^ width k < (2 ^ (E' + 2)) ^ width k := Nat.pow_lt_pow_left hrad hwpos
      _ = 2 ^ ((E' + 2) * width k) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ LL := Nat.pow_le_pow_right (by norm_num) hEL
  have hbig : 8 * (b + 1) ≤ 8 * (b + 1) * (C0 + 1) * (lg + C0 + 3) := by
    have h1 : 8 * (b + 1) ≤ 8 * (b + 1) * (C0 + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : 8 * (b + 1) * (C0 + 1) ≤ 8 * (b + 1) * (C0 + 1) * (lg + C0 + 3) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hbC : b * (C0 + 1) ≤ 8 * (b + 1) * (C0 + 1) * (lg + C0 + 3) := by
    have h1 : b * (C0 + 1) ≤ 8 * (b + 1) * (C0 + 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : 8 * (b + 1) * (C0 + 1) ≤ 8 * (b + 1) * (C0 + 1) * (lg + C0 + 3) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h3b : 3 ^ (3 * b) < 2 ^ LL := by
    have := pow3_le (3 * b)
    exact lt_of_le_of_lt this (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hccv : (s + 1) * (b ^ (k + 1) * 3) < 2 ^ LL := by
    have hbk : b ^ (k + 1) ≤ 2 ^ (b * (k + 1)) :=
      (Nat.pow_le_pow_left (Nat.lt_two_pow_self).le (k + 1)).trans_eq (pow_mul _ _ _).symm
    have hb1 : 1 ≤ b ^ (k + 1) := Nat.one_le_pow _ _ hbpos
    have h33 : (s + 1) * 3 < 2 ^ C0 := lt_of_le_of_lt (show (s + 1) * 3 ≤ C0 by omega) Nat.lt_two_pow_self
    have hm1 : (s + 1) * 3 * b ^ (k + 1) < 2 ^ C0 * 2 ^ (b * (k + 1)) :=
      calc (s + 1) * 3 * b ^ (k + 1) < 2 ^ C0 * b ^ (k + 1) := Nat.mul_lt_mul_of_pos_right h33 hb1
        _ ≤ 2 ^ C0 * 2 ^ (b * (k + 1)) := Nat.mul_le_mul_left _ hbk
    rw [← pow_add] at hm1
    have hbk1 : b * (k + 1) ≤ b * (C0 + 1) := Nat.mul_le_mul_left _ (by omega)
    calc (s + 1) * (b ^ (k + 1) * 3) = (s + 1) * 3 * b ^ (k + 1) := by ring
      _ < 2 ^ (C0 + b * (k + 1)) := hm1
      _ ≤ 2 ^ LL := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm0 : MultiTapePTM.letterBits k s b < LL := by
    unfold MultiTapePTM.letterBits
    have : (s + k + 4) * b ≤ b * (C0 + 1) := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hD0 : C * lg < LL := by
    have h1 : C * lg ≤ C0 * lg := Nat.mul_le_mul_right _ (by omega)
    have h2 : C0 * lg ≤ (C0 + 8) * (lg + 3) ^ 3 := by
      have : lg ≤ (lg + 3) ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) (lg + 3))
      exact Nat.mul_le_mul (by omega) this
    omega
  exact ⟨hL, hn, hcube, hcube1, hconst, hlarge, hN72, hD, hDr, limit_lt_L, hblk, group_lt_L, hqL,
    htup, hkey, hRw, h3b, hccv, hm0, schedules_lt, hD0⟩

/-- **The budget satisfies the numeric facts on large inputs.** -/
theorem eventually_mainFacts {C : ℕ} (hc : 2 ≤ c) (hC0 : bigC k s c C ≤ C0) :
    ∀ᶠ n in atTop, MainFacts k s c n (L k s c C0 n) (C * lgN k s c n) := by
  have hT := tendsto_edgesN k s c (by omega)
  filter_upwards [hT.eventually (Polylog.tendsto_log2.eventually
      (eventually_ge_atTop (ParameterChoice.cost 6))),
    hT.eventually (eventually_ge_atTop 72)] with n hlarge hN72
  exact mainFacts_of_large hc hlarge hN72 hC0

end NtimeDspace.Budget
