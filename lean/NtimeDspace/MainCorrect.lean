import NtimeDspace.DeciderCorrect
import NtimeDspace.PrimeProduct

/-!
# The main loop decides positivity of some contraction

`mainT_pos_iff`: for large inputs, the main loop is positive exactly when
some schedule's block network has a positive contraction. A schedule with a
positive contraction below `2^N` is nonzero modulo some prime in `(4N², N³]`
(`PrimeProduct`), and for those primes the counter computes the contraction
(`counterAt_cast`).
-/

namespace NtimeDspace.ProgTerm

open Term LocalSim Turing Parameters Cslib.Complexity.CountingSimulation WeightedSystem
  NetworkSystem Placement PrimeProduct

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool}

set_option maxHeartbeats 4000000 in
theorem mainT_denote_eq
    (hpos : 0 < edgesN k s (clk c w.length))
    (hlarge : ParameterChoice.cost 6 ≤ (edgesN k s (clk c w.length)).log2)
    (hrows : ∀ σ, ∃ r, (blockNetworkOf machine e (w, clk c w.length, σ)).2.IsRowsFirstBipartite r)
    (hex : ∀ σ (pos : 0 < (blockNetworkOf machine e (w, clk c w.length, σ)).2.numEdges),
      ∃ sd < 2 ^ (2 * blk (Q (kp k s c w.length)) (kp k s c w.length)
        (WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos))),
        balN (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos)
          (Q (kp k s c w.length)) (kp k s c w.length) sd) :
    (mainT k s c e machine (lvl 0)).denote w [w.length] =
      ∑ σ ∈ Finset.range (3 ^ ((k + 1) * numBlocks (clk c w.length))),
        ∑ p ∈ Finset.range (edgesN k s (clk c w.length) ^ 3 + 1),
          if 4 * edgesN k s (clk c w.length) ^ 2 < p ∧ p.Prime ∧
            ¬ p ∣ (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction then 1 else 0 := by
  set N := edgesN k s (clk c w.length) with hN
  have hx0 : StableAt w (lvl 0) [w.length] := stableAt_lvl (by simp)
  have hx0v : (lvl 0).denote w [w.length] = w.length := by simp [denote_lvl]
  rw [mainT, denote_sumT _ _ [w.length] (fun σ => ∑ p ∈ Finset.range (N ^ 3 + 1),
    if 4 * N ^ 2 < p ∧ p.Prime ∧
      ¬ p ∣ (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction then 1 else 0)
    (fun acc σ => ?_)]
  · congr 1
    rw [powT_denote _ _ _ (stableAt_const _ _), denote_const, denote_mul, denote_const,
      denote_numBlocksT hx0 hx0v]
  · -- the inner loop at schedule `σ`
    set env1 := acc :: σ :: [w.length] with henv1
    have hx1 : StableAt w (lvl 0) env1 := stableAt_lvl (by simp [henv1])
    have hx1v : (lvl 0).denote w env1 = w.length := by simp [henv1, denote_lvl]
    have hN1 := StableAt.edgesNT (k := k) (s := s) (c := c) hx1 hx1v
    have hN1v := denote_edgesNT (k := k) (s := s) (c := c) hx1 hx1v
    rw [denote_sumT _ _ env1 (fun p => if 4 * N ^ 2 < p ∧ p.Prime ∧
      ¬ p ∣ (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction then 1 else 0)
      (fun acc2 p => ?_)]
    · congr 2
      simp only [denote_add, denote_mul, hN1v, denote_const]
      ring
    · set env2 := acc2 :: p :: env1 with henv2
      have hx2 : StableAt w (lvl 0) env2 := stableAt_lvl (by simp [henv2, henv1])
      have hx2v : (lvl 0).denote w env2 = w.length := by simp [henv2, henv1, denote_lvl]
      have hσ2 : StableAt w (lvl [w.length].length) env2 := stableAt_lvl (by simp [henv2, henv1])
      have hσ2v : (lvl [w.length].length).denote w env2 = σ := by simp [henv2, henv1, denote_lvl]
      have hp2 : StableAt w (lvl env1.length) env2 := stableAt_lvl (by simp [henv2])
      have hp2v : (lvl env1.length).denote w env2 = p := by rw [henv2]; exact denote_lvl_index env1 acc2 p
      have hN2v := denote_edgesNT (k := k) (s := s) (c := c) hx2 hx2v
      simp only [denote_ite, denote_mul, denote_lt, denote_const, hN2v, hp2v, denote_mod]
      rw [denote_primeT hp2, hp2v]
      by_cases h1 : 4 * N ^ 2 < p
      · by_cases h2 : p.Prime
        · have : Fact p.Prime := ⟨h2⟩
          obtain ⟨r, hr⟩ := hrows σ
          have hcast := counterAt_cast (machine := machine) (e := e) hx2 hx2v hσ2 hσ2v hp2 hp2v
            hpos hlarge h1 hr (hex σ)
          have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
          rw [hmod]
          have h1' : 4 * (N * N) < p := by rw [pow_two] at h1; exact h1
          rw [if_pos (by rw [if_pos h1', if_pos h2]; norm_num)]
          by_cases h3 : p ∣ (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction
          · rw [Nat.mod_eq_zero_of_dvd h3, if_neg (lt_irrefl 0), if_neg (fun h => h.2.2 h3)]
          · rw [if_pos (Nat.pos_of_ne_zero (fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0))),
              if_pos ⟨h1, h2, h3⟩]
        · rw [if_neg (by rw [if_neg h2, mul_zero]; exact lt_irrefl 0), if_neg (fun h => h2 h.2.1)]
      · have h1' : ¬ 4 * (N * N) < p := by rw [pow_two] at h1; exact h1
        rw [if_neg (by rw [if_neg h1', zero_mul]; exact lt_irrefl 0), if_neg (fun h => h1 h.1)]

theorem paddedTime_le_edgesN (k s t : ℕ) : paddedTime t ≤ edgesN k s t := by
  unfold paddedTime edgesN MultiTapePTM.letterBits
  calc numBlocks t * blockLength t ≤ numBlocks t * blockLength t * (2 * (3 * k + 1) * (s + k + 4)) :=
        Nat.le_mul_of_pos_right _ (by positivity)
    _ = 2 * (numBlocks t * (3 * k + 1) * ((s + k + 4) * blockLength t)) := by ring

theorem contraction_lt_two_pow [Finite State] (hc : 2 ≤ c) (σ : ℕ)
    (hσ : σ < scheduleCount (k + 1) (clk c w.length)) :
    (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction ≤
      2 ^ edgesN k s (clk c w.length) := by
  have ht : 2 ≤ clk c w.length := by unfold clk; nlinarith
  have hsum := sum_contraction_blockNetworkOf machine e w ht
  have h1 : (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction ≤
      machine.acceptCount w (paddedTime (clk c w.length)) := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun σ => (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hσ)
  exact h1.trans (Cslib.Complexity.acceptCount_le_two_pow.trans
    (Nat.pow_le_pow_right (by norm_num) (paddedTime_le_edgesN k s _)))

/-- **The main loop is positive exactly when some contraction is.** -/
theorem mainT_pos_iff [Finite State] (hc : 2 ≤ c)
    (hpos : 0 < edgesN k s (clk c w.length))
    (hlarge : ParameterChoice.cost 6 ≤ (edgesN k s (clk c w.length)).log2)
    (h30 : 30 ≤ edgesN k s (clk c w.length))
    (hrows : ∀ σ, ∃ r, (blockNetworkOf machine e (w, clk c w.length, σ)).2.IsRowsFirstBipartite r)
    (hex : ∀ σ (pos : 0 < (blockNetworkOf machine e (w, clk c w.length, σ)).2.numEdges),
      ∃ sd < 2 ^ (2 * blk (Q (kp k s c w.length)) (kp k s c w.length)
        (WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos))),
        balN (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos)
          (Q (kp k s c w.length)) (kp k s c w.length) sd) :
    0 < (mainT k s c e machine (lvl 0)).denote w [w.length] ↔
      ∃ σ < scheduleCount (k + 1) (clk c w.length),
        0 < (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction := by
  rw [mainT_denote_eq hpos hlarge hrows hex, Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  set N := edgesN k s (clk c w.length)
  constructor
  · rintro ⟨σ, hσ, hin⟩
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)] at hin
    obtain ⟨p, -, hp⟩ := hin
    split_ifs at hp with h
    · refine ⟨σ, by simpa [scheduleCount] using hσ, Nat.pos_of_ne_zero fun h0 => h.2.2 ?_⟩
      rw [h0]; exact dvd_zero p
    · exact absurd hp (lt_irrefl 0)
  · rintro ⟨σ, hσ, hcpos⟩
    refine ⟨σ, by simpa [scheduleCount] using hσ, ?_⟩
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    have hlt : (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction <
        ∏ p ∈ primesIoc (4 * N ^ 2) (N ^ 3), p :=
      (contraction_lt_two_pow hc σ hσ).trans_lt (two_pow_lt_prod_primes N h30)
    obtain ⟨p, hpS, hpd⟩ := exists_prime_not_dvd (fun p hp => (Finset.mem_filter.mp hp).2) hcpos hlt
    have hpS' := Finset.mem_filter.mp hpS
    have hIoc := Finset.mem_Ioc.mp hpS'.1
    refine ⟨p, Finset.mem_range.mpr (by omega), ?_⟩
    rw [if_pos ⟨hIoc.1, hpS'.2, hpd⟩]
    exact Nat.one_pos

end NtimeDspace.ProgTerm
