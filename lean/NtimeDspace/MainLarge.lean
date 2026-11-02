import NtimeDspace.MainCorrect
import NtimeDspace.ParamLarge
import NtimeDspace.SemanticReduction

/-!
# The main loop decides the language on large inputs

`eventually_main_correct`: for the machine data of an `NTIME` language, on all
inputs of large enough length, membership is positivity of the main loop.
-/

namespace NtimeDspace.ProgTerm

open Term LocalSim Turing Parameters Cslib.Complexity.CountingSimulation WeightedSystem
  NetworkSystem Placement Filter

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s}

theorem le_edgesN (k s t : ℕ) : t ≤ edgesN k s t :=
  (le_paddedTime t).trans (paddedTime_le_edgesN k s t)

theorem tendsto_edgesN (k s c : ℕ) (hc : 1 ≤ c) :
    Tendsto (fun n => edgesN k s (clk c n)) atTop atTop :=
  tendsto_atTop_mono (fun n => (show n ≤ clk c n by unfold clk; nlinarith).trans (le_edgesN k s _))
    tendsto_id

/-- **The main loop decides the language on large inputs.** -/
theorem eventually_main_correct [Finite State] {A : Set (List Bool)} {C : ℕ} (hc : 2 ≤ c)
    (hM : ∀ a : List Bool, (a ∈ A ↔ ∃ σ < scheduleCount (k + 1) (clk c a.length),
        0 < (blockNetworkOf machine e (a, clk c a.length, σ)).2.contraction) ∧
      ∀ σ, ExplicitAdmissible C (clk c a.length) (blockNetworkOf machine e (a, clk c a.length, σ))) :
    ∀ᶠ n in atTop, ∀ a : List Bool, a.length = n →
      (a ∈ A ↔ 0 < (mainT k s c e machine (lvl 0)).denote a [a.length]) := by
  have hT := tendsto_edgesN k s c (by omega)
  filter_upwards [hT.eventually (Polylog.tendsto_log2.eventually (eventually_ge_atTop (ParameterChoice.cost 6))),
    hT.eventually (eventually_ge_atTop 30),
    hT.eventually (Polylog.eventually_polylog_le 2 3),
    hT.eventually (Polylog.eventually_polylog_le (2 + C) 4)] with n hlarge h30 hp1 hp2
  intro a ha
  subst ha
  set t := clk c a.length
  set N := edgesN k s t
  have hpos : 0 < N := by omega
  rw [(hM a).1]
  refine (mainT_pos_iff hc hpos hlarge h30 (fun σ => ⟨_, ((hM a).2 σ).1⟩) (fun σ pos => ?_)).symm
  have hadm := (hM a).2 σ
  have hNE : (blockNetworkOf machine e (a, t, σ)).2.numEdges = N := numEdges_blockNetworkOf machine e a t σ
  have hdeg : (blockNetworkOf machine e (a, t, σ)).2.maxDegree ≤
      C * (blockNetworkOf machine e (a, t, σ)).2.numEdges.log2 := by
    refine hadm.2.2.1.trans (Nat.mul_le_mul_left _ ?_)
    rw [hNE, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (le_edgesN k s t)
  have := exists_balN_network _ _ C pos hadm.1 hdeg (by rw [hNE]; exact hlarge) (by rw [hNE]; exact hp1)
    (by rw [hNE]; exact hp2)
  have hk : ParameterChoice.choose (blockNetworkOf machine e (a, t, σ)).2.numEdges = kp k s c a.length := by
    rw [hNE]
  obtain ⟨sd, hsd, hb⟩ := this
  rw [hk] at hsd hb
  exact ⟨sd, hsd, hb⟩

end NtimeDspace.ProgTerm
