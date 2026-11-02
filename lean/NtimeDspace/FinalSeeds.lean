import NtimeDspace.MainLarge
import NtimeDspace.NetFacts
import NtimeDspace.NetSystemSpec
import NtimeDspace.Budget

/-!
# Balanced seeds and degrees for every schedule

For the admissible networks of an `NTIME` language, on all large inputs every
schedule's network has a balanced seed (`eventually_seeds`), and every vertex
has at most `C · log₂ N` ports (`ports_le`).
-/

namespace NtimeDspace.ProgTerm

open Term LocalSim Turing Parameters Cslib.Complexity.CountingSimulation WeightedSystem
  NetworkSystem Placement Filter Budget

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s}

/-- **Every schedule has a balanced seed** on large inputs. -/
theorem eventually_seeds {C : ℕ} (hc : 2 ≤ c)
    (hadm : ∀ (a : List Bool) σ, ExplicitAdmissible C (clk c a.length)
      (blockNetworkOf machine e (a, clk c a.length, σ))) :
    ∀ᶠ n in atTop, ∀ a : List Bool, a.length = n → ∀ σ,
      ∀ pos : 0 < (blockNetworkOf machine e (a, clk c a.length, σ)).2.numEdges,
        ∃ sd < 2 ^ (2 * blk (Q (kp k s c a.length)) (kp k s c a.length)
          (WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (a, clk c a.length, σ)).2 pos))),
          balN (toSystem (blockNetworkOf machine e (a, clk c a.length, σ)).2 pos)
            (Q (kp k s c a.length)) (kp k s c a.length) sd := by
  have hT := tendsto_edgesN k s c (by omega)
  filter_upwards [hT.eventually (Polylog.tendsto_log2.eventually (eventually_ge_atTop (ParameterChoice.cost 6))),
    hT.eventually (Polylog.eventually_polylog_le 2 3),
    hT.eventually (Polylog.eventually_polylog_le (2 + C) 4)] with n hlarge hp1 hp2
  intro a ha σ pos
  subst ha
  set t := clk c a.length
  set N := edgesN k s t
  have hadm' := hadm a σ
  have hNE : (blockNetworkOf machine e (a, t, σ)).2.numEdges = N := numEdges_blockNetworkOf machine e a t σ
  have hdeg : (blockNetworkOf machine e (a, t, σ)).2.maxDegree ≤
      C * (blockNetworkOf machine e (a, t, σ)).2.numEdges.log2 := by
    refine hadm'.2.2.1.trans (Nat.mul_le_mul_left _ ?_)
    rw [hNE, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (le_edgesN k s t)
  have := exists_balN_network _ _ C pos hadm'.1 hdeg (by rw [hNE]; exact hlarge) (by rw [hNE]; exact hp1)
    (by rw [hNE]; exact hp2)
  have hk : ParameterChoice.choose (blockNetworkOf machine e (a, t, σ)).2.numEdges = kp k s c a.length := by
    rw [hNE]
  obtain ⟨sd, hsd, hb⟩ := this
  rw [hk] at hsd hb
  exact ⟨sd, hsd, hb⟩

/-- **Every vertex has at most `C · log₂ N` ports.** -/
theorem ports_le {C : ℕ} (a : List Bool)
    (hadm : ∀ σ, ExplicitAdmissible C (clk c a.length) (blockNetworkOf machine e (a, clk c a.length, σ)))
    (hpos : 0 < edgesN k s (clk c a.length)) :
    ∀ σ, ∀ v < verticesN k s (tN c a.length),
      (MultiTapePTM.explicitPortsNum k (numBlocks (clk c a.length))
        (MultiTapePTM.letterBits k s (blockLength (clk c a.length))) σ v).length ≤
        C * lgN k s c a.length := by
  intro σ v hv
  set t := clk c a.length
  have hNE : (blockNetworkOf machine e (a, t, σ)).2.numEdges = edgesN k s t :=
    numEdges_blockNetworkOf machine e a t σ
  have pos : 0 < (blockNetworkOf machine e (a, t, σ)).2.numEdges := by rw [hNE]; exact hpos
  have hlenS := length_constraints_toSystem machine e a t σ pos
  have hv' : v < (toSystem (blockNetworkOf machine e (a, t, σ)).2 pos).constraints.length := by
    rw [hlenS]; exact hv
  have hsc := scope_length_toSystem machine e a t σ pos v hv'
  have hle := scope_length_le_maxDegree (blockNetworkOf machine e (a, t, σ)).2 pos ⟨v, hv'⟩
  have hmax : (blockNetworkOf machine e (a, t, σ)).2.maxDegree ≤ C * lgN k s c a.length := by
    refine (hadm σ).2.2.1.trans (Nat.mul_le_mul_left _ ?_)
    show Nat.log 2 t ≤ (edgesN k s t).log2
    rw [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (le_edgesN k s t)
  have h1 : (netPorts k s t σ v).length ≤ (blockNetworkOf machine e (a, t, σ)).2.maxDegree := by
    rw [← hsc]; exact hle
  exact h1.trans hmax

end NtimeDspace.ProgTerm
