import NtimeDspace.TameParams
import NtimeDspace.TameSeed
import NtimeDspace.DeciderCorrect

/-!
# Tier of the decider's seed

For a schedule term `σ` (stable), the seed term `seedAt σ` has tier `1`: the
search keeps tier `2`, and its value is a seed number below `2^(2·blk)`
when a balanced seed exists.
-/

namespace NtimeDspace.ProgTerm

open Term Budget Parameters Cslib.Complexity.CountingSimulation LocalSim Placement WeightedSystem
  NetworkSystem

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : Turing.MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool} {L : ℕ}

/-- The value of the seed term: the first balanced seed number, below the search range. -/
theorem seedAt_value {env : List ℕ} {σT : Term} {σ : ℕ}
    (hx : StableAt w (lvl 0) env) (hxv : (lvl 0).denote w env = w.length)
    (hσs : StableAt w σT env) (hσv : σT.denote w env = σ)
    (hpos : 0 < edgesN k s (clk c w.length))
    (hex : ∀ pos : 0 < (blockNetworkOf machine e (w, clk c w.length, σ)).2.numEdges,
      ∃ sd < 2 ^ (2 * blk (Q (kp k s c w.length)) (kp k s c w.length)
        (WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos))),
        balN (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos)
          (Q (kp k s c w.length)) (kp k s c w.length) sd) :
    StableAt w (seedAt k s c (lvl 0) σT) env ∧
      (seedAt k s c (lvl 0) σT).denote w env <
        2 ^ (2 * blk (Q (kp k s c w.length)) (kp k s c w.length)
          ((max (edgesN k s (clk c w.length)) (verticesN k s (clk c w.length))).log2 + 1)) ∧
      ∀ pos : 0 < (blockNetworkOf machine e (w, clk c w.length, σ)).2.numEdges,
        balN (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos)
          (Q (kp k s c w.length)) (kp k s c w.length) ((seedAt k s c (lvl 0) σT).denote w env) := by
  set t := clk c w.length
  set N := edgesN k s t
  set kk := kp k s c w.length
  have hNE : (blockNetworkOf machine e (w, t, σ)).2.numEdges = N := numEdges_blockNetworkOf machine e w t σ
  have pos : 0 < (blockNetworkOf machine e (w, t, σ)).2.numEdges := by rw [hNE]; exact hpos
  set S := toSystem (blockNetworkOf machine e (w, t, σ)).2 pos
  have hlenS : S.constraints.length = verticesN k s t := length_constraints_toSystem machine e w t σ pos
  have hq := StableAt.numBlocksT (c := c) hx hxv
  have hqv := denote_numBlocksT (c := c) hx hxv
  have hbl := StableAt.blockLenT (c := c) hx hxv
  have hblv := denote_blockLenT (c := c) hx hxv
  have iAR := implN_arityNT (k := k) (s := s) (σ := σ) hq hqv hbl hblv hσs hσv
  have iV := implN2_portAtT (k := k) (s := s) (σ := σ) hq hqv hbl hblv hσs hσv
  have hAR : ∀ v (h : v < S.constraints.length),
      (netPorts k s t σ v).length = (S.constraints[v]).scope.length := fun v hv =>
    (scope_length_toSystem machine e w t σ pos v hv).symm
  have hV : ∀ inc : Incidence S, (netPorts k s t σ inc.1).getD inc.2 0 = (incidenceVariable S inc).val :=
    fun inc => (scope_get_toSystem machine e w t σ pos inc.1 inc.1.isLt inc.2 inc.2.isLt).symm
  have hQs : StableAt w (QpT k s c (lvl 0)) env := fun extra => by
    rw [denote_QpT (hx.extend extra) (by rw [hx extra, hxv]), denote_QpT hx hxv]
  have hQv := denote_QpT (k := k) (s := s) (c := c) hx hxv
  have hks := StableAt.kpT (k := k) (s := s) (c := c) hx hxv
  have hkv := denote_kpT (k := k) (s := s) (c := c) hx hxv
  have hNs := StableAt.edgesNT (k := k) (s := s) (c := c) hx hxv
  have hNv := denote_edgesNT (k := k) (s := s) (c := c) hx hxv
  have hVs := StableAt.verticesT (k := k) (s := s) (c := c) hx hxv
  have hVv := denote_verticesT (k := k) (s := s) (c := c) hx hxv
  have hIBs : StableAt w (inputBitsT k s c (lvl 0)) env := fun extra => by
    rw [denote_inputBitsT (hx.extend extra) (by rw [hx extra, hxv]) hpos, denote_inputBitsT hx hxv hpos]
  have hIBv : (inputBitsT k s c (lvl 0)).denote w env = WSchedulePlacement.inputBits S := by
    rw [denote_inputBitsT hx hxv hpos, WSchedulePlacement.inputBits, SchedulePlacement.identifierBits,
      hlenS, hNE]
  have hspec := seed_spec S (Q kk) kk hQs hQv hks hkv hIBs hIBv hNs
    (by rw [hNv, hNE] <;> rfl) hVs (by rw [hVv, hlenS]) iAR hAR iV hV (hex pos)
  have hstab := hspec.1
  have hlt := seed_lt S (Q kk) kk hQs hQv hks hkv hIBs hIBv hNs
    (by rw [hNv, hNE] <;> rfl) hVs (by rw [hVv, hlenS]) iAR hAR iV hV (hex pos)
  refine ⟨hstab, ?_, fun pos' => hspec.2⟩
  have hIBe : WSchedulePlacement.inputBits S =
      (max (edgesN k s (clk c w.length)) (verticesN k s (clk c w.length))).log2 + 1 := by
    rw [← hIBv, denote_inputBitsT hx hxv hpos]
  rw [hIBe] at hlt
  exact hlt

end NtimeDspace.ProgTerm
