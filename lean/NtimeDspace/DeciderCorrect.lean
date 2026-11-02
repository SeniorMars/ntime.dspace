import NtimeDspace.DeciderValues
import NtimeDspace.SeedSpec
import NtimeDspace.NetFacts
import NtimeDspace.NetworkCounter

/-!
# The decider's counter computes the contraction modulo `p`

`counterAt_cast`: at input `w`, schedule `σ` and a prime `p > 4N²`, the
counter term computes the contraction of the block network of `σ` modulo
`p`, for inputs large enough that `6 ≤ k`, when the network is rows-first
bipartite and a balanced seed number exists.
-/

namespace NtimeDspace.ProgTerm

open Term LocalSim Turing Parameters Cslib.Complexity.CountingSimulation WeightedSystem
  NetworkSystem Placement

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool}

set_option maxHeartbeats 4000000 in
theorem counterAt_cast {env : List ℕ} {xT σT pT : Term} {σ P r : ℕ} [Fact P.Prime]
    (hx : StableAt w xT env) (hxv : xT.denote w env = w.length)
    (hσs : StableAt w σT env) (hσv : σT.denote w env = σ)
    (hps : StableAt w pT env) (hpv : pT.denote w env = P)
    (hpos : 0 < edgesN k s (clk c w.length))
    (hlarge : ParameterChoice.cost 6 ≤ (edgesN k s (clk c w.length)).log2)
    (hP : 4 * edgesN k s (clk c w.length) ^ 2 < P)
    (hrows : (blockNetworkOf machine e (w, clk c w.length, σ)).2.IsRowsFirstBipartite r)
    (hex : ∀ pos : 0 < (blockNetworkOf machine e (w, clk c w.length, σ)).2.numEdges,
      ∃ sd < 2 ^ (2 * blk (Q (kp k s c w.length)) (kp k s c w.length)
        (WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos))),
        balN (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos)
          (Q (kp k s c w.length)) (kp k s c w.length) sd) :
    ((counterAt k s c e machine xT σT pT).denote w env : ZMod P) =
      ((blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction : ZMod P) := by
  set t := clk c w.length with ht
  set N := edgesN k s t with hN
  set kk := kp k s c w.length with hkk
  have hNE : (blockNetworkOf machine e (w, t, σ)).2.numEdges = N := numEdges_blockNetworkOf machine e w t σ
  have pos : 0 < (blockNetworkOf machine e (w, t, σ)).2.numEdges := by rw [hNE]; exact hpos
  set S := toSystem (blockNetworkOf machine e (w, t, σ)).2 pos with hS
  have six := ParameterChoice.six_le_selected N hlarge
  have kpos : 0 < kk := lt_of_lt_of_le (by norm_num) six
  obtain ⟨hQP, hRP, hqP, _⟩ :=
    scalar_parameter_bounds N kk P six hpos (ParameterChoice.admissible N) hP
  have hflat := flat_scalar_no_alias N kk P six hpos (ParameterChoice.admissible N) hP
  have hinc : incidenceCount S = 2 * N := by
    rw [hS, incidenceCount_eq_two_mul _ pos hrows, hNE]
  have hlenS : S.constraints.length = verticesN k s t := by
    rw [hS, length_constraints_toSystem machine e w t σ pos]
  -- the network accessors
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
  -- the parameters
  have hQs : StableAt w (QpT k s c xT) env := fun extra => by
    rw [denote_QpT (hx.extend extra) (by rw [hx extra, hxv]), denote_QpT hx hxv]
  have hQv := denote_QpT (k := k) (s := s) (c := c) hx hxv
  have hks := StableAt.kpT (k := k) (s := s) (c := c) hx hxv
  have hkv := denote_kpT (k := k) (s := s) (c := c) hx hxv
  have hNs := StableAt.edgesNT (k := k) (s := s) (c := c) hx hxv
  have hNv := denote_edgesNT (k := k) (s := s) (c := c) hx hxv
  have hVs := StableAt.verticesT (k := k) (s := s) (c := c) hx hxv
  have hVv := denote_verticesT (k := k) (s := s) (c := c) hx hxv
  have hIBs : StableAt w (inputBitsT k s c xT) env := fun extra => by
    rw [denote_inputBitsT (hx.extend extra) (by rw [hx extra, hxv]) hpos, denote_inputBitsT hx hxv hpos]
  have hIBv : (inputBitsT k s c xT).denote w env = WSchedulePlacement.inputBits S := by
    rw [denote_inputBitsT hx hxv hpos, WSchedulePlacement.inputBits, SchedulePlacement.identifierBits,
      hlenS, hNE]
  obtain ⟨hseedS, hseedB⟩ := seed_spec S (Q kk) kk hQs hQv hks hkv hIBs hIBv hNs
    (by rw [hNv, hNE] <;> rfl) hVs (by rw [hVv, hlenS]) iAR hAR iV hV (hex pos)
  have hqs : StableAt w (qpT k s c xT) env := fun extra => by
    rw [denote_qpT (hx.extend extra) (by rw [hx extra, hxv]), denote_qpT hx hxv]
  have hqpv := denote_qpT (k := k) (s := s) (c := c) hx hxv
  have hlgs := StableAt.lgNT (k := k) (s := s) (c := c) hx hxv
  have hlgv := denote_lgNT (k := k) (s := s) (c := c) hx hxv
  have hMs : StableAt w (radixPT k s c xT) env := fun extra => by
    rw [denote_radixPT (hx.extend extra) (by rw [hx extra, hxv]), denote_radixPT hx hxv]
  have hMv := denote_radixPT (k := k) (s := s) (c := c) hx hxv
  have hKs : StableAt w (limitT k s c xT) env := fun extra => by
    rw [denote_limitT (hx.extend extra) (by rw [hx extra, hxv]), denote_limitT hx hxv]
  have hKv := denote_limitT (k := k) (s := s) (c := c) hx hxv
  have hRs : StableAt w (RpT k s c xT) env := fun extra => by
    rw [denote_RpT (hx.extend extra) (by rw [hx extra, hxv]), denote_RpT hx hxv]
  have hRv := denote_RpT (k := k) (s := s) (c := c) hx hxv
  have hsPs : StableAt w (startPT k s c xT) env := fun extra => by
    simp only [startPT, denote_div, denote_add, denote_mul, denote_sub, denote_const,
      (StableAt.spT (k := k) (s := s) (c := c) hx hxv) extra, hks extra]
  have hcps := StableAt.copiesT (k := k) (s := s) (c := c) hx hxv
  have hcpv := denote_copiesT (k := k) (s := s) (c := c) hx hxv
  have hLRs := StableAt.localRadixT (s := s) (c := c) hx hxv
  have hLRv := denote_localRadixT (s := s) (c := c) hx hxv
  have hdeg : incidenceCount S * (R kk - 1) ≤
      3 * (blockNetworkOf machine e (w, t, σ)).2.numEdges * R kk := by
    rw [hinc, hNE]
    exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (Nat.sub_le _ _)
  have hcap : incidenceCount S * (R kk - 1) <
      Q kk * (q (blockNetworkOf machine e (w, t, σ)).2.numEdges kk + 1) :=
    lt_of_le_of_lt hdeg (degree_below_QJ _ kk kpos)
  have halias : incidenceCount S * (R kk - 1) +
      Q kk * q (blockNetworkOf machine e (w, t, σ)).2.numEdges kk ≤ P - 2 := by
    rw [hinc, hNE] at hdeg ⊢
    exact (Nat.add_le_add_right hdeg _).trans hflat
  have pp : ParserParams w env (blockNetworkOf machine e (w, t, σ)).2.numEdges
      (Parameters.q (blockNetworkOf machine e (w, t, σ)).2.numEdges kk)
      (SupportBudget.limit (blockNetworkOf machine e (w, t, σ)).2.numEdges kk)
      (edgesNT k s c xT) (qpT k s c xT) (lgNT k s c xT) (radixPT k s c xT) (limitT k s c xT) :=
    ⟨hNs, (by rw [hNv, hNE]), hqs, (by rw [hqpv, hNE]), hlgs, (by rw [hlgv, hNE]), hMs,
      (by rw [hMv, hNE]), hKs, (by rw [hKv, hNE])⟩
  have := networkCounterT_eq (machine := machine) (e := e) (w := w) (P := P) (Q := Q kk)
    (bits := kk) (kk := kk) (sd := (seedAt k s c xT σT).denote w env)
    (sP := (startPT k s c xT).denote w env) (sN := 0) (width := R kk) (t := t) (σ := σ)
    pos hseedB (by have := Nat.one_le_pow 2 N hpos; omega) hQP six hRP (by rw [hNE]; exact hqP) hcap halias hps hpv hQs hQv (hqs.add (stableAt_const _ _))
    (by rw [denote_add, hqpv, denote_const, hNE]) hNs (by rw [hNv, hNE]) hVs (by rw [hVv, ← hlenS])
    hks hkv hIBs hIBv hseedS rfl hsPs rfl (stableAt_const _ _) rfl hRs hRv hcps
    (by rw [hcpv, copiesOf, hinc]) pp hq hqv hbl hblv hσs hσv hLRs hLRv hx hxv
  exact this

end NtimeDspace.ProgTerm
