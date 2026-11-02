import NtimeDspace.CounterAssemblyEq
import NtimeDspace.NetSystemSpec

/-!
# The counter for a block-counting network

The network's constraint system is accessed by `arityNT`, `portAtT` and
`weightNT`. This file proves their contracts against
`NetworkSystem.toSystem (blockNetworkOf …)`, and `networkCounterT_eq`: the
system counter term over these accessors computes the network's contraction
modulo `p`.
-/

namespace NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Complexity.CountingSimulation Turing Turing.MultiTapePTM
  NetworkSystem WeightedSystem

variable {w : List Bool} {k s : ℕ} {State : Type} [DecidableEq State]
  {machine : MultiTapePTM k Bool State} {e : State ≃ Fin s}

section Contracts

variable {qT bT σT : Term} {env : List ℕ} {t σ : ℕ}
  (hq : StableAt w qT env) (hqv : qT.denote w env = numBlocks t)
  (hb : StableAt w bT env) (hbv : bT.denote w env = blockLength t)
  (hσ : StableAt w σT env) (hσv : σT.denote w env = σ)
include hq hqv hb hbv hσ hσv

theorem implN_arityNT : ImplN w env (arityNT k s qT bT σT) (fun v => (netPorts k s t σ v).length) := by
  have key : ∀ (pre : List ℕ) (a : Term), StableAt w a (pre ++ env) →
      (arityNT k s qT bT σT a).denote w (pre ++ env) = (netPorts k s t σ (a.denote w (pre ++ env))).length := by
    intro pre a ha
    rw [denote_arityNT (hq.extend pre) (hb.extend pre) (hσ.extend pre) ha, hq pre, hqv, hb pre, hbv,
      hσ pre, hσv]
    rfl
  intro pre a ha
  refine ⟨key pre a ha, fun extra => ?_⟩
  rw [← List.append_assoc, key _ a (by rw [List.append_assoc]; exact ha.extend extra),
    List.append_assoc, ha extra, key pre a ha]

theorem implN2_portAtT :
    ImplN2 w env (portAtT k s qT bT σT) (fun v i => (netPorts k s t σ v).getD i 0) := by
  have key : ∀ (pre : List ℕ) (a b : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
      (portAtT k s qT bT σT a b).denote w (pre ++ env) =
        (netPorts k s t σ (a.denote w (pre ++ env))).getD (b.denote w (pre ++ env)) 0 := by
    intro pre a b ha hb'
    rw [denote_portAtT (hq.extend pre) (hb.extend pre) (hσ.extend pre) ha b hb', hq pre, hqv,
      hb pre, hbv, hσ pre, hσv]
    rfl
  intro pre a b ha hb'
  refine ⟨key pre a b ha hb', fun extra => ?_⟩
  rw [← List.append_assoc, key _ a b (by rw [List.append_assoc]; exact ha.extend extra)
    (by rw [List.append_assoc]; exact hb'.extend extra), List.append_assoc, ha extra, hb' extra,
    key pre a b ha hb']

theorem implZ2_weightNT {P : ℕ} {RT NT : Term} (hR : StableAt w RT env)
    (hRv : RT.denote w env = radix (blockLength t) w.length s) (hN : StableAt w NT env)
    (hNv : NT.denote w env = w.length) :
    ImplZ2 w env P (weightNT k s e machine RT NT qT bT σT) (fun v A =>
      (tableEntryNum e (blockLength t) machine w (numBlocks t) σ v (netPorts k s t σ v)
        (A % 2 ^ (netPorts k s t σ v).length) : ZMod P)) := by
  intro pre a b ha hb'
  rw [denote_weightNT (hR.extend pre) (hN.extend pre) (hq.extend pre) (hb.extend pre)
    (hσ.extend pre) ha hb' (by rw [hb pre, hbv]; exact one_le_blockLength t)
    (by rw [hR pre, hRv, hb pre, hbv]) (by rw [hN pre, hNv]), hq pre, hqv, hb pre, hbv, hσ pre, hσv]
  rfl

end Contracts

/-- Every port of every vertex names an edge. -/
theorem ports_valid (x : List Bool) (t σ : ℕ) :
    ∀ v ∈ (blockNetworkOf machine e (x, t, σ)).2.vertices, ∀ i ∈ v.1,
      i < (blockNetworkOf machine e (x, t, σ)).2.numEdges := by
  intro v hv i hi
  rw [blockNetworkOf_eq] at hv ⊢
  simp only [explicitNetworkNum, explicitVerticesNum, List.mem_map, List.mem_range] at hv
  obtain ⟨j, _, rfl⟩ := hv
  exact lt_numEdges_of_mem_netPorts (k := k) (s := s) (t := t) (σ := σ) (v := j) hi

set_option maxHeartbeats 2000000 in
/-- **The network counter computes the contraction modulo `p`.** -/
theorem networkCounterT_eq {P Q bits kk sd sP sN width t σ : ℕ} [Fact P.Prime]
    (pos : 0 < (blockNetworkOf machine e (w, t, σ)).2.numEdges)
    (hbal : Placement.balN (toSystem (blockNetworkOf machine e (w, t, σ)).2 pos) Q bits sd)
    (hP3 : 2 < P) (hQP : Q < P) (large : 6 ≤ kk) (small : width < P)
    (below : Parameters.q (blockNetworkOf machine e (w, t, σ)).2.numEdges kk + 1 < P)
    (capacity : incidenceCount (toSystem (blockNetworkOf machine e (w, t, σ)).2 pos) * (width - 1) <
      Q * (Parameters.q (blockNetworkOf machine e (w, t, σ)).2.numEdges kk + 1))
    (no_alias : incidenceCount (toSystem (blockNetworkOf machine e (w, t, σ)).2 pos) * (width - 1) +
      Q * Parameters.q (blockNetworkOf machine e (w, t, σ)).2.numEdges kk ≤ P - 2)
    {pT QT orderT B Cap Lb M K nT mT bitsT IBT sT sPT sNT widthT copiesT qT bT σT RT NT : Term}
    {env : List ℕ}
    (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q)
    (ho : StableAt w orderT env)
    (hov : orderT.denote w env = Parameters.q (blockNetworkOf machine e (w, t, σ)).2.numEdges kk + 1)
    (hn : StableAt w nT env) (hnv : nT.denote w env = (blockNetworkOf machine e (w, t, σ)).2.numEdges)
    (hm : StableAt w mT env)
    (hmv : mT.denote w env = (toSystem (blockNetworkOf machine e (w, t, σ)).2 pos).constraints.length)
    (hb' : StableAt w bitsT env) (hbv' : bitsT.denote w env = bits)
    (hIB : StableAt w IBT env)
    (hIBv : IBT.denote w env =
      WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (w, t, σ)).2 pos))
    (hs : StableAt w sT env) (hsv : sT.denote w env = sd)
    (hsP : StableAt w sPT env) (hsPv : sPT.denote w env = sP)
    (hsN : StableAt w sNT env) (hsNv : sNT.denote w env = sN)
    (hwd : StableAt w widthT env) (hwdv : widthT.denote w env = width)
    (hcp : StableAt w copiesT env)
    (hcpv : copiesT.denote w env = copiesOf (toSystem (blockNetworkOf machine e (w, t, σ)).2 pos) Q bits)
    (pp : ParserParams w env (blockNetworkOf machine e (w, t, σ)).2.numEdges
      (Parameters.q (blockNetworkOf machine e (w, t, σ)).2.numEdges kk)
      (SupportBudget.limit (blockNetworkOf machine e (w, t, σ)).2.numEdges kk) B Cap Lb M K)
    (hq : StableAt w qT env) (hqv : qT.denote w env = numBlocks t)
    (hbl : StableAt w bT env) (hblv : bT.denote w env = blockLength t)
    (hσ : StableAt w σT env) (hσv : σT.denote w env = σ)
    (hR : StableAt w RT env) (hRv : RT.denote w env = radix (blockLength t) w.length s)
    (hN : StableAt w NT env) (hNv : NT.denote w env = w.length) :
    ((systemCounterT pT QT orderT B Cap Lb M K nT mT bitsT IBT sT sPT sNT widthT copiesT
        (arityNT k s qT bT σT) (portAtT k s qT bT σT) (weightNT k s e machine RT NT qT bT σT)).denote
        w env : ZMod P) = ((blockNetworkOf machine e (w, t, σ)).2.contraction : ZMod P) := by
  rw [← count_toSystem _ pos (ports_valid w t σ)]
  refine systemCounterT_eq (toSystem (blockNetworkOf machine e (w, t, σ)).2 pos) pos hbal hP3 hQP
    large small below capacity no_alias hp hpv hQ hQv ho hov hn hnv hm hmv hb' hbv' hIB hIBv hs hsv
    hsP hsPv hsN hsNv hwd hwdv hcp hcpv pp (implN_arityNT hq hqv hbl hblv hσ hσv) ?_
    (implN2_portAtT hq hqv hbl hblv hσ hσv) ?_ (implZ2_weightNT hq hqv hbl hblv hσ hσv hR hRv hN hNv) ?_
  · intro v hv
    exact (scope_length_toSystem machine e w t σ pos v hv).symm
  · intro inc
    exact (scope_get_toSystem machine e w t σ pos inc.1 inc.1.isLt inc.2 inc.2.isLt).symm
  · intro v hv A
    rw [weight_toSystem machine e w t σ pos v hv A]

end NtimeDspace.LocalSim
