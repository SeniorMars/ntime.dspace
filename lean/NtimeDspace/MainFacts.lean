import NtimeDspace.TameMain

/-!
# The numeric facts of the main loop's tier

`MainFacts k s c n L D0` bundles the numeric hypotheses of `tm_mainT` at input
length `n` and scale `L`. They only bound quantities by `L` or `2^L`, so they
persist when `L` grows (`MainFacts.mono`).
-/

namespace NtimeDspace.ProgTerm

open Term Budget Parameters Cslib.Complexity.CountingSimulation LocalSim Placement WeightedSystem
  NetworkSystem Turing

/-- The numeric hypotheses of `tm_mainT`. -/
structure MainFacts (k s c n L D0 : ℕ) : Prop where
  hL : 8 ≤ L
  hn : n < 2 ^ L
  hcube : NN k s c n ^ 3 < 2 ^ L
  hcube1 : NN k s c n ^ 3 + 1 < 2 ^ L
  hconst : 4 * k + s + c + 100 < 2 ^ L
  hlarge : ParameterChoice.cost 6 ≤ lgN k s c n
  hN72 : 72 ≤ NN k s c n
  hD : (2 ^ kN k s c n * 2 ^ kN k s c n) ^ Q (kN k s c n) < 2 ^ L
  hDr : (2 ^ kN k s c n) ^ (2 * Q (kN k s c n)) < 2 ^ L
  hlim : SupportBudget.limit (NN k s c n) (kN k s c n) + 1 < L
  hblk : 2 ^ (2 * blk (Q (kN k s c n)) (kN k s c n)
    ((max (NN k s c n) (verticesN k s (tN c n))).log2 + 1)) < 2 ^ L
  hgroup : 2 * NN k s c n / 2 ^ kN k s c n < L
  hqL : q (NN k s c n) (kN k s c n) < L
  htup : (2 * (2 ^ kN k s c n) ^ (2 * Q (kN k s c n)) + 1) ^ tupleWidth k s c n < 2 ^ L
  hkey : keyCount k s * k + keyCount k s + width k + 3 ^ k < 2 ^ L
  hRw : LocalSim.radix (blockLength (clk c n)) n s ^ width k < 2 ^ L
  h3b : 3 ^ (3 * blockLength (clk c n)) < 2 ^ L
  hccv : (s + 1) * (blockLength (clk c n) ^ (k + 1) * 3) < 2 ^ L
  hm0 : MultiTapePTM.letterBits k s (blockLength (clk c n)) < L
  hsched : 3 ^ ((k + 1) * numBlocks (clk c n)) < 2 ^ L
  hD0 : D0 < L

theorem MainFacts.mono {k s c n L L' D0 : ℕ} (h : MainFacts k s c n L D0) (hle : L ≤ L') :
    MainFacts k s c n L' D0 := by
  have hp : 2 ^ L ≤ 2 ^ L' := Nat.pow_le_pow_right (by norm_num) hle
  exact ⟨by have := h.hL; omega, by have := h.hn; omega, by have := h.hcube; omega,
    by have := h.hcube1; omega, by have := h.hconst; omega, h.hlarge, h.hN72,
    by have := h.hD; omega, by have := h.hDr; omega,
    by have := h.hlim; omega, by have := h.hblk; omega, by have := h.hgroup; omega,
    by have := h.hqL; omega, by have := h.htup; omega, by have := h.hkey; omega,
    by have := h.hRw; omega, by have := h.h3b; omega, by have := h.hccv; omega,
    by have := h.hm0; omega, by have := h.hsched; omega, by have := h.hD0; omega⟩

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool} {L : ℕ}

/-- The main loop's tier from the bundled facts. -/
theorem tm_mainT_of_facts {D0 : ℕ} (hc : 2 ≤ c) (h : MainFacts k s c w.length L D0)
    (hdeg : ∀ σ, ∀ v < verticesN k s (tN c w.length),
      (MultiTapePTM.explicitPortsNum k (numBlocks (clk c w.length))
        (MultiTapePTM.letterBits k s (blockLength (clk c w.length))) σ v).length ≤ D0)
    (hex : ∀ σ, ∀ pos : 0 < (blockNetworkOf machine e (w, clk c w.length, σ)).2.numEdges,
      ∃ sd < 2 ^ (2 * blk (Q (kp k s c w.length)) (kp k s c w.length)
        (WSchedulePlacement.inputBits (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos))),
        balN (toSystem (blockNetworkOf machine e (w, clk c w.length, σ)).2 pos)
          (Q (kp k s c w.length)) (kp k s c w.length) sd) :
    Tm w L 3 (mainT k s c e machine (lvl 0)) [w.length] :=
  tm_mainT h.hL h.hn h.hcube h.hcube1 h.hconst hc h.hlarge h.hN72 h.hD h.hDr h.hlim h.hblk
    h.hgroup h.hqL h.htup h.hkey h.hRw h.h3b h.hccv h.hm0 h.hsched h.hD0 hdeg hex

end NtimeDspace.ProgTerm
