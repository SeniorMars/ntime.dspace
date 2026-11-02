import NtimeDspace.DeciderTerm

/-!
# Values of the decider's terms

The number of vertices, the identifier width, the local radix and the number
of copies, as functions of the input length.
-/

namespace NtimeDspace.ProgTerm

open Term LocalSim Turing Parameters Cslib.Complexity.CountingSimulation

variable {w : List Bool} {k s c : ℕ} {xT : Term} {env : List ℕ} {x : ℕ}
  (hx : StableAt w xT env) (hxv : xT.denote w env = x)
include hx hxv

/-- The number of vertices of the block network at clock `t`. -/
abbrev verticesN (k s t : ℕ) : ℕ :=
  numBlocks t * (3 * k + 2) + numBlocks t * (3 * k + 1) * MultiTapePTM.letterBits k s (blockLength t)

theorem denote_verticesT : (verticesT k s c xT).denote w env = verticesN k s (clk c x) := by
  simp only [verticesT, denote_add, denote_mul, denote_const, denote_numBlocksT hx hxv,
    denote_blockLenT hx hxv, verticesN, MultiTapePTM.letterBits]
theorem StableAt.verticesT : StableAt w (verticesT k s c xT) env := fun extra => by
  rw [denote_verticesT (hx.extend extra) (by rw [hx extra, hxv]), denote_verticesT hx hxv]

theorem denote_inputBitsT (hpos : 0 < edgesN k s (clk c x)) :
    (inputBitsT k s c xT).denote w env =
      (max (edgesN k s (clk c x)) (verticesN k s (clk c x))).log2 + 1 := by
  have hN := StableAt.edgesNT (k := k) (s := s) (c := c) hx hxv
  have hNv := denote_edgesNT (k := k) (s := s) (c := c) hx hxv
  have hV := StableAt.verticesT (k := k) (s := s) (c := c) hx hxv
  have hVv := denote_verticesT (k := k) (s := s) (c := c) hx hxv
  have hmx : StableAt w (maxT (edgesNT k s c xT) (verticesT k s c xT)) env := fun extra => by
    rw [denote_maxT, denote_maxT, hN extra, hV extra]
  have hmv : (maxT (edgesNT k s c xT) (verticesT k s c xT)).denote w env =
      max (edgesN k s (clk c x)) (verticesN k s (clk c x)) := by rw [denote_maxT, hNv, hVv]
  rw [inputBitsT, denote_add, denote_const, log2T_denote _ _ env hmx (by rw [hmv]; omega)
    (by rw [hmv]; exact Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))),
    hmv]

theorem denote_localRadixT : (localRadixT s c xT).denote w env = radix (blockLength (clk c x)) x s := by
  simp only [localRadixT, denote_add, denote_const, powT_denote _ _ _ (stableAt_const _ _),
    denote_mul, denote_blockLenT hx hxv, hxv, radix]
theorem StableAt.localRadixT : StableAt w (localRadixT s c xT) env := fun extra => by
  rw [denote_localRadixT (hx.extend extra) (by rw [hx extra, hxv]), denote_localRadixT hx hxv]

theorem denote_copiesT : (copiesT k s c xT).denote w env =
    2 * (2 * edgesN k s (clk c x)) / (2 ^ kp k s c x * 2 ^ kp k s c x) ^ Q (kp k s c x) := by
  have hk := StableAt.kpT (k := k) (s := s) (c := c) hx hxv
  simp only [copiesT, denote_div, denote_mul, denote_const, denote_edgesNT hx hxv,
    powT_denote _ _ _ (hk.pow2.mul hk.pow2), denote_pow2, denote_kpT hx hxv, denote_QpT hx hxv]
theorem StableAt.copiesT : StableAt w (copiesT k s c xT) env := fun extra => by
  rw [denote_copiesT (hx.extend extra) (by rw [hx extra, hxv]), denote_copiesT hx hxv]

end NtimeDspace.ProgTerm
