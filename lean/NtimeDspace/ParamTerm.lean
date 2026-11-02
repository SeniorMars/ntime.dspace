import NtimeDspace.ArithHelpers
import NtimeDspace.NetworkCounter
import NtimeDspace.IntegerWindow
import NtimeDspace.SupportBudget

/-!
# The parameters as terms

From the input length `x` and the clock constant `c`: the clock
`t = c·x + c`, the block length and number, the number of edges `N` of the
block network, `log₂ N`, the selected `k = ParameterChoice.choose N`, and the
counter's parameters `s, Q, R, q`, the support budget and the window start.
Each term has a value lemma under stability of `x`.
-/

namespace NtimeDspace.ProgTerm

open Term Parameters Cslib.Complexity.CountingSimulation

variable {w : List Bool}

section Def

variable (k s c : ℕ) (xT : Term)

def clockT : Term := add (mul (const c) xT) (const c)
def blockLenT : Term := clogT (add (clockT c xT) (const 2))
def numBlocksT : Term := ceilDivT (clockT c xT) (blockLenT c xT)
def edgesNT : Term :=
  mul (const 2) (mul (mul (numBlocksT c xT) (const (3 * k + 1))) (mul (const (s + k + 4)) (blockLenT c xT)))
def lgNT : Term := log2T (edgesNT k s c xT) (edgesNT k s c xT)
def kpT : Term := chooseT (lgNT k s c xT)
def spT : Term := pow2 (kpT k s c xT)
def QpT : Term := mul (mul (spT k s c xT) (spT k s c xT)) (kpT k s c xT)
def RpT : Term := mul (mul (const 8) (spT k s c xT)) (kpT k s c xT)
def qpT : Term := div (mul (mul (const 3) (edgesNT k s c xT)) (RpT k s c xT)) (QpT k s c xT)
def limitT : Term :=
  div (sub (add (mul (mul (const 24) (edgesNT k s c xT)) (add (mul (const 2) (kpT k s c xT)) (const 1)))
    (spT k s c xT)) (const 1)) (spT k s c xT)
def startPT : Term :=
  div (add (mul (mul (spT k s c xT) (kpT k s c xT)) (sub (spT k s c xT) (const 9))) (const 1)) (const 2)
def radixPT : Term :=
  add (add (add (edgesNT k s c xT) (qpT k s c xT)) (lgNT k s c xT)) (const 3)

end Def

section Values

variable {k s c : ℕ} {xT : Term} {env : List ℕ} {x : ℕ} (hx : StableAt w xT env)
  (hxv : xT.denote w env = x)
include hx hxv

/-- The clock. -/
abbrev clk (c x : ℕ) : ℕ := c * x + c

/-- The number of edges of the block network at clock `t`. -/
abbrev edgesN (k s t : ℕ) : ℕ := 2 * (numBlocks t * (3 * k + 1) * Turing.MultiTapePTM.letterBits k s (blockLength t))

theorem denote_clockT : (clockT c xT).denote w env = clk c x := by simp [clockT, hxv]
theorem StableAt.clockT : StableAt w (clockT c xT) env :=
  (((stableAt_const _ _).mul hx).add (stableAt_const _ _))

theorem denote_blockLenT : (blockLenT c xT).denote w env = blockLength (clk c x) := by
  rw [blockLenT, denote_clogT ((StableAt.clockT hx hxv).add (stableAt_const _ _))
    (by simp), denote_add, denote_clockT hx hxv, denote_const]
  rfl
theorem StableAt.blockLenT : StableAt w (blockLenT c xT) env :=
  StableAt.clogT ((StableAt.clockT hx hxv).add (stableAt_const _ _)) (by simp)

theorem denote_numBlocksT : (numBlocksT c xT).denote w env = numBlocks (clk c x) := by
  rw [numBlocksT, denote_ceilDivT, denote_clockT hx hxv, denote_blockLenT hx hxv, numBlocks,
    Nat.ceilDiv_eq_add_pred_div]
theorem StableAt.numBlocksT : StableAt w (numBlocksT c xT) env := fun extra => by
  rw [denote_numBlocksT (hx.extend extra) (by rw [hx extra, hxv]), denote_numBlocksT hx hxv]

theorem denote_edgesNT : (edgesNT k s c xT).denote w env = edgesN k s (clk c x) := by
  simp only [edgesNT, denote_mul, denote_const, denote_numBlocksT hx hxv, denote_blockLenT hx hxv,
    edgesN, Turing.MultiTapePTM.letterBits]
  try ring
theorem StableAt.edgesNT : StableAt w (edgesNT k s c xT) env := fun extra => by
  rw [denote_edgesNT (hx.extend extra) (by rw [hx extra, hxv]), denote_edgesNT hx hxv]

theorem denote_lgNT : (lgNT k s c xT).denote w env = (edgesN k s (clk c x)).log2 := by
  have hN := StableAt.edgesNT (k := k) (s := s) (c := c) hx hxv
  have hNv := denote_edgesNT (k := k) (s := s) (c := c) hx hxv
  rcases Nat.eq_zero_or_pos (edgesN k s (clk c x)) with h0 | hpos
  · rw [h0, lgNT, log2T, denote_sumT _ _ env (fun _ => 0) (fun acc i => by
      simp only [denote_lt, denote_const, divPowT_denote _ _ _ _ (stableAt_const _ _), hN.cons₂,
        hNv, h0, Nat.zero_div, lt_irrefl, if_false])]
    simp
  · rw [lgNT, log2T_denote _ _ env hN (by rw [hNv]; exact hpos) (by
      rw [hNv]; exact Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))),
      hNv]
theorem StableAt.lgNT : StableAt w (lgNT k s c xT) env := fun extra => by
  rw [denote_lgNT (hx.extend extra) (by rw [hx extra, hxv]), denote_lgNT hx hxv]

theorem denote_kpT :
    (kpT k s c xT).denote w env = ParameterChoice.choose (edgesN k s (clk c x)) :=
  denote_chooseT (StableAt.lgNT hx hxv) _ (denote_lgNT hx hxv)
theorem StableAt.kpT : StableAt w (kpT k s c xT) env :=
  StableAt.chooseT (StableAt.lgNT hx hxv) _ (denote_lgNT hx hxv)

/-- The selected `k`. -/
abbrev kp (k s c x : ℕ) : ℕ := ParameterChoice.choose (edgesN k s (clk c x))

theorem denote_spT : (spT k s c xT).denote w env = Parameters.s (kp k s c x) := by
  simp [spT, denote_kpT hx hxv, Parameters.s]
theorem StableAt.spT : StableAt w (spT k s c xT) env := (StableAt.kpT hx hxv).pow2

theorem denote_QpT : (QpT k s c xT).denote w env = Parameters.Q (kp k s c x) := by
  simp [QpT, denote_spT hx hxv, denote_kpT hx hxv, Parameters.Q, pow_two]
theorem denote_RpT : (RpT k s c xT).denote w env = Parameters.R (kp k s c x) := by
  simp [RpT, denote_spT hx hxv, denote_kpT hx hxv, Parameters.R]
theorem denote_qpT :
    (qpT k s c xT).denote w env = Parameters.q (edgesN k s (clk c x)) (kp k s c x) := by
  simp [qpT, denote_edgesNT hx hxv, denote_RpT hx hxv, denote_QpT hx hxv, Parameters.q]
theorem denote_limitT :
    (limitT k s c xT).denote w env = SupportBudget.limit (edgesN k s (clk c x)) (kp k s c x) := by
  simp [limitT, denote_edgesNT hx hxv, denote_kpT hx hxv, denote_spT hx hxv, SupportBudget.limit]
theorem denote_radixPT :
    (radixPT k s c xT).denote w env = ParserFold.radix (edgesN k s (clk c x))
      (Parameters.q (edgesN k s (clk c x)) (kp k s c x)) := by
  simp [radixPT, denote_edgesNT hx hxv, denote_qpT hx hxv, denote_lgNT hx hxv, ParserFold.radix]

/-- With `s ≥ 9`, the window start is the natural number `startPT`. -/
theorem startPT_eq (hs9 : 9 ≤ Parameters.s (kp k s c x)) :
    ((startPT k s c xT).denote w env : ℤ) = IntegerWindow.start (kp k s c x) := by
  simp only [startPT, denote_div, denote_add, denote_mul, denote_sub, denote_const,
    denote_spT hx hxv, denote_kpT hx hxv, IntegerWindow.start]
  push_cast [Nat.cast_sub hs9]
  rfl

end Values

end NtimeDspace.ProgTerm
