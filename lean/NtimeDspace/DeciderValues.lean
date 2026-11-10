import NtimeDspace.LocalCount
import NtimeDspace.ParamTerm

/-!
# Values of the decider's terms

The number of vertices, the identifier width, the local radix and the number
of copies, as functions of the input length.
-/

namespace NtimeDspace.ProgTerm

open Term LocalSim Turing Cslib.Complexity.CountingSimulation

variable {w : List Bool} {k s c : ℕ} {xT : Term} {env : List ℕ} {x : ℕ}
  (hx : StableAt w xT env) (hxv : xT.denote w env = x)
include hx hxv

/-- The number of vertices of the block network at clock `t`. -/
abbrev verticesN (k s t : ℕ) : ℕ :=
  numBlocks t * (3 * k + 2) + numBlocks t * (3 * k + 1) * MultiTapePTM.letterBits k s (blockLength t)

end NtimeDspace.ProgTerm
