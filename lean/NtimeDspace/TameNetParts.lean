import NtimeDspace.TameNet
import NtimeDspace.TameLocal

/-!
# Tiers of the parts of a table entry

The table entry is split into the letter decoding, the interval entry and the
old-network entry, each bounded by a separate `tame1` run (one pass), to keep
the proof searches small.
-/

namespace NtimeDspace.ProgTerm

open Term LocalSim Turing

/-- One pass of `tame`. -/
macro "tame1" : tactic => `(tactic| ((repeat' tame_step) <;> try tame_num))

variable {w : List Bool} {L : ℕ} {env : List ℕ} {k s : ℕ} {State : Type} [DecidableEq State]
  {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

end NtimeDspace.ProgTerm
