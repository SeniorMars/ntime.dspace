import NtimeDspace.SpectralIndexing
import NtimeDspace.IntegerWindow

/-!
# The scanned bad count is the tail parameter's bad count

With the window start `IntegerWindow.start k` and width `R k`, the counter's
scanned bad count equals `TailParameters.badCount k`, which is at most
`D / (3 s⁵)` (`TailParameters.badCount_scaled`).
-/

namespace NtimeDspace

open Parameters

theorem badCount_bridge (k : ℕ) :
    SpectralIndexing.badCount (s k) (Q k) (s_pos k) (IntegerWindow.start k) (R k) =
      TailParameters.badCount k := by
  rw [SpectralIndexing.badCount_correct, TailParameters.badCount, TailParameters.badIndices,
    IntegerWindow.start_eq_centered]
  rfl

end NtimeDspace
