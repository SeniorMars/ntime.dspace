import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.Space.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List

/-! Negative control: a different statement under the same name; Comparator must reject. -/

namespace NtimeDspace

theorem ntime_ssubset_dspace :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => n) ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n + 1) := sorry

end NtimeDspace
