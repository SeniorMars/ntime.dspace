import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.Space.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List

/-!
# Comparator challenge: NTIME(n) ⊊ DSPACE(n)

The statement only, written against Complexitylib's definitions and imports.
`lake comparator` checks that `NtimeDspace.Final` proves exactly this.
-/

namespace NtimeDspace

theorem ntime_ssubset_dspace :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => n) ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n) := sorry

end NtimeDspace
