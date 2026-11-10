import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.Space.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List

/-!
# Comparator challenge: Theorem 1.1 at linear time

The statements only, written against Complexitylib's definitions and imports, with
`n / ⌊√⌊log₂ n⌋⌋ + 1` written out. `lake comparator` checks that `NtimeDspace.Cross.Theorem`
proves exactly these.

* `ntime_decidable_sqrtLog`: every language in `NTIME[n]` is decided in simultaneous deterministic
  time `2^(C·(n/√log n + 1))` and space `C·(n/√log n + 1)` (Theorem 1.1 for `t(n) = n`).
* `ntime_subset_dspace_sqrtLog`: `NTIME[n] ⊆ DSPACE[n/√log n]`.
* `ntime_ssubset_dspace`: `NTIME[n] ⊊ DSPACE[n]` (Corollary 1.2 (i) at `t(n) = n`).
-/

namespace NtimeDspace.Crossing

theorem ntime_decidable_sqrtLog {A : Set (List Bool)}
    (hA : A ∈ Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => n)) :
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace A Turing.MultiTapeTM.encBits
      (fun a => 2 ^ (C * (a.length / Nat.sqrt a.length.log2 + 1)))
      (fun a => C * (a.length / Nat.sqrt a.length.log2 + 1)) := sorry

theorem ntime_subset_dspace_sqrtLog :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => n) ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n / Nat.sqrt n.log2 + 1) := sorry

theorem ntime_ssubset_dspace :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => n) ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n) := sorry

end NtimeDspace.Crossing
