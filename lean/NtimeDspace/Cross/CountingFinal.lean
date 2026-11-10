-- `GeneralFinal` is imported so that this module, the solution module of `comparator-general.json`,
-- exposes every theorem that config checks, including the NTIME statements proved there.
import NtimeDspace.Cross.GeneralFinal
import NtimeDspace.Cross.CountingClasses
import NtimeDspace.Cross.CubeFinal
import Complexity.Computability.Complexity.Classes.Space.Nondeterministic

/-!
# Theorem 7.1, unconditionally

The clocked bits of the accept count (`cubeClockedBits`: Theorem 2.3 for the block networks and the
column adder over schedules) give Theorem 7.1 for every `t(n) ≥ n`:
`PPTIME[t]`, `BPTIME[t]`, `⊕TIME[t]`, `Mod_qTIME[t]` and `C=TIME[t]` are in `DSPACE[t/√log t]`.
`PPTIME` and `BPTIME` are Complexitylib's; `ParityTIME`, `ModTIME` and `CeqTIME` are defined in
CountingClasses.lean.
-/

namespace NtimeDspace.Crossing

open NtimeDspace.Cross

/-- The bits of the clocked accept count, by the route of §§3–6. -/
theorem cubeClockedBits : Exact.ClockedBits := Exact.clockedBits_of_blockBits cubeBlockBits

/-- **Theorem 7.1 for `PPTIME`:** `PPTIME[t] ⊆ DSPACE[t/√log t]` for every `t(n) ≥ n`. -/
theorem pptime_subset_dspace_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.PPTIME Turing.MultiTapeTM.encBits t ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  pptime_subset_dspace cubeClockedBits ht

/-- **Theorem 7.1 for `BPTIME`:** `BPTIME[t] ⊆ DSPACE[t/√log t]` for every `t(n) ≥ n`. -/
theorem bptime_subset_dspace_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.BPTIME Turing.MultiTapeTM.encBits t ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  bptime_subset_dspace cubeClockedBits ht

/-- **Theorem 7.1 for `⊕TIME`.** -/
theorem parityTIME_subset_dspace_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    ParityTIME Turing.MultiTapeTM.encBits t ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  fun _ hA => (parityTIME_decided cubeClockedBits ht hA).mem_DSPACE

/-- **Theorem 7.1 for `Mod_qTIME`** (`q ≥ 1`). -/
theorem modTIME_subset_dspace_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) {q : ℕ}
    (hq : 1 ≤ q) :
    ModTIME q Turing.MultiTapeTM.encBits t ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  fun _ hA => (modTIME_decided cubeClockedBits ht hq hA).mem_DSPACE

/-- **Theorem 7.1 for `C=TIME`.** -/
theorem ceqTIME_subset_dspace_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    CeqTIME Turing.MultiTapeTM.encBits t ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  fun _ hA => (ceqTIME_decided cubeClockedBits ht hA).mem_DSPACE

end NtimeDspace.Crossing
