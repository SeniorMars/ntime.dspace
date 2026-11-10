import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.PP.Time
import Complexity.Computability.Complexity.Classes.Space.Basic
import Complexity.Computability.Complexity.Classes.Space.Nondeterministic
import Complexity.Computability.Complexity.Classes.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List

/-!
# Comparator challenge: Theorem 1.1, Corollary 1.2 and Theorem 7.1 (PP, BP) for every `t(n) ≥ n`

The statements only, written against Complexitylib's definitions and imports, with
`m / ⌊√⌊log₂ m⌋⌋ + 1` written out. `lake comparator` checks that `NtimeDspace.Cross.CountingFinal`
proves exactly these.
-/

namespace NtimeDspace.Crossing

/-- **Theorem 1.1.** For every `t(n) ≥ n` (not necessarily constructible), every language in
`NTIME[t]` is decided in simultaneous deterministic time `2^(C·(t/⌊√⌊log₂ t⌋⌋ + 1))` and space
`C·(t/⌊√⌊log₂ t⌋⌋ + 1)`. -/
theorem ntime_decidable_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) {A : Set (List Bool)}
    (hA : A ∈ Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits t) :
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace A Turing.MultiTapeTM.encBits
      (fun a => 2 ^ (C * (t a.length / Nat.sqrt (t a.length).log2 + 1)))
      (fun a => C * (t a.length / Nat.sqrt (t a.length).log2 + 1)) := sorry

/-- **Theorem 1.1, as a class inclusion:** `NTIME[t] ⊆ DSPACE[t/√log t]` for every `t(n) ≥ n`. -/
theorem ntime_subset_dspace_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits t ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) := sorry

/-- **Corollary 1.2 (i):** `NTIME[t] ⊊ DSPACE[t]` for every space-constructible `t(n) ≥ n`. -/
theorem ntime_ssubset_dspace_general (t : ℕ → ℕ) (hsc : Cslib.Complexity.SpaceConstructible t)
    (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits t ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits t := sorry

/-- **Corollary 1.2 (i):** `NTIME[t] ⊊ NSPACE[t]`, so `NTIME[t] ≠ NSPACE[t]`, for every
space-constructible `t(n) ≥ n`. -/
theorem ntime_ssubset_nspace_general (t : ℕ → ℕ) (hsc : Cslib.Complexity.SpaceConstructible t)
    (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits t ⊂
      Cslib.Complexity.NSPACE Turing.MultiTapeTM.encBits t := sorry

/-- **Corollary 1.2 (ii):** `NTIME[t·√log t] ⊆ DSPACE[t]` for every `t(n) ≥ n`. -/
theorem ntime_mul_sqrtLog_subset_dspace_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => t n * Nat.sqrt (Nat.log2 (t n))) ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits t := sorry

/-- **Corollary 1.2 (iii):** a language in `DSPACE[n]` such that every nondeterministic machine
deciding it or its complement takes at least `n·⌊√⌊log₂ n⌋⌋ / C` steps on some input of every
large length `n`, for some `C ≥ 1`. -/
theorem exists_dspace_linear_ntime_lower_bound_general :
    ∃ L : Set (List Bool), L ∈ Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n) ∧
      ∀ (k : ℕ) (State : Type) [Finite State] (ntm : Turing.MultiTapeNTM k Bool State)
        (B : Set (List Bool)), (B = L ∨ B = Lᶜ) →
        (∀ x, (∃ t, ntm.RunsInTime x t) ∧ (x ∈ B ↔ ntm.Accepts x)) →
        ∃ C, 1 ≤ C ∧ ∀ᶠ n in Filter.atTop,
          ∃ x : List Bool, x.length = n ∧ ¬ ntm.RunsInTime x (n * Nat.sqrt n.log2 / C) := sorry

/-- **Theorem 7.1 for `PPTIME`:** `PPTIME[t] ⊆ DSPACE[t/√log t]` for every `t(n) ≥ n`. -/
theorem pptime_subset_dspace_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.PPTIME Turing.MultiTapeTM.encBits t ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) := sorry

/-- **Theorem 7.1 for `BPTIME`:** `BPTIME[t] ⊆ DSPACE[t/√log t]` for every `t(n) ≥ n`. -/
theorem bptime_subset_dspace_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.BPTIME Turing.MultiTapeTM.encBits t ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) := sorry

end NtimeDspace.Crossing
