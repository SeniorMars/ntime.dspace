import NtimeDspace.TameArity
import NtimeDspace.TameCounterAt
import NtimeDspace.TameLocal
import NtimeDspace.TameNet
import NtimeDspace.TameWeight

/-!
# Bounds on the machine's tables

`tables_le`: the machine's transition tables, read as numbers, have entries at most `s + 3`
(from the code bounds `sgnCode_le` and `wCode_le`). The tier lemmas of `Cross/NetTerm.lean` use it.
-/

namespace NtimeDspace.ProgTerm

open Term Cslib.Complexity.CountingSimulation LocalSim Turing

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool} {L : ℕ}

theorem sgnCode_le (x : SignType) : sgnCode x ≤ 2 := by cases x <;> simp [sgnCode]

theorem wCode_le (x : Option (Option Bool)) : wCode x ≤ 3 := by
  cases x with
  | none => simp [wCode]
  | some c => have := cc_lt c; simp only [wCode]; omega

/-- The machine's tables have entries at most `s + 3`. -/
theorem tables_le (x : ℕ) : fSt e machine x ≤ s + 3 ∧ fIn e machine x ≤ s + 3 ∧
    fOut e machine x ≤ s + 3 ∧ fEmit x ≤ s + 3 ∧ fW e machine x ≤ s + 3 ∧ fM e machine x ≤ s + 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := stc_lt e (actOf e machine x).state; unfold fSt; omega
  · have := sgnCode_le (actOf e machine x).inputTape; unfold fIn; omega
  · have := cc_lt (actOf e machine x).output; unfold fOut; omega
  · have := trc_lt ((trOf (x % 3)).emit (cellOf (x / 3))); unfold fEmit; omega
  · unfold fW; split
    · have := wCode_le ((actOf e machine (x % keyCount k s)).workTapes ⟨x / keyCount k s, by omega⟩).1
      omega
    · omega
  · unfold fM; split
    · have := sgnCode_le ((actOf e machine (x % keyCount k s)).workTapes ⟨x / keyCount k s, by omega⟩).2
      omega
    · omega

end NtimeDspace.ProgTerm
