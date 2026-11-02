import NtimeDspace.ClearRegisterMachine
import NtimeDspace.CopyRegisterMachine
import NtimeDspace.TapeEmbedding
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
Replace one register by another and release the source register. The source
serves as the width marker while clearing the old destination; after copying,
the new destination serves as the marker while clearing the source. No scratch
word or unbounded control state is introduced.
-/

namespace NtimeDspace.ReplaceRegisterMachine

open Turing Turing.MultiTapeTM

def swap : Fin 2 ↪ Fin 2 :=
  ⟨![1, 0], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

noncomputable def clearSource := ClearRegisterMachine.machine.extendTapes swap

noncomputable def machine :=
  (ClearRegisterMachine.machine.seq CopyRegisterMachine.machine).seq clearSource

/-- Clear the old destination, copy the source, then clear the source. The
length condition makes both erasures bounded by a preserved register. -/
theorem transforms_replace (L : ℕ) :
    TransformsTapes machine
      (fun _ ws => (ws 0).length ≤ L ∧ (ws 1).length ≤ (ws 0).length)
      (fun _ ws ws' emitted => ws' 0 = [] ∧ ws' 1 = ws 0 ∧ emitted = [])
      (6 * L + 6) (6 * (L + 2)) := by
  have copied := transformsTapes_seq (ClearRegisterMachine.transforms_clear L)
    (CopyRegisterMachine.transforms_copy L) (by
      intro _ ws ws' _ pre post
      exact ⟨by rw [post.1]; exact pre.1, post.2.1⟩)
  have copied_spec : TransformsTapes
      (ClearRegisterMachine.machine.seq CopyRegisterMachine.machine)
      (fun _ ws => (ws 0).length ≤ L ∧ (ws 1).length ≤ (ws 0).length)
      (fun _ ws ws' emitted => ws' 0 = ws 0 ∧ ws' 1 = ws 0 ∧ emitted = [])
      (4 * L + 4) (4 * (L + 2)) := by
    apply copied.imp
    · exact fun _ _ h => h
    · rintro _ ws ws' e _ ⟨middle, e₀, e₁, first, second, rfl⟩
      exact ⟨second.1.trans first.1, second.2.1.trans first.1,
        by simp [first.2.2, second.2.2]⟩
    · omega
    · omega
  have clear_spec : TransformsTapes clearSource
      (fun _ ws => (ws 1).length ≤ L ∧ (ws 0).length ≤ (ws 1).length)
      (fun _ ws ws' emitted => ws' 1 = ws 1 ∧ ws' 0 = [] ∧ emitted = [])
      (2 * L + 2) (2 * (L + 2)) := by
    apply (TapeEmbedding.transforms_extendTapes (ClearRegisterMachine.transforms_clear L) swap).imp
    · intro _ ws pre
      exact pre
    · intro _ ws ws' emitted _ post
      exact post.1
    · exact le_rfl
    · simp
  have composed := transformsTapes_seq copied_spec clear_spec (by
    intro _ ws ws' _ pre post
    exact ⟨by rw [post.2.1]; exact pre.1, by rw [post.1, post.2.1]⟩)
  apply composed.imp
  · exact fun _ _ h => h
  · rintro _ ws ws' e _ ⟨middle, e₀, e₁, first, second, rfl⟩
    exact ⟨second.2.1, second.1.trans first.2.1,
      by simp [first.2.2, second.2.2]⟩
  · omega
  · omega

end NtimeDspace.ReplaceRegisterMachine
