import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank

/-!
A driver-word loop in the actual CSLib machine model. A round removes one
symbol from a designated tape and reestablishes a word-level invariant. Every
round resets all heads. The visited-cell bound is independent of the number
of rounds, rather than obtained by summing the individual space bounds.
The empty driver still executes one round, so the body contract must cover it.
-/

namespace NtimeDspace.RegisterLoop

open Turing Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-- Number of body calls made by a tail-consuming loop. The library loop is a
repeat-until construct, so it makes one call even for an empty driver. -/
def calls (length : ℕ) : ℕ := length - 1 + 1

theorem calls_eq_max (length : ℕ) : calls length = max 1 length := by
  unfold calls
  omega

/-- A decreasing driver word turns a round specification into a terminating
machine specification. `I n` may track values of other registers after round
`n`; its natural index is a proof index, not an extra machine register. -/
theorem transforms_tail_loop (driver : Fin k) (body : MultiTapeTM k Symbol State)
    (length t s : ℕ) (I : ℕ → List Symbol → (Fin k → List Symbol) → Prop)
    (round : ∀ n < calls length, TransformsTapes body
      (fun input ws => I n input ws ∧ (ws driver).length = length - n)
      (fun input ws ws' emitted => I (n + 1) input ws' ∧
        ws' driver = (ws driver).tail ∧ emitted = []) t s) :
    TransformsTapes (repeatUntilBlank driver body)
      (fun input ws => I 0 input ws ∧ (ws driver).length = length)
      (fun input _ ws' emitted => I (calls length) input ws' ∧
        ws' driver = [] ∧ emitted = [])
      (calls length * (t + 1)) (2 * k * s + k) := by
  let P : ℕ → List Symbol → (Fin k → List Symbol) → List Symbol → Prop :=
    fun n input ws emitted => I n input ws ∧
      (ws driver).length = length - n ∧ emitted = []
  let R : List Symbol → (Fin k → List Symbol) → List Symbol → Prop :=
    fun input ws emitted => I (calls length) input ws ∧ ws driver = [] ∧ emitted = []
  have next : ∀ n < length - 1, ∀ emitted, TransformsTapes body
      (fun input ws => P n input ws emitted)
      (fun input _ ws' e => P (n + 1) input ws' (emitted ++ e) ∧ ws' driver ≠ []) t s := by
    intro n hn emitted
    apply (round n (by unfold calls; omega)).imp
    · intro input ws pre
      exact ⟨pre.1, pre.2.1⟩
    · intro input ws ws' e pre post
      have new_length : (ws' driver).length = length - (n + 1) := by
        rw [post.2.1, List.length_tail, pre.2.1]
        omega
      refine ⟨⟨post.1, new_length, ?_⟩, ?_⟩
      · simp [pre.2.2, post.2.2]
      · intro empty
        have := congrArg List.length empty
        simp only [List.length_nil] at this
        omega
    · exact le_rfl
    · exact le_rfl
  have stop : ∀ emitted, TransformsTapes body
      (fun input ws => P (length - 1) input ws emitted)
      (fun input _ ws' e => R input ws' (emitted ++ e) ∧ ws' driver = []) t s := by
    intro emitted
    apply (round (length - 1) (by unfold calls; omega)).imp
    · intro input ws pre
      exact ⟨pre.1, pre.2.1⟩
    · intro input ws ws' e pre post
      have empty : ws' driver = [] := by
        apply List.length_eq_zero_iff.mp
        rw [post.2.1, List.length_tail, pre.2.1]
        omega
      exact ⟨⟨post.1, empty, by simp [pre.2.2, post.2.2]⟩, empty⟩
    · exact le_rfl
    · exact le_rfl
  apply (transformsTapes_repeatUntilBlank driver next stop).imp
  · intro input ws pre
    exact ⟨pre.1, by simpa using pre.2, rfl⟩
  · intro input ws ws' e _ post
    exact post
  · exact le_rfl
  · exact le_rfl

/-- A uniform round contract works for drivers of any length at most `limit`.
The invariant and the body stay unchanged; no counter for the length is added
to the concrete machine. -/
theorem transforms_tail_loop_bounded (driver : Fin k)
    (body : MultiTapeTM k Symbol State) (limit t s : ℕ)
    (I : ℕ → List Symbol → (Fin k → List Symbol) → Prop)
    (round : ∀ n, TransformsTapes body
      (fun input ws => I n input ws)
      (fun input ws ws' emitted => I (n + 1) input ws' ∧
        ws' driver = (ws driver).tail ∧ emitted = []) t s) :
    TransformsTapes (repeatUntilBlank driver body)
      (fun input ws => I 0 input ws ∧ (ws driver).length ≤ limit)
      (fun input ws ws' emitted => I (calls (ws driver).length) input ws' ∧
        ws' driver = [] ∧ emitted = [])
      (max 1 limit * (t + 1)) (2 * k * s + k) := by
  intro input ws out pre
  have exact_round : ∀ n < calls (ws driver).length, TransformsTapes body
      (fun input words => I n input words ∧
        (words driver).length = (ws driver).length - n)
      (fun input words words' emitted => I (n + 1) input words' ∧
        words' driver = (words driver).tail ∧ emitted = []) t s := by
    intro n _
    apply (round n).imp
    · exact fun _ _ h => h.1
    · exact fun _ _ _ _ _ h => h
    · exact le_rfl
    · exact le_rfl
  obtain ⟨ws', emitted, post, path, first, last, time, space⟩ :=
    transforms_tail_loop driver body (ws driver).length t s I exact_round
      input ws out ⟨pre.1, rfl⟩
  refine ⟨ws', emitted, post, path, first, last, ?_, space⟩
  apply time.trans
  apply Nat.mul_le_mul_right
  rw [calls_eq_max]
  exact max_le_max le_rfl pre.2

end NtimeDspace.RegisterLoop
