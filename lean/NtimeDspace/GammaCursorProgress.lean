import NtimeDspace.BoundedGammaPayload

/-!
One-step cursor facts for an enclosing reader that immediately commits a
completed gamma codeword and continues. Such a reader needs progress also on
the accepting gamma transition, not only on still-running gamma states.
-/

namespace NtimeDspace.GammaCursorProgress

open BoundedGammaPayload

theorem next_cursor_bounds (bound : ℕ) (state : State) (bit : Option Bool) :
    state.cursor ≤ (next bound (state, bit)).cursor ∧
      (next bound (state, bit)).cursor ≤ state.cursor + 1 ∧
      (bit = none → (next bound (state, bit)).cursor = state.cursor) := by
  cases bit with
  | none => simp only [next]; split_ifs <;> simp
  | some bit =>
    cases bit <;> simp only [next, appendValue] <;> split_ifs <;> simp_all

/-- Successful completion consumes the last payload bit too. Rejected steps
may leave the cursor stationary, so rejection is excluded explicitly. -/
theorem next_notRejected_cursor (bound : ℕ) (state : State) (bit : Option Bool)
    (before : halted state = false) (after : (next bound (state, bit)).phase ≠ 3) :
    (next bound (state, bit)).cursor = state.cursor + 1 := by
  have phase : state.phase = 0 ∨ state.phase = 1 := by
    simp only [halted, decide_eq_false_iff_not] at before
    have values : state.phase.val = 0 ∨ state.phase.val = 1 := by omega
    rcases values with value | value
    · exact Or.inl (Fin.ext value)
    · exact Or.inr (Fin.ext value)
  rcases phase with pref | payload
  · cases bit with
    | none => simp [next, pref] at after
    | some bit =>
      cases bit <;> simp only [next, pref, ↓reduceIte] at after ⊢ <;>
        split_ifs at after ⊢ <;> simp_all
  · cases bit with
    | none => simp [next, payload] at after
    | some bit =>
      cases result : appendValue bound state.accumulator bit <;>
        simp [next, payload, result] at after ⊢

end NtimeDspace.GammaCursorProgress
