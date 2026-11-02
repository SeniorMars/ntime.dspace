import NtimeDspace.ModularMultiplyInitialization
import NtimeDspace.ModularMultiplyBody
import NtimeDspace.RegisterLoop

/-!
An eleven-tape modular-multiplication machine, built from fixed finite-state
initialization, repeated modular doubling/addition, and final cleanup. The
multiplier is consumed one bit at a time. The original three input words are
preserved, the result has their original width, and all remaining work tapes
finish blank. The loop uses a shared visited-cell bound independent of its
number of rounds; no host-language multiplication is executed by the machine.
-/

namespace NtimeDspace.ModularMultiplyMachine

open Turing Turing.MultiTapeTM BinaryCounterMachine

abbrev Words := ModularMultiplyInitialization.Words
abbrev Ready := ModularMultiplyInitialization.Ready

noncomputable def loop := repeatUntilBlank 3 ModularMultiplyBody.machine

def cleanupTapes : Fin 2 ↪ Fin 11 :=
  ⟨![2, 4], by intro first second same; fin_cases first <;> fin_cases second <;> simp_all⟩

noncomputable def cleanup := ClearRegisterMachine.machine.extendTapes cleanupTapes

noncomputable def machine := (ModularMultiplyInitialization.machine.seq loop).seq cleanup

/-- The product is specification data; the transition code uses only additions. -/
def product (ws : Words) : ℕ := value (ws 0) * value (ws 1) % value (ws 2)

def residue (ws : Words) : ℕ :=
  (value (ws 5) + value (ws 4) * value (ws 3)) % value (ws 2)

/-- The iteration count is not stored: this invariant uses only tape values. -/
def Invariant (L : ℕ) (original ws : Words) : Prop :=
  ModularMultiplyBody.Ready L ws ∧
    (∀ i : Fin 11, i.val < 3 → ws i = original i) ∧ residue ws = product original

/-- The complete final tuple has one result word and no other mutable words. -/
def finalWords (original : Words) (result : List Bool) : Words :=
  fun i => if i.val < 3 then original i else if i = 5 then result else []

def Complete (L : ℕ) (original ws : Words) : Prop :=
  (∀ i : Fin 11, i.val < 3 → ws i = original i) ∧
    (ws 5).length = L ∧ value (ws 5) = product original ∧
    (∀ i : Fin 11, 3 ≤ i.val → i ≠ 5 → ws i = [])

theorem complete_exact_words (L : ℕ) (original ws : Words) (complete : Complete L original ws) :
    ws = finalWords original (ws 5) := by
  funext i
  unfold finalWords
  by_cases source : i.val < 3
  · rw [ite_eq_left source]
    exact complete.1 i source
  · rw [ite_eq_right source]
    by_cases result : i = 5
    · subst i
      simp
    · rw [ite_eq_right result]
      exact complete.2.2.2 i (by omega) result

private theorem width_positive (L : ℕ) (ws : Words) (ready : Ready L ws) : 0 < L := by
  have nonempty : (ws 2).length ≠ 0 := by
    intro zero
    have empty : ws 2 = [] := List.eq_nil_of_length_eq_zero zero
    have := ready.modulus_positive
    simp [empty, value] at this
  have := ready.modulus_length
  omega

private theorem value_replicate_false (L : ℕ) : value (List.replicate L false) = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simp [List.replicate_succ, value, ih]

theorem initial_invariant (L : ℕ) (ws : Words) (ready : Ready L ws) :
    Invariant L ws (ModularMultiplyInitialization.initialWords L ws) := by
  have source := ModularMultiplyInitialization.initialWords_sources L ws
  have source2 := source 2 (by decide)
  refine ⟨?_, source, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [source2] using ready.modulus_length
    · simpa using ready.first_length
    · simp
    · simpa only [source2] using ready.modulus_positive
    · simpa only [source2, ModularMultiplyInitialization.initialWords_current]
        using ready.first_lt_modulus
    · simpa only [source2, ModularMultiplyInitialization.initialWords_accumulator,
        value_replicate_false] using ready.modulus_positive
    · simpa using ready.second_length.le
    · exact ModularMultiplyInitialization.initialWords_scratch L ws ready
  · simp [residue, product, source2, value_replicate_false]

/-- The body may also execute on an empty driver. That case preserves the
residue even though it doubles the now-unused current multiplicand. -/
theorem round_residue (before after : Words)
    (modulus : after 2 = before 2) (driver : after 3 = (before 3).tail)
    (current : value (after 4) = ModularMultiplication.double (value (before 2)) (value (before 4)))
    (accumulator : value (after 5) = ModularMultiplication.addBit (value (before 2))
      ((before 3).head?.getD false) (value (before 4)) (value (before 5))) :
    residue after = residue before := by
  unfold residue
  rw [modulus, driver, current, accumulator]
  cases digits : before 3 with
  | nil => simp [ModularMultiplication.addBit, value]
  | cons bit rest =>
      simpa using ModularMultiplication.round_invariant (value (before 2)) bit rest
        (value (before 4)) (value (before 5))

private theorem transforms_loop (L : ℕ) (original : Words) :
    TransformsTapes loop
      (fun _ ws => Invariant L original ws ∧ (ws 3).length = L)
      (fun _ _ ws' emitted => Invariant L original ws' ∧ ws' 3 = [] ∧ emitted = [])
      (RegisterLoop.calls L * (60 * L + 81)) (22 * (64 * L + 294) + 11) := by
  apply RegisterLoop.transforms_tail_loop 3 ModularMultiplyBody.machine L (60 * L + 80)
    (64 * L + 294) (fun _ _ ws => Invariant L original ws)
  intro _ _
  apply (ModularMultiplyBody.transforms_body L).imp (fun _ _ pre => pre.1.1)
  · intro _ before after emitted pre post
    obtain ⟨ready, sources, driver, current, accumulator, output⟩ := post
    refine ⟨⟨ready, ?_, ?_⟩, driver, output⟩
    · intro i source
      exact (sources i source).trans (pre.1.2.1 i source)
    · exact (round_residue before after (sources 2 (by decide)) driver current accumulator).trans
        pre.1.2.2
  · exact le_rfl
  · exact le_rfl

private theorem transforms_cleanup (L : ℕ) (original : Words) :
    TransformsTapes cleanup
      (fun _ ws => Invariant L original ws ∧ ws 3 = [])
      (fun _ _ ws' emitted => Complete L original ws' ∧ emitted = [])
      (2 * L + 2) (2 * L + 13) := by
  apply (TapeEmbedding.transforms_extendTapes (ClearRegisterMachine.transforms_clear L) cleanupTapes).imp
  · intro _ ws pre
    change (ws 2).length ≤ L ∧ (ws 4).length ≤ (ws 2).length
    exact ⟨pre.1.1.modulus_length.le, by rw [pre.1.1.current_length, pre.1.1.modulus_length]⟩
  · intro _ ws ws' emitted pre post
    obtain ⟨⟨marker, cleared, output⟩, unchanged⟩ := post
    change ws' 2 = ws 2 at marker
    change ws' 4 = [] at cleared
    have same (i : Fin 11) (ne2 : i ≠ 2) (ne4 : i ≠ 4) : ws' i = ws i := by
      apply unchanged i
      rintro ⟨j, equation⟩
      fin_cases j
      · exact ne2 equation.symm
      · exact ne4 equation.symm
    have result_same := same 5 (by decide) (by decide)
    have result_value : value (ws 5) = product original := by
      have invariant := pre.1.2.2
      simpa only [residue, pre.2, value, Nat.mul_zero, Nat.add_zero,
        Nat.mod_eq_of_lt pre.1.1.accumulator_small] using invariant
    refine ⟨⟨?_, ?_, ?_, ?_⟩, output⟩
    · intro i source
      have ne4 : i ≠ 4 := by intro eq; subst eq; simp at source
      by_cases isMarker : i = 2
      · subst i
        exact marker.trans (pre.1.2.1 2 (by decide))
      · exact (same i isMarker ne4).trans (pre.1.2.1 i source)
    · rw [result_same]
      exact pre.1.1.accumulator_length
    · rw [result_same]
      exact result_value
    · intro i scratch notResult
      by_cases isCurrent : i = 4
      · subst i
        exact cleared
      · have ne2 : i ≠ 2 := by intro eq; subst eq; simp at scratch
        rw [same i ne2 isCurrent]
        by_cases isDriver : i = 3
        · subst i
          exact pre.2
        · exact pre.1.1.scratch i (by
            have ne3 : i.val ≠ 3 := fun h => isDriver (Fin.ext h)
            have ne4 : i.val ≠ 4 := fun h => isCurrent (Fin.ext h)
            have ne5 : i.val ≠ 5 := fun h => notResult (Fin.ext h)
            omega)
  · exact le_rfl
  · omega

private theorem transforms_from (L : ℕ) (original : Words) (ready : Ready L original) :
    TransformsTapes machine (fun _ ws => ws = original)
      (fun _ _ ws' emitted => Complete L original ws' ∧ emitted = [])
      (60 * L ^ 2 + 89 * L + 8) (1416 * L + 6531) := by
  have initialization : TransformsTapes ModularMultiplyInitialization.machine
      (fun _ ws => ws = original)
      (fun _ _ ws' emitted => Invariant L original ws' ∧ (ws' 3).length = L ∧ emitted = [])
      (6 * L + 6) (6 * L + 39) := by
    apply (ModularMultiplyInitialization.transforms_initialize L).imp
    · intro _ _ same
      subst same
      exact ready
    · intro _ actual after emitted same post
      subst same
      obtain ⟨rfl, output⟩ := post
      exact ⟨initial_invariant L actual ready, by simpa using ready.second_length, output⟩
    · exact le_rfl
    · exact le_rfl
  have initialized_loop := transformsTapes_seq initialization (transforms_loop L original)
    (fun _ _ _ _ _ post => ⟨post.1, post.2.1⟩)
  have complete := transformsTapes_seq initialized_loop (transforms_cleanup L original) (by
    rintro _ _ _ _ _ ⟨_, _, _, _, post, _⟩
    exact ⟨post.1, post.2.1⟩)
  apply complete.imp (fun _ _ pre => pre)
  · rintro _ _ _ _ _ ⟨_, firstOutput, secondOutput,
      ⟨_, _, _, firstPost, loopPost, rfl⟩, cleanupPost, rfl⟩
    exact ⟨cleanupPost.1, by simp [firstPost.2.2, loopPost.2.2, cleanupPost.2]⟩
  · have positive := width_positive L original ready
    rw [RegisterLoop.calls_eq_max, max_eq_right (by omega : 1 ≤ L)]
    nlinarith
  · omega

/-- One fixed eleven-tape machine multiplies an initial residue by any
same-width multiplier. All originals survive; only the fixed-width result
remains on tape5, and every other mutable tape is blank. Bounds count actual
steps and visited work cells, with space independent of the number of rounds. -/
theorem transforms_modularMultiply (L : ℕ) :
    TransformsTapes machine (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => ws' = finalWords ws (ws' 5) ∧
        (ws' 5).length = L ∧ value (ws' 5) = value (ws 0) * value (ws 1) % value (ws 2) ∧
        emitted = [])
      (60 * L ^ 2 + 89 * L + 8) (1416 * L + 6531) := by
  intro input ws out ready
  obtain ⟨result, emitted, post, path, first, last, time, space⟩ :=
    transforms_from L ws ready input ws out rfl
  exact ⟨result, emitted,
    ⟨complete_exact_words L ws result post.1, post.1.2.1, post.1.2.2.1, post.2⟩,
    path, first, last, time, space⟩

end NtimeDspace.ModularMultiplyMachine
