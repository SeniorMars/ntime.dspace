import NtimeDspace.CopyRegisterMachine
import NtimeDspace.MapRegisterMachine
import NtimeDspace.TapeEmbedding

/-!
Initialization for repeated-doubling modular multiplication on eleven tapes.
Three fixed finite-control machines copy the multiplier to the driver, copy the
multiplicand to the current residue, and zero the accumulator. The remaining
scratch words stay blank. The word tuples below specify tape contents; they are
not buffers allocated by the machine.
-/

namespace NtimeDspace.ModularMultiplyInitialization

open Turing Turing.MultiTapeTM BinaryCounterMachine

abbrev Words := Fin 11 → List Bool

def registerTapes (source target : Fin 11) (different : source ≠ target) : Fin 2 ↪ Fin 11 :=
  ⟨fun i => if i = 0 then source else target, by
    intro first second same
    fin_cases first <;> fin_cases second <;> simp_all⟩

noncomputable def copyDriver :=
  CopyRegisterMachine.machine.extendTapes (registerTapes 1 3 (by decide))
noncomputable def copyCurrent :=
  CopyRegisterMachine.machine.extendTapes (registerTapes 0 4 (by decide))
noncomputable def zeroAccumulator :=
  MapRegisterMachine.zeroMachine.extendTapes (registerTapes 2 5 (by decide))
noncomputable def machine := (copyDriver.seq copyCurrent).seq zeroAccumulator

/-- Only the multiplicand must initially be a residue. The multiplier can be
any binary word of the same width as the positive modulus. -/
structure Ready (L : ℕ) (ws : Words) : Prop where
  first_length : (ws 0).length = L
  second_length : (ws 1).length = L
  modulus_length : (ws 2).length = L
  modulus_positive : 0 < value (ws 2)
  first_lt_modulus : value (ws 0) < value (ws 2)
  scratch : ∀ i : Fin 11, 3 ≤ i.val → ws i = []

def initialWords (L : ℕ) (ws : Words) : Words :=
  Function.update (Function.update (Function.update ws 3 (ws 1)) 4 (ws 0))
    5 (List.replicate L false)

@[simp] theorem initialWords_driver (L : ℕ) (ws : Words) :
    initialWords L ws 3 = ws 1 := by simp [initialWords]

@[simp] theorem initialWords_current (L : ℕ) (ws : Words) :
    initialWords L ws 4 = ws 0 := by simp [initialWords]

@[simp] theorem initialWords_accumulator (L : ℕ) (ws : Words) :
    initialWords L ws 5 = List.replicate L false := by simp [initialWords]

theorem initialWords_sources (L : ℕ) (ws : Words) (i : Fin 11) (source : i.val < 3) :
    initialWords L ws i = ws i := by
  have ne3 : i ≠ 3 := by intro h; subst h; simp at source
  have ne4 : i ≠ 4 := by intro h; subst h; simp at source
  have ne5 : i ≠ 5 := by intro h; subst h; simp at source
  simp [initialWords, ne3, ne4, ne5]

theorem initialWords_scratch (L : ℕ) (ws : Words) (ready : Ready L ws)
    (i : Fin 11) (scratch : 6 ≤ i.val) : initialWords L ws i = [] := by
  have ne3 : i ≠ 3 := by intro h; subst h; simp at scratch
  have ne4 : i ≠ 4 := by intro h; subst h; simp at scratch
  have ne5 : i ≠ 5 := by intro h; subst h; simp at scratch
  simpa [initialWords, ne3, ne4, ne5] using ready.scratch i (by omega)

private def Exact {S : Type*} (tm : MultiTapeTM 11 Bool S)
    (before after : Words) (time space : ℕ) : Prop :=
  TransformsTapes tm (fun _ ws => ws = before)
    (fun _ _ ws' emitted => ws' = after ∧ emitted = []) time space

private theorem exact_seq {S T : Type*} {first : MultiTapeTM 11 Bool S}
    {second : MultiTapeTM 11 Bool T} {before middle after : Words} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : Exact first before middle t₁ s₁) (h₂ : Exact second middle after t₂ s₂) :
    Exact (first.seq second) before after (t₁ + t₂) (s₁ + s₂) := by
  apply (transformsTapes_seq h₁ h₂ (fun _ _ _ _ _ post => post.1)).imp
    (fun _ _ pre => pre)
  · rintro _ _ _ _ _ ⟨_, _, _, first_post, second_post, rfl⟩
    exact ⟨second_post.1, by simp [first_post.2, second_post.2]⟩
  · exact le_rfl
  · exact le_rfl

private theorem exact_copy (L : ℕ) (ws : Words) (source target : Fin 11)
    (different : source ≠ target) (length : (ws source).length ≤ L)
    (blank : ws target = []) :
    Exact (CopyRegisterMachine.machine.extendTapes (registerTapes source target different))
      ws (Function.update ws target (ws source)) (2 * L + 2) (2 * (L + 2) + 9) := by
  apply (TapeEmbedding.transforms_extendTapes (CopyRegisterMachine.transforms_copy L)
    (registerTapes source target different)).imp
  · intro _ _ pre
    subst pre
    exact ⟨length, blank⟩
  · intro _ actual result emitted pre post
    subst pre
    obtain ⟨⟨preserved, copied, output⟩, unchanged⟩ := post
    change result source = actual source at preserved
    change result target = actual source at copied
    refine ⟨?_, output⟩
    funext i
    by_cases isTarget : i = target
    · subst i
      simpa using copied
    · by_cases isSource : i = source
      · subst i
        simpa [different] using preserved
      · have outside : i ∉ Set.range (registerTapes source target different) := by
          rintro ⟨j, same⟩
          fin_cases j
          · exact isSource same.symm
          · exact isTarget same.symm
        simpa [isTarget] using unchanged i outside
  · exact le_rfl
  · exact le_rfl

private theorem exact_zero (L : ℕ) (ws : Words)
    (length : (ws 2).length = L) (blank : ws 5 = []) :
    Exact zeroAccumulator ws (Function.update ws 5 (List.replicate L false))
      (2 * L + 2) (2 * (L + 2) + 9) := by
  apply (TapeEmbedding.transforms_extendTapes (MapRegisterMachine.transforms_zero L)
    (registerTapes 2 5 (by decide))).imp
  · intro _ _ pre
    subst pre
    exact ⟨length.le, blank⟩
  · intro _ actual result emitted pre post
    subst pre
    obtain ⟨⟨preserved, cleared, _, _, output⟩, unchanged⟩ := post
    change result 2 = actual 2 at preserved
    change result 5 = List.replicate (actual 2).length false at cleared
    refine ⟨?_, output⟩
    funext i
    by_cases isTarget : i = 5
    · subst i
      simpa [length] using cleared
    · by_cases isSource : i = 2
      · subst i
        simpa using preserved
      · have outside : i ∉ Set.range (registerTapes 2 5 (by decide)) := by
          rintro ⟨j, same⟩
          fin_cases j
          · exact isSource same.symm
          · exact isTarget same.symm
        simpa [isTarget] using unchanged i outside
  · exact le_rfl
  · exact le_rfl

/-- A fixed eleven-tape finite-control machine initializes all three loop
registers and resets every head. The original input words, input tape and output
are preserved. Bounds count actual computation steps and visited work cells. -/
theorem transforms_initialize (L : ℕ) :
    TransformsTapes machine (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => ws' = initialWords L ws ∧ emitted = [])
      (6 * L + 6) (6 * L + 39) := by
  intro input ws out ready
  have first := exact_copy L ws 1 3 (by decide) ready.second_length.le
    (ready.scratch 3 (by decide))
  have second := exact_copy L (Function.update ws 3 (ws 1)) 0 4 (by decide)
    (by simpa using ready.first_length.le)
    (by simpa using ready.scratch 4 (by decide))
  have third := exact_zero L
    (Function.update (Function.update ws 3 (ws 1)) 4 (ws 0))
    (by simpa using ready.modulus_length)
    (by simpa using ready.scratch 5 (by decide))
  have combined := exact_seq (exact_seq first second) third
  have bounded : Exact machine ws (initialWords L ws) (6 * L + 6) (6 * L + 39) := by
    simpa only [Exact, machine, copyDriver, copyCurrent, initialWords,
      Function.update_of_ne (by decide : (0 : Fin 11) ≠ 3)]
      using combined.mono (by omega : (2 * L + 2 + (2 * L + 2)) + (2 * L + 2) ≤ 6 * L + 6)
        (by omega : (2 * (L + 2) + 9 + (2 * (L + 2) + 9)) + (2 * (L + 2) + 9) ≤
          6 * L + 39)
  exact bounded input ws out rfl

end NtimeDspace.ModularMultiplyInitialization
