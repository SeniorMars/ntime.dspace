import NtimeDspace.ModularAddMachine
import NtimeDspace.ClearRegisterMachine
import NtimeDspace.NormalizeRegisterMachine

/-!
A reusable seven-tape modular-addition macro. Tapes 0, 1, and 2 are preserved
equal-width residues and modulus. Tape 6 receives the residue at exactly that
width; tapes 3, 4, and 5 finish blank. In-place truncation first removes the
at-most-two extra cells, so the preserved modulus can delimit every clear.
All intermediate words below specify tape contents, not host-side buffers.
-/

namespace NtimeDspace.CleanModularAddMachine

open Turing Turing.MultiTapeTM BinaryCounterMachine

abbrev Words := ModularAddMachine.Words
abbrev Ready := ModularAddMachine.Ready

def truncateTapes (target : Fin 7) (different : target ≠ 2) : Fin 2 ↪ Fin 7 :=
  ⟨fun i => if i = 0 then target else 2, by
    intro first second same
    fin_cases first <;> fin_cases second <;> simp_all⟩

def clearTapes (target : Fin 7) (different : target ≠ 2) : Fin 2 ↪ Fin 7 :=
  ⟨fun i => if i = 0 then 2 else target, by
    intro first second same
    fin_cases first <;> fin_cases second <;> simp_all⟩

noncomputable def truncate (target : Fin 7) (different : target ≠ 2) :=
  NormalizeRegisterMachine.machine.extendTapes (truncateTapes target different)

noncomputable def clear (target : Fin 7) (different : target ≠ 2) :=
  ClearRegisterMachine.machine.extendTapes (clearTapes target different)

noncomputable def machine :=
  ((((((ModularAddMachine.machine.seq (truncate 3 (by decide))).seq
    (truncate 4 (by decide))).seq (truncate 6 (by decide))).seq
    (clear 3 (by decide))).seq (clear 4 (by decide))).seq (clear 5 (by decide)))

def truncateWords (L : ℕ) (target : Fin 7) (ws : Words) : Words :=
  Function.update ws target ((ws target).take L)

def clearWords (target : Fin 7) (ws : Words) : Words := Function.update ws target []

def truncatedWords (L : ℕ) (ws : Words) : Words :=
  truncateWords L 6 (truncateWords L 4 (truncateWords L 3 (ModularAddMachine.finalWords ws)))

def finalWords (L : ℕ) (ws : Words) : Words :=
  clearWords 5 (clearWords 4 (clearWords 3 (truncatedWords L ws)))

private def Exact {S : Type*} (tm : MultiTapeTM 7 Bool S)
    (before after : Words) (time space : ℕ) : Prop :=
  TransformsTapes tm (fun _ ws => ws = before)
    (fun _ _ ws' emitted => ws' = after ∧ emitted = []) time space

private theorem exact_seq {S T : Type*} {first : MultiTapeTM 7 Bool S}
    {second : MultiTapeTM 7 Bool T} {before middle after : Words} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : Exact first before middle t₁ s₁) (h₂ : Exact second middle after t₂ s₂) :
    Exact (first.seq second) before after (t₁ + t₂) (s₁ + s₂) := by
  apply (transformsTapes_seq h₁ h₂ (fun _ _ _ _ _ post => post.1)).imp
    (fun _ _ pre => pre)
  · rintro _ _ _ _ _ ⟨_, _, _, first_post, second_post, rfl⟩
    exact ⟨second_post.1, by simp [first_post.2, second_post.2]⟩
  · exact le_rfl
  · exact le_rfl

private theorem exact_add (L : ℕ) (ws : Words) (ready : Ready L ws) :
    Exact ModularAddMachine.machine ws (ModularAddMachine.finalWords ws)
      (8 * L + 13) (10 * L + 43) := by
  apply (ModularAddMachine.transforms_modularAdd L).imp
  · intro _ _ pre
    subst pre
    exact ready
  · intro _ _ _ _ pre post
    subst pre
    exact ⟨post.1, post.2.2.2.2⟩
  · exact le_rfl
  · exact le_rfl

private theorem exact_clear (L : ℕ) (target : Fin 7) (different : target ≠ 2)
    (ws : Words) (marker : (ws 2).length ≤ L) (short : (ws target).length ≤ (ws 2).length) :
    Exact (clear target different) ws (clearWords target ws)
      (2 * L + 2) (2 * (L + 2) + 5) := by
  apply (TapeEmbedding.transforms_extendTapes (ClearRegisterMachine.transforms_clear L)
    (clearTapes target different)).imp
  · intro _ _ pre
    subst pre
    exact ⟨marker, short⟩
  · intro _ actual result emitted pre post
    subst pre
    obtain ⟨⟨source, blank, output⟩, unchanged⟩ := post
    change result 2 = actual 2 at source
    change result target = [] at blank
    refine ⟨?_, output⟩
    funext i
    by_cases isTarget : i = target
    · subst i
      simpa [clearWords] using blank
    · by_cases isMarker : i = 2
      · subst i
        simpa [clearWords, different.symm] using source
      · have outside : i ∉ Set.range (clearTapes target different) := by
          rintro ⟨j, same⟩
          fin_cases j
          · exact isMarker same.symm
          · exact isTarget same.symm
        simpa [clearWords, isTarget] using unchanged i outside
  · exact le_rfl
  · exact le_rfl

private theorem exact_truncate (L : ℕ) (target : Fin 7) (different : target ≠ 2)
    (ws : Words) (lower : L ≤ (ws target).length) (upper : (ws target).length ≤ L + 2)
    (marker : (ws 2).length = L) :
    Exact (truncate target different) ws (truncateWords L target ws)
      (2 * L + 4) (2 * (L + 3) + 5) := by
  apply (TapeEmbedding.transforms_extendTapes (NormalizeRegisterMachine.transforms_truncate L)
    (truncateTapes target different)).imp
  · intro _ _ pre
    subst pre
    exact ⟨lower, upper, marker⟩
  · intro _ actual result emitted pre post
    subst pre
    obtain ⟨⟨truncated, preserved, _, output⟩, unchanged⟩ := post
    change result target = (actual target).take L at truncated
    change result 2 = actual 2 at preserved
    refine ⟨?_, output⟩
    funext i
    by_cases isTarget : i = target
    · subst i
      simpa [truncateWords] using truncated
    · by_cases isMarker : i = 2
      · subst i
        simpa [truncateWords, different.symm] using preserved
      · have outside : i ∉ Set.range (truncateTapes target different) := by
          rintro ⟨j, same⟩
          fin_cases j
          · exact isTarget same.symm
          · exact isMarker same.symm
        simpa [truncateWords, isTarget] using unchanged i outside
  · exact le_rfl
  · exact le_rfl

private theorem width_positive (L : ℕ) (ws : Words) (ready : Ready L ws) : 0 < L := by
  have nonempty : (ws 2).length ≠ 0 := by
    intro zero
    have empty : ws 2 = [] := List.eq_nil_of_length_eq_zero zero
    have := ready.modulus_positive
    simp [empty, value] at this
  have := ready.modulus_length
  omega

private theorem modular_result_length_lower (L : ℕ) (ws : Words) (ready : Ready L ws) :
    L ≤ (ModularAddMachine.finalWords ws 6).length := by
  rw [ModularAddMachine.finalWords_result ws
    (ready.first_length.trans ready.second_length.symm)]
  split <;> simp only [AddRegistersMachine.sumBits_length,
    SubtractRegistersMachine.differenceBits_length, ready.first_length] <;> omega

private theorem modular_result_value_small (L : ℕ) (ws : Words) (ready : Ready L ws) :
    value (ModularAddMachine.finalWords ws 6) < 2 ^ L := by
  rw [ModularAddMachine.finalWords_value L ws ready]
  have modulus_bound := CompareRegistersMachine.value_lt_pow_length (ws 2)
  rw [ready.modulus_length] at modulus_bound
  exact (Nat.mod_lt _ ready.modulus_positive).trans modulus_bound

private theorem exact_program (L : ℕ) (ws : Words) (ready : Ready L ws) :
    Exact machine ws (finalWords L ws) (20 * L + 31) (22 * L + 103) := by
  let added := ModularAddMachine.finalWords ws
  have marker : (added 2).length = L := by
    dsimp [added]
    rw [ModularAddMachine.finalWords_sources ws 2 (by decide)]
    exact ready.modulus_length
  have sum_length : (added 3).length = L + 1 := by
    simp [added, ModularAddMachine.finalWords, ModularAddMachine.reduceWords,
      ModularAddMachine.compareWords, ModularAddMachine.padWords, ModularAddMachine.addWords,
      AddRegistersMachine.sumBits_length, ready.first_length]
  have padded_length : (added 4).length = L + 1 := by
    simp [added, ModularAddMachine.finalWords, ModularAddMachine.reduceWords,
      ModularAddMachine.compareWords, ModularAddMachine.padWords, ModularAddMachine.addWords,
      ready.modulus_length]
  have flag_length : (added 5).length = 1 := by
    simp [added, ModularAddMachine.finalWords, ModularAddMachine.reduceWords,
      ModularAddMachine.compareWords]
  have marker' : (ModularAddMachine.finalWords ws 2).length = L := marker
  have flag_length' : (ModularAddMachine.finalWords ws 5).length = 1 := flag_length
  have first := exact_add L ws ready
  have second := exact_truncate L 3 (by decide) added (by omega) (by omega) marker
  have third := exact_truncate L 4 (by decide) (truncateWords L 3 added)
    (by simp [truncateWords, padded_length])
    (by simp [truncateWords, padded_length])
    (by simpa [truncateWords] using marker)
  have fourth := exact_truncate L 6 (by decide) (truncateWords L 4 (truncateWords L 3 added))
    (by simpa [truncateWords, added] using modular_result_length_lower L ws ready)
    (by simpa [truncateWords, added] using ModularAddMachine.finalWords_length L ws ready)
    (by simpa [truncateWords] using marker)
  have fifth := exact_clear L 3 (by decide) (truncatedWords L ws)
    (by simpa [truncatedWords, truncateWords, added] using marker.le)
    (by simp [truncatedWords, truncateWords, marker'])
  have sixth := exact_clear L 4 (by decide) (clearWords 3 (truncatedWords L ws))
    (by simpa [clearWords, truncatedWords, truncateWords, added] using marker.le)
    (by simp [clearWords, truncatedWords, truncateWords, marker'])
  have seventh := exact_clear L 5 (by decide) (clearWords 4 (clearWords 3 (truncatedWords L ws)))
    (by simpa [clearWords, truncatedWords, truncateWords, added] using marker.le)
    (by simpa [clearWords, truncatedWords, truncateWords, marker', flag_length'] using
      Nat.succ_le_iff.mpr (width_positive L ws ready))
  exact (exact_seq (exact_seq (exact_seq (exact_seq (exact_seq (exact_seq
    first second) third) fourth) fifth) sixth) seventh).mono (by omega) (by omega)

theorem result_eq_take (L : ℕ) (ws : Words) :
    finalWords L ws 6 = (ModularAddMachine.finalWords ws 6).take L := by
  simp [finalWords, clearWords, truncatedWords, truncateWords]

theorem finalWords_sources (L : ℕ) (ws : Words) (i : Fin 7) (source : i.val < 3) :
    finalWords L ws i = ws i := by
  have ne3 : i ≠ 3 := by intro same; subst same; simp at source
  have ne4 : i ≠ 4 := by intro same; subst same; simp at source
  have ne5 : i ≠ 5 := by intro same; subst same; simp at source
  have ne6 : i ≠ 6 := by intro same; subst same; simp at source
  simp only [finalWords, clearWords, truncatedWords, truncateWords,
    Function.update_of_ne ne3, Function.update_of_ne ne4, Function.update_of_ne ne5,
    Function.update_of_ne ne6]
  exact ModularAddMachine.finalWords_sources ws i source

theorem finalWords_scratch (L : ℕ) (ws : Words) (i : Fin 7)
    (scratch : 3 ≤ i.val ∧ i.val ≤ 5) : finalWords L ws i = [] := by
  fin_cases i <;> simp_all [finalWords, clearWords]

theorem finalWords_length (L : ℕ) (ws : Words) (ready : Ready L ws) :
    (finalWords L ws 6).length = L := by
  rw [result_eq_take, List.length_take]
  exact Nat.min_eq_left (modular_result_length_lower L ws ready)

theorem finalWords_value (L : ℕ) (ws : Words) (ready : Ready L ws) :
    value (finalWords L ws 6) = (value (ws 0) + value (ws 1)) % value (ws 2) := by
  rw [result_eq_take, NormalizeRegisterMachine.value_take_eq _ L
    (modular_result_value_small L ws ready)]
  exact ModularAddMachine.finalWords_value L ws ready

/-- Fixed-width modular addition with every scratch tape blank afterward.
The full seven-tape tuple is specified, the three sources survive, and the
standard normal form resets all heads and preserves input/output. -/
theorem transforms_cleanModularAdd (L : ℕ) :
    TransformsTapes machine (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => ws' = finalWords L ws ∧
        value (ws' 6) = (value (ws 0) + value (ws 1)) % value (ws 2) ∧
        (ws' 6).length = L ∧
        (∀ i : Fin 7, i.val < 3 → ws' i = ws i) ∧
        (∀ i : Fin 7, 3 ≤ i.val ∧ i.val ≤ 5 → ws' i = []) ∧ emitted = [])
      (20 * L + 31) (22 * L + 103) := by
  intro input ws out ready
  obtain ⟨result, emitted, post, path, first, last, time, space⟩ :=
    exact_program L ws ready input ws out rfl
  refine ⟨result, emitted, ⟨post.1, ?_, ?_, ?_, ?_, post.2⟩,
    path, first, last, time, space⟩
  · rw [post.1]
    exact finalWords_value L ws ready
  · rw [post.1]
    exact finalWords_length L ws ready
  · rw [post.1]
    exact finalWords_sources L ws
  · rw [post.1]
    exact finalWords_scratch L ws

end NtimeDspace.CleanModularAddMachine
