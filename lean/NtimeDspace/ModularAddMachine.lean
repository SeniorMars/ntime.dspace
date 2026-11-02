import NtimeDspace.AddRegistersMachine
import NtimeDspace.PadRegisterMachine
import NtimeDspace.CompareRegistersMachine
import NtimeDspace.SubtractRegistersMachine
import NtimeDspace.CopyRegisterMachine
import NtimeDspace.TapeEmbedding
import NtimeDspace.BranchOnBit

/-!
Seven-tape modular addition composed from fixed finite-state CSLib machines.
The first three tapes contain equal-width residues `a`, `b`, and their positive
modulus. The four initially empty scratch tapes hold the sum, padded modulus,
comparison flag, and result. Scratch words remain explicit; this macro does not
clear or shorten them for a later call. All bounds concern actual run paths.
-/

namespace NtimeDspace.ModularAddMachine

open Turing Turing.MultiTapeTM BinaryCounterMachine

abbrev Words := Fin 7 → List Bool

def addTapes : Fin 3 ↪ Fin 7 :=
  ⟨![0, 1, 3], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def padTapes : Fin 2 ↪ Fin 7 :=
  ⟨![2, 4], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def compareTapes : Fin 3 ↪ Fin 7 :=
  ⟨![3, 4, 5], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def copyTapes : Fin 2 ↪ Fin 7 :=
  ⟨![3, 6], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def subtractTapes : Fin 3 ↪ Fin 7 :=
  ⟨![3, 4, 6], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

noncomputable def add := AddRegistersMachine.machine.extendTapes addTapes
noncomputable def pad := PadRegisterMachine.machine.extendTapes padTapes
noncomputable def compare := CompareRegistersMachine.machine.extendTapes compareTapes
noncomputable def copy := CopyRegisterMachine.machine.extendTapes copyTapes
noncomputable def subtract := SubtractRegistersMachine.machine.extendTapes subtractTapes
noncomputable def reduce := BranchOnBit.machine 5 copy subtract
noncomputable def machine := ((add.seq pad).seq compare).seq reduce

/-- These word tuples specify intermediate configurations; the machine stores
them on its tapes through the preceding primitive transitions. -/
def addWords (ws : Words) : Words :=
  Function.update ws 3 (AddRegistersMachine.sumBits (ws 0) (ws 1))
def padWords (ws : Words) : Words :=
  Function.update ws 4 (PadRegisterMachine.paddedBits (ws 2))
def compareWords (ws : Words) : Words :=
  Function.update ws 5 [decide (value (ws 3) < value (ws 4))]
def reduceWords (ws : Words) : Words :=
  Function.update ws 6 (if (ws 5).head? = some true then ws 3
    else SubtractRegistersMachine.differenceBits (ws 3) (ws 4))
def finalWords (ws : Words) : Words := reduceWords (compareWords (padWords (addWords ws)))

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

private theorem exact_add (L : ℕ) (ws : Words)
    (length : (ws 0).length ≤ L) (same : (ws 0).length = (ws 1).length)
    (blank : ws 3 = []) :
    Exact add ws (addWords ws) (2 * L + 2) (3 * (L + 2) + 4) := by
  apply (TapeEmbedding.transforms_extendTapes (AddRegistersMachine.transforms_add L) addTapes).imp
  · intro _ _ pre
    subst pre
    exact ⟨length, same, blank⟩
  · intro _ _ final emitted pre post
    subst pre
    rcases post with ⟨⟨h0, h1, h3, _, _, output⟩, unchanged⟩
    refine ⟨?_, output⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact unchanged 2 (by decide)
    · exact h3
    · exact unchanged 4 (by decide)
    · exact unchanged 5 (by decide)
    · exact unchanged 6 (by decide)
  · exact le_rfl
  · exact le_rfl

private theorem exact_pad (L : ℕ) (ws : Words)
    (length : (ws 2).length ≤ L) (blank : ws 4 = []) :
    Exact pad ws (padWords ws) (2 * L + 2) (2 * (L + 2) + 5) := by
  apply (TapeEmbedding.transforms_extendTapes (PadRegisterMachine.transforms_pad L) padTapes).imp
  · intro _ _ pre
    subst pre
    exact ⟨length, blank⟩
  · intro _ _ final emitted pre post
    subst pre
    rcases post with ⟨⟨h2, h4, _, _, output⟩, unchanged⟩
    refine ⟨?_, output⟩
    funext i
    fin_cases i
    · exact unchanged 0 (by decide)
    · exact unchanged 1 (by decide)
    · exact h2
    · exact unchanged 3 (by decide)
    · exact h4
    · exact unchanged 5 (by decide)
    · exact unchanged 6 (by decide)
  · exact le_rfl
  · exact le_rfl

private theorem exact_compare (L : ℕ) (ws : Words)
    (length : (ws 3).length ≤ L) (same : (ws 3).length = (ws 4).length)
    (blank : ws 5 = []) :
    Exact compare ws (compareWords ws) (2 * L + 2) (2 * (L + 2) + 1 + 4) := by
  apply (TapeEmbedding.transforms_extendTapes
    (CompareRegistersMachine.transforms_compare L) compareTapes).imp
  · intro _ _ pre
    subst pre
    exact ⟨length, same, blank⟩
  · intro _ _ final emitted pre post
    subst pre
    rcases post with ⟨⟨h3, h4, h5, output⟩, unchanged⟩
    refine ⟨?_, output⟩
    funext i
    fin_cases i
    · exact unchanged 0 (by decide)
    · exact unchanged 1 (by decide)
    · exact unchanged 2 (by decide)
    · exact h3
    · exact h4
    · exact h5
    · exact unchanged 6 (by decide)
  · exact le_rfl
  · exact le_rfl

private theorem exact_copy (L : ℕ) (ws : Words)
    (length : (ws 3).length ≤ L) (blank : ws 6 = []) :
    Exact copy ws (Function.update ws 6 (ws 3)) (2 * L + 2) (2 * (L + 2) + 5) := by
  apply (TapeEmbedding.transforms_extendTapes (CopyRegisterMachine.transforms_copy L) copyTapes).imp
  · intro _ _ pre
    subst pre
    exact ⟨length, blank⟩
  · intro _ _ final emitted pre post
    subst pre
    rcases post with ⟨⟨h3, h6, output⟩, unchanged⟩
    refine ⟨?_, output⟩
    funext i
    fin_cases i
    · exact unchanged 0 (by decide)
    · exact unchanged 1 (by decide)
    · exact unchanged 2 (by decide)
    · exact h3
    · exact unchanged 4 (by decide)
    · exact unchanged 5 (by decide)
    · exact h6
  · exact le_rfl
  · exact le_rfl

private theorem exact_subtract (L : ℕ) (ws : Words)
    (length : (ws 3).length ≤ L) (same : (ws 3).length = (ws 4).length)
    (blank : ws 6 = []) (ordered : value (ws 4) ≤ value (ws 3)) :
    Exact subtract ws (Function.update ws 6
      (SubtractRegistersMachine.differenceBits (ws 3) (ws 4)))
      (2 * L + 2) (3 * (L + 2) + 4) := by
  apply (TapeEmbedding.transforms_extendTapes
    (SubtractRegistersMachine.transforms_subtract L) subtractTapes).imp
  · intro _ _ pre
    subst pre
    exact ⟨length, same, blank, ordered⟩
  · intro _ _ final emitted pre post
    subst pre
    rcases post with ⟨⟨h3, h4, h6, _, _, output⟩, unchanged⟩
    refine ⟨?_, output⟩
    funext i
    fin_cases i
    · exact unchanged 0 (by decide)
    · exact unchanged 1 (by decide)
    · exact unchanged 2 (by decide)
    · exact h3
    · exact h4
    · exact unchanged 5 (by decide)
    · exact h6
  · exact le_rfl
  · exact le_rfl

private theorem exact_reduce (L : ℕ) (ws : Words)
    (length : (ws 3).length ≤ L) (same : (ws 3).length = (ws 4).length)
    (blank : ws 6 = [])
    (flag : (ws 5).head? = some (decide (value (ws 3) < value (ws 4)))) :
    Exact reduce ws (reduceWords ws) (2 * L + 3) (3 * (L + 2) + 4) := by
  have yes : TransformsTapes copy
      (fun _ actual => actual = ws ∧ (actual 5).head? = some true)
      (fun _ _ final emitted => final = reduceWords ws ∧ emitted = [])
      (2 * L + 2) (3 * (L + 2) + 4) := by
    apply (exact_copy L ws length blank).imp (fun _ _ pre => pre.1)
    · intro _ actual final emitted pre post
      have selected : (ws 5).head? = some true := by simpa only [pre.1] using pre.2
      simpa only [reduceWords, selected, ↓reduceIte] using post
    · exact le_rfl
    · omega
  have no : TransformsTapes subtract
      (fun _ actual => actual = ws ∧ (actual 5).head? ≠ some true)
      (fun _ _ final emitted => final = reduceWords ws ∧ emitted = [])
      (2 * L + 2) (3 * (L + 2) + 4) := by
    intro input actual out pre
    have selected : (ws 5).head? ≠ some true := by simpa only [pre.1] using pre.2
    have ordered : value (ws 4) ≤ value (ws 3) := by
      have not_less : ¬ value (ws 3) < value (ws 4) := by
        intro less
        apply selected
        simp [flag, less]
      omega
    obtain ⟨final, emitted, post, path, first, last, time, space⟩ :=
      exact_subtract L ws length same blank ordered input actual out pre.1
    exact ⟨final, emitted, by simpa only [reduceWords, selected, ↓reduceIte] using post,
      path, first, last, time, space⟩
  simpa [Exact, reduce, Nat.add_assoc] using BranchOnBit.transforms_common 5 copy subtract yes no

/-- Initial tape contract. Equal widths may include high zero padding; the
represented numbers, rather than the encodings' syntactic shapes, are residues. -/
structure Ready (L : ℕ) (ws : Words) : Prop where
  first_length : (ws 0).length = L
  second_length : (ws 1).length = L
  modulus_length : (ws 2).length = L
  modulus_positive : 0 < value (ws 2)
  first_small : value (ws 0) < value (ws 2)
  second_small : value (ws 1) < value (ws 2)
  sum_blank : ws 3 = []
  padded_blank : ws 4 = []
  flag_blank : ws 5 = []
  result_blank : ws 6 = []

private theorem exact_program (L : ℕ) (ws : Words) (ready : Ready L ws) :
    Exact machine ws (finalWords ws) (8 * L + 13) (10 * L + 43) := by
  have first := exact_add L ws ready.first_length.le
    (ready.first_length.trans ready.second_length.symm) ready.sum_blank
  have second := exact_pad L (addWords ws)
    (by simpa [addWords] using ready.modulus_length.le)
    (by simpa [addWords] using ready.padded_blank)
  have third := exact_compare (L + 1) (padWords (addWords ws))
    (by simp [padWords, addWords, AddRegistersMachine.sumBits_length, ready.first_length])
    (by simp [padWords, addWords, AddRegistersMachine.sumBits_length,
      ready.first_length, ready.modulus_length])
    (by simpa [padWords, addWords] using ready.flag_blank)
  have fourth := exact_reduce (L + 1) (compareWords (padWords (addWords ws)))
    (by simp [compareWords, padWords, addWords, AddRegistersMachine.sumBits_length,
      ready.first_length])
    (by simp [compareWords, padWords, addWords, AddRegistersMachine.sumBits_length,
      ready.first_length, ready.modulus_length])
    (by simpa [compareWords, padWords, addWords] using ready.result_blank)
    (by simp [compareWords])
  exact (exact_seq (exact_seq (exact_seq first second) third) fourth).mono
    (by omega) (by omega)

/-- The exact output word chooses either the unmodified sum or its difference
with the zero-padded modulus. This is a specification, not a host arithmetic
operation used by the machine. -/
theorem finalWords_result (ws : Words) (same : (ws 0).length = (ws 1).length) :
    finalWords ws 6 =
      if value (ws 0) + value (ws 1) < value (ws 2)
      then AddRegistersMachine.sumBits (ws 0) (ws 1)
      else SubtractRegistersMachine.differenceBits
        (AddRegistersMachine.sumBits (ws 0) (ws 1)) (PadRegisterMachine.paddedBits (ws 2)) := by
  simp [finalWords, reduceWords, compareWords, padWords, addWords,
    AddRegistersMachine.sumBits_value _ _ same]

theorem finalWords_value (L : ℕ) (ws : Words) (ready : Ready L ws) :
    value (finalWords ws 6) = (value (ws 0) + value (ws 1)) % value (ws 2) := by
  have same := ready.first_length.trans ready.second_length.symm
  have sum_value := AddRegistersMachine.sumBits_value (ws 0) (ws 1) same
  rw [finalWords_result ws same]
  by_cases small : value (ws 0) + value (ws 1) < value (ws 2)
  · simp only [small, ↓reduceIte, sum_value, Nat.mod_eq_of_lt small]
  · have ordered : value (ws 2) ≤ value (ws 0) + value (ws 1) := by omega
    have lengths : (AddRegistersMachine.sumBits (ws 0) (ws 1)).length =
        (PadRegisterMachine.paddedBits (ws 2)).length := by
      simp [AddRegistersMachine.sumBits_length, ready.first_length, ready.modulus_length]
    have ordered_words : value (PadRegisterMachine.paddedBits (ws 2)) ≤
        value (AddRegistersMachine.sumBits (ws 0) (ws 1)) := by
      simpa only [PadRegisterMachine.paddedBits_value, sum_value] using ordered
    rw [ite_eq_right small, SubtractRegistersMachine.differenceBits_value _ _ lengths ordered_words,
      sum_value, PadRegisterMachine.paddedBits_value, Nat.mod_eq_sub_mod ordered,
      Nat.mod_eq_of_lt (by have := ready.first_small; have := ready.second_small; omega)]

theorem finalWords_length (L : ℕ) (ws : Words) (ready : Ready L ws) :
    (finalWords ws 6).length ≤ L + 2 := by
  rw [finalWords_result ws (ready.first_length.trans ready.second_length.symm)]
  split <;> simp [AddRegistersMachine.sumBits_length,
    SubtractRegistersMachine.differenceBits_length, ready.first_length]

theorem finalWords_sources (ws : Words) (i : Fin 7) (source : i.val < 3) :
    finalWords ws i = ws i := by
  have ne3 : i ≠ 3 := by intro h; subst h; simp at source
  have ne4 : i ≠ 4 := by intro h; subst h; simp at source
  have ne5 : i ≠ 5 := by intro h; subst h; simp at source
  have ne6 : i ≠ 6 := by intro h; subst h; simp at source
  simp [finalWords, reduceWords, compareWords, padWords, addWords, ne3, ne4, ne5, ne6]

/-- One fixed finite-state seven-tape machine performs modular addition for
every width. All heads return to their initial positions, the original three
input words survive, and no output symbols are emitted. Its exact scratch
tuple is exposed for later cleanup/composition proofs. -/
theorem transforms_modularAdd (L : ℕ) :
    TransformsTapes machine (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => ws' = finalWords ws ∧
        value (ws' 6) = (value (ws 0) + value (ws 1)) % value (ws 2) ∧
        (ws' 6).length ≤ L + 2 ∧
        (∀ i : Fin 7, i.val < 3 → ws' i = ws i) ∧ emitted = [])
      (8 * L + 13) (10 * L + 43) := by
  intro input ws out ready
  obtain ⟨result, emitted, post, path, first, last, time, space⟩ :=
    exact_program L ws ready input ws out rfl
  refine ⟨result, emitted, ⟨post.1, ?_, ?_, ?_, post.2⟩,
    path, first, last, time, space⟩
  · rw [post.1]
    exact finalWords_value L ws ready
  · rw [post.1]
    exact finalWords_length L ws ready
  · rw [post.1]
    exact finalWords_sources ws

end NtimeDspace.ModularAddMachine
