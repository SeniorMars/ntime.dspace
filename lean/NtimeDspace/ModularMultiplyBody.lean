import NtimeDspace.CleanModularAddMachine
import NtimeDspace.ReplaceRegisterMachine
import NtimeDspace.DropFirstRegisterMachine
import NtimeDspace.ModularMultiplication

/-!
One actual eleven-tape double-and-add round. Tapes 0,1,2 preserve the original
inputs and modulus; tape 3 is the remaining little-endian driver, tape 4 the
current multiplicand and tape 5 the accumulator. Tapes 6 through 10 are blank
between rounds. The current multiplicand is copied before doubling, so every
placement into a previously checked macro is genuinely injective.
-/

namespace NtimeDspace.ModularMultiplyBody

open Turing Turing.MultiTapeTM BinaryCounterMachine

abbrev Words := Fin 11 → List Bool

def pairTapes (source target : Fin 11) (different : source ≠ target) : Fin 2 ↪ Fin 11 :=
  ⟨![source, target], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

@[simp] theorem pairTapes_zero (source target : Fin 11) (different : source ≠ target) :
    pairTapes source target different 0 = source := rfl

@[simp] theorem pairTapes_one (source target : Fin 11) (different : source ≠ target) :
    pairTapes source target different 1 = target := rfl

def accumulateTapes : Fin 7 ↪ Fin 11 :=
  ⟨![5, 4, 2, 6, 7, 8, 9], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def doubleTapes : Fin 7 ↪ Fin 11 :=
  ⟨![4, 10, 2, 6, 7, 8, 9], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

noncomputable def addInto (e : Fin 7 ↪ Fin 11) :=
  (CleanModularAddMachine.machine.extendTapes e).seq
    (ReplaceRegisterMachine.machine.extendTapes
      (pairTapes (e 6) (e 0) (fun h => by have := e.injective h; simp at this)))

noncomputable def accumulate := BranchOnBit.machine 3
  (addInto accumulateTapes) (nop 11 Bool)
noncomputable def duplicate := CopyRegisterMachine.machine.extendTapes (pairTapes 4 10 (by decide))
noncomputable def clearDuplicate := ClearRegisterMachine.machine.extendTapes (pairTapes 2 10 (by decide))
noncomputable def dropDriver := DropFirstRegisterMachine.machine.extendTapes (tapeEmb (3 : Fin 11))
noncomputable def doubleCurrent := (duplicate.seq (addInto doubleTapes)).seq clearDuplicate
noncomputable def machine :=
  (accumulate.seq doubleCurrent).seq dropDriver

/-- Each round starts with reduced, fixed-width arithmetic registers and no
live scratch word. The originals on tapes zero and one need no extra condition. -/
structure Ready (L : ℕ) (ws : Words) : Prop where
  modulus_length : (ws 2).length = L
  current_length : (ws 4).length = L
  accumulator_length : (ws 5).length = L
  modulus_positive : 0 < value (ws 2)
  current_small : value (ws 4) < value (ws 2)
  accumulator_small : value (ws 5) < value (ws 2)
  driver_length : (ws 3).length ≤ L
  scratch : ∀ i : Fin 11, 6 ≤ i.val → ws i = []

private theorem extended_clean_add (L : ℕ) (e : Fin 7 ↪ Fin 11) :
    TransformsTapes (CleanModularAddMachine.machine.extendTapes e)
      (fun _ ws => ModularAddMachine.Ready L (fun j => ws (e j)))
      (fun _ ws ws' emitted => ∃ result,
        result.length = L ∧ value result = (value (ws (e 0)) + value (ws (e 1))) % value (ws (e 2)) ∧
        ws' = Function.update ws (e 6) result ∧ emitted = [])
      (20 * L + 31) (22 * L + 107) := by
  apply (TapeEmbedding.transforms_extendTapes
    (CleanModularAddMachine.transforms_cleanModularAdd L) e).imp
  · exact fun _ _ pre => pre
  · intro _ ws ws' emitted ready post
    rcases post.1 with ⟨_, number, length, sources, scratch, output⟩
    refine ⟨ws' (e 6), length, number, ?_, output⟩
    funext i
    by_cases inside : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := inside
      have selected (j : Fin 7) (ne : j ≠ 6) : e j ≠ e 6 := fun h => ne (e.injective h)
      fin_cases j
      · simpa [Function.update_of_ne (selected 0 (by decide))] using sources 0 (by decide)
      · simpa [Function.update_of_ne (selected 1 (by decide))] using sources 1 (by decide)
      · simpa [Function.update_of_ne (selected 2 (by decide))] using sources 2 (by decide)
      · simpa [Function.update_of_ne (selected 3 (by decide)), ready.sum_blank] using
          scratch 3 (by decide)
      · simpa [Function.update_of_ne (selected 4 (by decide)), ready.padded_blank] using
          scratch 4 (by decide)
      · simpa [Function.update_of_ne (selected 5 (by decide)), ready.flag_blank] using
          scratch 5 (by decide)
      · simp
    · have ne : i ≠ e 6 := by intro h; exact inside ⟨6, h.symm⟩
      simpa [Function.update_of_ne ne] using post.2 i inside
  · exact le_rfl
  · omega

private theorem extended_replace (L : ℕ) (source target : Fin 11) (different : source ≠ target) :
    TransformsTapes
      (ReplaceRegisterMachine.machine.extendTapes (pairTapes source target different))
      (fun _ ws => (ws source).length ≤ L ∧ (ws target).length ≤ (ws source).length)
      (fun _ ws ws' emitted =>
        ws' = Function.update (Function.update ws source []) target (ws source) ∧ emitted = [])
      (6 * L + 6) (6 * L + 21) := by
  apply (TapeEmbedding.transforms_extendTapes
    (ReplaceRegisterMachine.transforms_replace L) (pairTapes source target different)).imp
  · exact fun _ _ pre => pre
  · intro _ ws ws' emitted _ post
    rcases post.1 with ⟨cleared, copied, output⟩
    refine ⟨?_, output⟩
    funext i
    by_cases is_source : i = source
    · subst i
      simpa [Function.update_of_ne different] using cleared
    · by_cases is_target : i = target
      · subst i
        simpa [pairTapes_zero, pairTapes_one] using copied
      · have outside : i ∉ Set.range (pairTapes source target different) := by
          rintro ⟨j, rfl⟩
          fin_cases j <;> simp_all [pairTapes_zero, pairTapes_one]
        simpa [Function.update_of_ne is_source, Function.update_of_ne is_target] using post.2 i outside
  · exact le_rfl
  · omega

/-- Add the two selected source residues, replace the first one, and release
the temporary result tape. All other words are exactly preserved. -/
private theorem transforms_addInto (L : ℕ) (e : Fin 7 ↪ Fin 11) :
    TransformsTapes (addInto e)
      (fun _ ws => ModularAddMachine.Ready L (fun j => ws (e j)))
      (fun _ ws ws' emitted => ∃ result,
        result.length = L ∧ value result = (value (ws (e 0)) + value (ws (e 1))) % value (ws (e 2)) ∧
        ws' = Function.update ws (e 0) result ∧ emitted = [])
      (26 * L + 37) (28 * L + 128) := by
  have different : e 6 ≠ e 0 := fun h => by have := e.injective h; simp at this
  have composed := transformsTapes_seq (extended_clean_add L e)
    (extended_replace L (e 6) (e 0) different) (by
      rintro _ ws ws' _ ready ⟨result, length, _, rfl, _⟩
      simp [length, ready.first_length])
  apply composed.imp (fun _ _ pre => pre)
  · rintro _ ws ws' _ ready ⟨middle, e₀, e₁, ⟨result, length, number, rfl, empty₀⟩,
      ⟨rfl, empty₁⟩, rfl⟩
    refine ⟨result, length, number, ?_, by simp [empty₀, empty₁]⟩
    simp only [Function.update_self, Function.update_idem]
    have restore : Function.update ws (e 6) [] = ws := by
      rw [← ready.result_blank]
      exact Function.update_eq_self _ _
    rw [restore]
  · omega
  · omega

private theorem extended_copy (L : ℕ) (source target : Fin 11) (different : source ≠ target) :
    TransformsTapes (CopyRegisterMachine.machine.extendTapes (pairTapes source target different))
      (fun _ ws => (ws source).length ≤ L ∧ ws target = [])
      (fun _ ws ws' emitted => ws' = Function.update ws target (ws source) ∧ emitted = [])
      (2 * L + 2) (2 * L + 13) := by
  apply (TapeEmbedding.transforms_extendTapes
    (CopyRegisterMachine.transforms_copy L) (pairTapes source target different)).imp
  · exact fun _ _ pre => pre
  · intro _ ws ws' emitted _ post
    rcases post.1 with ⟨preserved, copied, output⟩
    refine ⟨?_, output⟩
    funext i
    by_cases is_source : i = source
    · subst i
      simpa [Function.update_of_ne different] using preserved
    · by_cases is_target : i = target
      · subst i
        simpa using copied
      · have outside : i ∉ Set.range (pairTapes source target different) := by
          rintro ⟨j, rfl⟩
          fin_cases j <;> simp_all
        simpa [Function.update_of_ne is_target] using post.2 i outside
  · exact le_rfl
  · omega

private theorem extended_clear (L : ℕ) (source target : Fin 11) (different : source ≠ target) :
    TransformsTapes (ClearRegisterMachine.machine.extendTapes (pairTapes source target different))
      (fun _ ws => (ws source).length ≤ L ∧ (ws target).length ≤ (ws source).length)
      (fun _ ws ws' emitted => ws' = Function.update ws target [] ∧ emitted = [])
      (2 * L + 2) (2 * L + 13) := by
  apply (TapeEmbedding.transforms_extendTapes
    (ClearRegisterMachine.transforms_clear L) (pairTapes source target different)).imp
  · exact fun _ _ pre => pre
  · intro _ ws ws' emitted _ post
    rcases post.1 with ⟨preserved, cleared, output⟩
    refine ⟨?_, output⟩
    funext i
    by_cases is_source : i = source
    · subst i
      simpa [Function.update_of_ne different] using preserved
    · by_cases is_target : i = target
      · subst i
        simpa using cleared
      · have outside : i ∉ Set.range (pairTapes source target different) := by
          rintro ⟨j, rfl⟩
          fin_cases j <;> simp_all
        simpa [Function.update_of_ne is_target] using post.2 i outside
  · exact le_rfl
  · omega

private theorem ready_accumulate_project (L : ℕ) (ws : Words) (ready : Ready L ws) :
    ModularAddMachine.Ready L (fun j => ws (accumulateTapes j)) where
  first_length := ready.accumulator_length
  second_length := ready.current_length
  modulus_length := ready.modulus_length
  modulus_positive := ready.modulus_positive
  first_small := ready.accumulator_small
  second_small := ready.current_small
  sum_blank := ready.scratch 6 (by decide)
  padded_blank := ready.scratch 7 (by decide)
  flag_blank := ready.scratch 8 (by decide)
  result_blank := ready.scratch 9 (by decide)

private theorem transforms_accumulate (L : ℕ) :
    TransformsTapes accumulate (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => ∃ result,
        result.length = L ∧
        value result = ModularMultiplication.addBit (value (ws 2)) ((ws 3).head?.getD false)
          (value (ws 4)) (value (ws 5)) ∧
        ws' = Function.update ws 5 result ∧ emitted = [])
      (26 * L + 38) (28 * L + 128) := by
  have yes : TransformsTapes (addInto accumulateTapes)
      (fun _ ws => Ready L ws ∧ (ws 3).head? = some true)
      (fun _ ws ws' emitted => ∃ result,
        result.length = L ∧
        value result = ModularMultiplication.addBit (value (ws 2)) ((ws 3).head?.getD false)
          (value (ws 4)) (value (ws 5)) ∧
        ws' = Function.update ws 5 result ∧ emitted = [])
      (26 * L + 37) (28 * L + 128) := by
    apply (transforms_addInto L accumulateTapes).imp
    · exact fun _ ws pre => ready_accumulate_project L ws pre.1
    · rintro _ ws ws' emitted pre ⟨result, length, number, final, output⟩
      refine ⟨result, length, ?_, final, output⟩
      change value result = (value (ws 5) + value (ws 4)) % value (ws 2) at number
      simpa only [pre.2, Option.getD_some, ModularMultiplication.addBit, ↓reduceIte] using number
    · exact le_rfl
    · exact le_rfl
  have no : TransformsTapes (nop 11 Bool)
      (fun _ ws => Ready L ws ∧ (ws 3).head? ≠ some true)
      (fun _ ws ws' emitted => ∃ result,
        result.length = L ∧
        value result = ModularMultiplication.addBit (value (ws 2)) ((ws 3).head?.getD false)
          (value (ws 4)) (value (ws 5)) ∧
        ws' = Function.update ws 5 result ∧ emitted = [])
      (26 * L + 37) (28 * L + 128) := by
    apply (transformsTapes_nop 11 Bool).imp (fun _ _ _ => True.intro)
    · intro _ ws ws' emitted pre post
      rcases post with ⟨identity, output⟩
      subst ws'
      have bit_false : (ws 3).head?.getD false = false := by
        cases head : (ws 3).head? with
        | none => rfl
        | some bit => cases bit <;> simp_all
      refine ⟨ws 5, pre.1.accumulator_length, ?_, (Function.update_eq_self 5 ws).symm, output⟩
      simp [bit_false, ModularMultiplication.addBit, Nat.mod_eq_of_lt pre.1.accumulator_small]
    · omega
    · omega
  simpa [accumulate, Nat.add_assoc] using BranchOnBit.transforms_common 3 _ _ yes no

private theorem ready_double_project (L : ℕ) (ws : Words) (ready : Ready L ws) :
    ModularAddMachine.Ready L (fun j => (Function.update ws 10 (ws 4)) (doubleTapes j)) := by
  have projection : (fun j => (Function.update ws 10 (ws 4)) (doubleTapes j)) =
      ![ws 4, ws 4, ws 2, ws 6, ws 7, ws 8, ws 9] := by
    funext j
    fin_cases j <;> rfl
  rw [projection]
  exact ⟨ready.current_length, ready.current_length, ready.modulus_length,
    ready.modulus_positive, ready.current_small, ready.current_small,
    ready.scratch 6 (by decide), ready.scratch 7 (by decide),
    ready.scratch 8 (by decide), ready.scratch 9 (by decide)⟩

private theorem transforms_double (L : ℕ) :
    TransformsTapes doubleCurrent (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => ∃ result,
        result.length = L ∧ value result = ModularMultiplication.double (value (ws 2)) (value (ws 4)) ∧
        ws' = Function.update ws 4 result ∧ emitted = [])
      (30 * L + 41) (32 * L + 154) := by
  have copied : TransformsTapes duplicate (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => ws' = Function.update ws 10 (ws 4) ∧ emitted = [])
      (2 * L + 2) (2 * L + 13) := by
    apply (extended_copy L 4 10 (by decide)).imp
    · exact fun _ ws pre => ⟨pre.current_length.le, pre.scratch 10 (by decide)⟩
    · exact fun _ _ _ _ _ post => post
    · exact le_rfl
    · exact le_rfl
  have added := transformsTapes_seq copied (transforms_addInto L doubleTapes)
    (by
      intro _ ws ws' _ ready post
      rw [post.1]
      exact ready_double_project L ws ready)
  have composed := transformsTapes_seq added (extended_clear L 2 10 (by decide))
    (by
      rintro _ ws ws' _ ready ⟨middle, _, _, ⟨rfl, _⟩, ⟨result, _, _, final, _⟩, _⟩
      change ws' = Function.update (Function.update ws 10 (ws 4)) 4 result at final
      rw [final]
      simp [ready.current_length, ready.modulus_length])
  apply composed.imp (fun _ _ pre => pre)
  · rintro _ ws ws' _ ready ⟨afterAdd, e₀, e₁,
      ⟨afterCopy, e₂, e₃, ⟨copy_eq, empty₂⟩, ⟨result, length, number, add_eq, empty₃⟩, output₀⟩,
      ⟨clear_eq, empty₁⟩, rfl⟩
    have number' : value result = ModularMultiplication.double (value (ws 2)) (value (ws 4)) := by
      rw [copy_eq] at number
      change value result =
        (value ((Function.update ws 10 (ws 4)) 4) + value ((Function.update ws 10 (ws 4)) 10)) %
          value ((Function.update ws 10 (ws 4)) 2) at number
      simpa [ModularMultiplication.double] using number
    refine ⟨result, length, number', ?_, by simp [output₀, empty₁, empty₂, empty₃]⟩
    rw [clear_eq, add_eq, copy_eq]
    change Function.update (Function.update (Function.update ws 10 (ws 4)) 4 result) 10 [] = _
    funext i
    by_cases current : i = 4
    · subst i
      simp
    · by_cases temporary : i = 10
      · subst i
        simp [ready.scratch 10 (by decide)]
      · simp [Function.update_of_ne current, Function.update_of_ne temporary]
  · omega
  · omega

private theorem ready_update_accumulator (L : ℕ) (ws : Words) (ready : Ready L ws)
    (result : List Bool) (length : result.length = L) (small : value result < value (ws 2)) :
    Ready L (Function.update ws 5 result) where
  modulus_length := by simpa using ready.modulus_length
  current_length := by simpa using ready.current_length
  accumulator_length := by simpa using length
  modulus_positive := by simpa using ready.modulus_positive
  current_small := by simpa using ready.current_small
  accumulator_small := by simpa using small
  driver_length := by simpa using ready.driver_length
  scratch := by
    intro i hi
    have different : i ≠ 5 := by intro h; subst i; simp at hi
    simpa [Function.update_of_ne different] using ready.scratch i hi

private theorem ready_update_current (L : ℕ) (ws : Words) (ready : Ready L ws)
    (result : List Bool) (length : result.length = L) (small : value result < value (ws 2)) :
    Ready L (Function.update ws 4 result) where
  modulus_length := by simpa using ready.modulus_length
  current_length := by simpa using length
  accumulator_length := by simpa using ready.accumulator_length
  modulus_positive := by simpa using ready.modulus_positive
  current_small := by simpa using small
  accumulator_small := by simpa using ready.accumulator_small
  driver_length := by simpa using ready.driver_length
  scratch := by
    intro i hi
    have different : i ≠ 4 := by intro h; subst i; simp at hi
    simpa [Function.update_of_ne different] using ready.scratch i hi

private theorem ready_drop_driver (L : ℕ) (ws : Words) (ready : Ready L ws) :
    Ready L (Function.update ws 3 (ws 3).tail) where
  modulus_length := by simpa using ready.modulus_length
  current_length := by simpa using ready.current_length
  accumulator_length := by simpa using ready.accumulator_length
  modulus_positive := by simpa using ready.modulus_positive
  current_small := by simpa using ready.current_small
  accumulator_small := by simpa using ready.accumulator_small
  driver_length := by simpa using (Nat.sub_le (ws 3).length 1).trans ready.driver_length
  scratch := by
    intro i hi
    have different : i ≠ 3 := by intro h; subst i; simp at hi
    simpa [Function.update_of_ne different] using ready.scratch i hi

private theorem transforms_drop (L : ℕ) :
    TransformsTapes dropDriver (fun _ ws => (ws 3).length ≤ L)
      (fun _ ws ws' emitted => ws' = Function.update ws 3 (ws 3).tail ∧ emitted = [])
      (4 * L + 1) (4 * L + 12) := by
  apply ((DropFirstRegisterMachine.transforms_drop L).tapeEmb (3 : Fin 11)).imp
  · exact fun _ _ pre => pre
  · rintro _ ws ws' emitted _ ⟨result, post, final⟩
    exact ⟨by simpa only [post.1] using final, post.2.2.2⟩
  · exact le_rfl
  · omega

/-- The complete arithmetic round. The driver may be empty: its false branch
then leaves the reduced accumulator unchanged, while doubling the irrelevant
current register still preserves the modular loop invariant. -/
theorem transforms_body (L : ℕ) :
    TransformsTapes machine (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => Ready L ws' ∧
        (∀ i : Fin 11, i.val < 3 → ws' i = ws i) ∧
        ws' 3 = (ws 3).tail ∧
        value (ws' 4) = ModularMultiplication.double (value (ws 2)) (value (ws 4)) ∧
        value (ws' 5) = ModularMultiplication.addBit (value (ws 2)) ((ws 3).head?.getD false)
          (value (ws 4)) (value (ws 5)) ∧ emitted = [])
      (60 * L + 80) (64 * L + 294) := by
  have accumulate_ready : TransformsTapes accumulate (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => Ready L ws' ∧ ∃ result,
        result.length = L ∧
        value result = ModularMultiplication.addBit (value (ws 2)) ((ws 3).head?.getD false)
          (value (ws 4)) (value (ws 5)) ∧
        ws' = Function.update ws 5 result ∧ emitted = [])
      (26 * L + 38) (28 * L + 128) := by
    apply (transforms_accumulate L).imp (fun _ _ pre => pre)
    · intro _ ws ws' emitted ready post
      obtain ⟨result, length, number, final, output⟩ := post
      refine ⟨?_, result, length, number, final, output⟩
      rw [final]
      apply ready_update_accumulator L ws ready result length
      rw [number]
      exact ModularMultiplication.addBit_lt _ ready.modulus_positive _ _ _
    · exact le_rfl
    · exact le_rfl
  have double_ready : TransformsTapes doubleCurrent (fun _ ws => Ready L ws)
      (fun _ ws ws' emitted => Ready L ws' ∧ ∃ result,
        result.length = L ∧ value result = ModularMultiplication.double (value (ws 2)) (value (ws 4)) ∧
        ws' = Function.update ws 4 result ∧ emitted = [])
      (30 * L + 41) (32 * L + 154) := by
    apply (transforms_double L).imp (fun _ _ pre => pre)
    · intro _ ws ws' emitted ready post
      obtain ⟨result, length, number, final, output⟩ := post
      refine ⟨?_, result, length, number, final, output⟩
      rw [final]
      apply ready_update_current L ws ready result length
      rw [number]
      exact ModularMultiplication.double_lt _ ready.modulus_positive _
    · exact le_rfl
    · exact le_rfl
  have arithmetic := transformsTapes_seq accumulate_ready double_ready
    (fun _ _ _ _ _ post => post.1)
  have composed := transformsTapes_seq arithmetic (transforms_drop L)
    (by rintro _ _ _ _ _ ⟨_, _, _, _, post, _⟩; exact post.1.driver_length)
  apply composed.imp (fun _ _ pre => pre)
  · rintro _ ws ws' _ _ ⟨afterArithmetic, e₀, e₁,
      ⟨afterAcc, e₂, e₃, ⟨_, acc, _, acc_value, acc_eq, empty₂⟩,
        ⟨after_ready, current, _, current_value, current_eq, empty₃⟩, output₀⟩,
      ⟨drop_eq, empty₁⟩, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp [output₀, empty₁, empty₂, empty₃]⟩
    · rw [drop_eq]
      exact ready_drop_driver L afterArithmetic after_ready
    · intro i hi
      have ne3 : i ≠ 3 := by intro h; subst i; simp at hi
      have ne4 : i ≠ 4 := by intro h; subst i; simp at hi
      have ne5 : i ≠ 5 := by intro h; subst i; simp at hi
      simp [drop_eq, current_eq, acc_eq, Function.update_of_ne ne3,
        Function.update_of_ne ne4, Function.update_of_ne ne5]
    · simp [drop_eq, current_eq, acc_eq]
    · simpa [drop_eq, current_eq, acc_eq] using current_value
    · simpa [drop_eq, current_eq, acc_eq] using acc_value
  · omega
  · omega

end NtimeDspace.ModularMultiplyBody
