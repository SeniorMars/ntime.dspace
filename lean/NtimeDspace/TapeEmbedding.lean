import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

/-!
Placement of a tape-transforming machine on any injectively selected work tapes.
The unchanged tapes retain their words and head positions. Starting from the
standard word configuration, each extra tape contributes its one stationary
visited cell. Time is unchanged. No assumption about the contents of the extra
tapes, and no additional submachine cost hypothesis, is needed.
-/

namespace NtimeDspace.TapeEmbedding

open Turing Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*}

/-- Replace exactly the selected words by the submachine's final words. This
is a specification of the tape contents, not a buffer in the machine. -/
def placeWords (e : Fin k ↪ Fin k') (original : Fin k' → List Symbol)
    (result : Fin k → List Symbol) : Fin k' → List Symbol :=
  fun l => match partialInv e l with
    | some j => result j
    | none => original l

@[simp] theorem placeWords_selected (e : Fin k ↪ Fin k')
    (original : Fin k' → List Symbol) (result : Fin k → List Symbol) (j : Fin k) :
    placeWords e original result (e j) = result j := by
  simp [placeWords]

theorem placeWords_unselected (e : Fin k ↪ Fin k')
    (original : Fin k' → List Symbol) (result : Fin k → List Symbol)
    (l : Fin k') (outside : l ∉ Set.range e) :
    placeWords e original result l = original l := by
  simp [placeWords, partialInv_eq_none e outside]

@[simp] theorem placeWords_project (e : Fin k ↪ Fin k')
    (original : Fin k' → List Symbol) :
    placeWords e original (fun j => original (e j)) = original := by
  funext l
  dsimp [placeWords]
  cases inverse : partialInv e l with
  | none => rfl
  | some j =>
      exact congrArg original (partialInv_eq_some e inverse)

theorem embed_wordsCfg (e : Fin k ↪ Fin k') (input : List Symbol)
    (state : Option State) (original : Fin k' → List Symbol)
    (result : Fin k → List Symbol) (out : List Symbol) :
    embed e (wordsCfg input state result out) (fun l => tapeOfList (original l))
        (fun _ => 0) = wordsCfg input state (placeWords e original result) out := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext l
    simp only [embed, wordsCfg, placeWords]
    cases partialInv e l <;> rfl
  · funext l
    simp only [embed, wordsCfg]
    cases partialInv e l <;> rfl
  · rfl

/-- Generic placement of a tape transformer. Its complete output tuple is
inserted into the selected tapes and all other words are kept. All heads reset
by the `TransformsTapes` normal form; emitted output is passed through exactly.
The extra tapes contribute one visited cell each, independently of their words. -/
theorem transforms_place {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapes tm P Q t s) (e : Fin k ↪ Fin k') :
    TransformsTapes (tm.extendTapes e)
      (fun input ws => P input (fun j => ws (e j)))
      (fun input ws ws' emitted => ∃ result,
        Q input (fun j => ws (e j)) result emitted ∧ ws' = placeWords e ws result)
      t (s + (k' - k)) := by
  intro input ws out pre
  obtain ⟨result, emitted, post, path, initial, final, time, space⟩ :=
    h input (fun j => ws (e j)) out pre
  refine ⟨placeWords e ws result, emitted, ⟨result, post, rfl⟩,
    path.map (embedHom tm e (fun l => tapeOfList (ws l)) (fun _ => 0)),
    ?_, ?_, time, ?_⟩
  · simp only [RelSeries.head_map, initial, embedHom_apply, embed_wordsCfg,
      placeWords_project]
    rfl
  · simp only [RelSeries.last_map, final, embedHom_apply, embed_wordsCfg]
  · exact (space_map_embedHom_le tm e _ _ path).trans (Nat.add_le_add_right space _)

/-- The same contract directly on the projected final words: the original
postcondition holds on selected tapes, and every unselected word is preserved.
The theorem applies to tape permutations as well as embeddings into more tapes. -/
theorem transforms_extendTapes {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapes tm P Q t s) (e : Fin k ↪ Fin k') :
    TransformsTapes (tm.extendTapes e)
      (fun input ws => P input (fun j => ws (e j)))
      (fun input ws ws' emitted =>
        Q input (fun j => ws (e j)) (fun j => ws' (e j)) emitted ∧
        ∀ l, l ∉ Set.range e → ws' l = ws l)
      t (s + (k' - k)) := by
  apply (transforms_place h e).imp (fun _ _ pre => pre)
  · intro input ws ws' emitted pre post
    obtain ⟨result, post, rfl⟩ := post
    constructor
    · simpa only [placeWords_selected] using post
    · exact fun l outside => placeWords_unselected e ws result l outside
  · exact le_rfl
  · exact le_rfl

end NtimeDspace.TapeEmbedding
