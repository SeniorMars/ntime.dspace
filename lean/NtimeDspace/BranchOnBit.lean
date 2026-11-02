import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
A conditional on one work-tape bit, in the actual CSLib multitape model.
The first step reads the flag and changes only the finite control. The selected
machine then runs on the original tapes and head positions. The decision step
adds one step and no visited cells. As with CSLib's sequential composition,
the transition accessor is noncomputable; compilation of that accessor is a
separate obligation from this machine-semantic theorem.
-/

namespace NtimeDspace.BranchOnBit

open Turing Turing.MultiTapeTM

variable {k : ℕ} {StateTrue StateFalse : Type*} {input : List Bool}

abbrev State (StateTrue StateFalse : Type*) := Unit ⊕ (StateTrue ⊕ StateFalse)

/-- Read `flag` once. Only `some true` selects the first branch; both a blank
and `some false` select the second branch. -/
noncomputable def machine (flag : Fin k)
    (yes : MultiTapeTM k Bool StateTrue) (no : MultiTapeTM k Bool StateFalse) :
    MultiTapeTM k Bool (State StateTrue StateFalse) :=
  .ofTr (.inl ()) fun state inp work =>
    match state with
    | .inl _ =>
        ⟨0, fun _ => (none, 0), none,
          some (if work flag = some true then .inr (.inl yes.q₀) else .inr (.inr no.q₀))⟩
    | .inr (.inl q) =>
        let action := yes.tr q inp work
        { action with state := action.state.map (fun q => .inr (.inl q)) }
    | .inr (.inr q) =>
        let action := no.tr q inp work
        { action with state := action.state.map (fun q => .inr (.inr q)) }

def trueCfg (cfg : Cfg k Bool StateTrue input) : Cfg k Bool (State StateTrue StateFalse) input :=
  cfg.mapState (Option.map fun q => .inr (.inl q))

def falseCfg (cfg : Cfg k Bool StateFalse input) : Cfg k Bool (State StateTrue StateFalse) input :=
  cfg.mapState (Option.map fun q => .inr (.inr q))

theorem step_trueCfg (flag : Fin k) (yes : MultiTapeTM k Bool StateTrue)
    (no : MultiTapeTM k Bool StateFalse) (cfg : Cfg k Bool StateTrue input) :
    (machine flag yes no).step (trueCfg cfg) = trueCfg (yes.step cfg) := by
  cases state_eq : cfg.state with
  | none =>
      rw [step_of_halt (by simp [trueCfg, Cfg.mapState, state_eq]), step_of_halt state_eq]
  | some state =>
      rw [step_of_state (show (trueCfg (StateFalse := StateFalse) cfg).state =
          some (.inr (.inl state)) by simp [trueCfg, Cfg.mapState, state_eq]),
        step_of_state state_eq]
      simp only [machine, tr_ofTr]
      rfl

theorem step_falseCfg (flag : Fin k) (yes : MultiTapeTM k Bool StateTrue)
    (no : MultiTapeTM k Bool StateFalse) (cfg : Cfg k Bool StateFalse input) :
    (machine flag yes no).step (falseCfg cfg) = falseCfg (no.step cfg) := by
  cases state_eq : cfg.state with
  | none =>
      rw [step_of_halt (by simp [falseCfg, Cfg.mapState, state_eq]), step_of_halt state_eq]
  | some state =>
      rw [step_of_state (show (falseCfg (StateTrue := StateTrue) cfg).state =
          some (.inr (.inr state)) by simp [falseCfg, Cfg.mapState, state_eq]),
        step_of_state state_eq]
      simp only [machine, tr_ofTr]
      rfl

theorem step_decide_true (flag : Fin k) (yes : MultiTapeTM k Bool StateTrue)
    (no : MultiTapeTM k Bool StateFalse) (ws : Fin k → List Bool) (out : List Bool)
    (selected : (ws flag).head? = some true) :
    (machine flag yes no).step (wordsCfg input (some (.inl ())) ws out) =
      trueCfg (wordsCfg input (some yes.q₀) ws out) := by
  rw [List.head?_eq_getElem?] at selected
  rw [step_of_state rfl]
  simp [machine, Action.apply, wordsCfg, trueCfg, Cfg.mapState, Cfg.workTapeSymbols,
    tapeOfList, selected]

theorem step_decide_false (flag : Fin k) (yes : MultiTapeTM k Bool StateTrue)
    (no : MultiTapeTM k Bool StateFalse) (ws : Fin k → List Bool) (out : List Bool)
    (selected : (ws flag).head? ≠ some true) :
    (machine flag yes no).step (wordsCfg input (some (.inl ())) ws out) =
      falseCfg (wordsCfg input (some no.q₀) ws out) := by
  rw [List.head?_eq_getElem?] at selected
  rw [step_of_state rfl]
  simp [machine, Action.apply, wordsCfg, falseCfg, Cfg.mapState, Cfg.workTapeSymbols,
    tapeOfList, selected]

/-- A stationary decision can be prepended to a state-only simulation without
adding any work cell: its positions are exactly the branch path's first ones. -/
private theorem prepend_decision {Source Target : Type*}
    (source : MultiTapeTM k Bool Source) (target : MultiTapeTM k Bool Target)
    (embed : Source → Target)
    (commutes : ∀ cfg : Cfg k Bool Source input,
      target.step (cfg.mapState (Option.map embed)) =
        (source.step cfg).mapState (Option.map embed))
    (path : source.RunPath input) (begin : Cfg k Bool Target input)
    (decision : target.step begin = path.head.mapState (Option.map embed))
    (positions : begin.workTapePos = path.head.workTapePos) :
    ∃ result : target.RunPath input,
      result.head = begin ∧ result.last = path.last.mapState (Option.map embed) ∧
      result.length = path.length + 1 ∧ result.space ≤ path.space := by
  let hom := stepHom (tm := source) (tm' := target)
    (fun cfg => cfg.mapState (Option.map embed)) (fun cfg => (commutes cfg).symm)
  let mapped := path.map hom
  have follows : (begin, mapped.head) ∈ target.stepRel input := by
    apply step_iff.mpr
    exact decision
  let result : target.RunPath input := mapped.cons begin follows
  refine ⟨result, rfl, by simp only [result, RelSeries.last_cons, mapped, RelSeries.last_map]; rfl,
    by simp [result, mapped], ?_⟩
  apply result.space_le_sum_card (S := fun i => path.visitedByTapeHead i)
  intro cfg membership i
  have member : cfg = begin ∨ cfg ∈ mapped := by
    change cfg ∈ mapped.cons begin follows at membership
    have := RelSeries.mem_toList.mpr membership
    simpa only [RelSeries.toList_cons, List.mem_cons, RelSeries.mem_toList] using this
  rcases member with rfl | member
  · apply path.mem_visitedByTapeHead.mpr
    exact ⟨path.head, RelSeries.head_mem path, congrFun positions.symm i⟩
  · obtain ⟨original, original_mem, rfl⟩ := RelSeries.exists_of_mem_map member
    exact path.mem_visitedByTapeHead.mpr ⟨original, original_mem, rfl⟩

/-- Branch specifications split on the *initial* flag. No restriction is
imposed on whether the chosen machine later overwrites that flag. Each branch
starts in its own initial state, on the unchanged initial tape words. -/
theorem transforms_branch (flag : Fin k)
    (yes : MultiTapeTM k Bool StateTrue) (no : MultiTapeTM k Bool StateFalse)
    {P : List Bool → (Fin k → List Bool) → Prop}
    {QTrue QFalse : List Bool → (Fin k → List Bool) → (Fin k → List Bool) →
      List Bool → Prop}
    {tTrue sTrue tFalse sFalse : ℕ}
    (yes_spec : TransformsTapes yes
      (fun input ws => P input ws ∧ (ws flag).head? = some true) QTrue tTrue sTrue)
    (no_spec : TransformsTapes no
      (fun input ws => P input ws ∧ (ws flag).head? ≠ some true) QFalse tFalse sFalse) :
    TransformsTapes (machine flag yes no) P
      (fun input ws ws' emitted =>
        if (ws flag).head? = some true then QTrue input ws ws' emitted
        else QFalse input ws ws' emitted)
      (max tTrue tFalse + 1) (max sTrue sFalse) := by
  intro input ws out precondition
  let begin := wordsCfg input (some (machine flag yes no).q₀) ws out
  by_cases selected : (ws flag).head? = some true
  · obtain ⟨ws', emitted, post, path, first, last, time, space⟩ :=
      yes_spec input ws out ⟨precondition, selected⟩
    obtain ⟨result, result_first, result_last, result_length, result_space⟩ :=
      prepend_decision yes (machine flag yes no) (fun state => .inr (.inl state))
        (step_trueCfg flag yes no) path begin
        (by rw [first]; exact step_decide_true flag yes no ws out selected)
        (by rw [first]; rfl)
    refine ⟨ws', emitted, by simpa only [selected, ↓reduceIte] using post,
      result, result_first, ?_, ?_, ?_⟩
    · rw [result_last, last]
      rfl
    · change result.length ≤ max tTrue tFalse + 1
      rw [result_length]
      exact Nat.add_le_add_right (time.trans (le_max_left _ _)) 1
    · exact result_space.trans (space.trans (le_max_left _ _))
  · obtain ⟨ws', emitted, post, path, first, last, time, space⟩ :=
      no_spec input ws out ⟨precondition, selected⟩
    obtain ⟨result, result_first, result_last, result_length, result_space⟩ :=
      prepend_decision no (machine flag yes no) (fun state => .inr (.inr state))
        (step_falseCfg flag yes no) path begin
        (by rw [first]; exact step_decide_false flag yes no ws out selected)
        (by rw [first]; rfl)
    refine ⟨ws', emitted, by simpa only [selected, ↓reduceIte] using post,
      result, result_first, ?_, ?_, ?_⟩
    · rw [result_last, last]
      rfl
    · change result.length ≤ max tTrue tFalse + 1
      rw [result_length]
      exact Nat.add_le_add_right (time.trans (le_max_right _ _)) 1
    · exact result_space.trans (space.trans (le_max_right _ _))

/-- A common postcondition can be proved independently on the two initial flag
cases. The time is the larger branch time plus the one decision step, while
the space is just the larger branch space. -/
theorem transforms_common (flag : Fin k)
    (yes : MultiTapeTM k Bool StateTrue) (no : MultiTapeTM k Bool StateFalse)
    {P : List Bool → (Fin k → List Bool) → Prop}
    {Q : List Bool → (Fin k → List Bool) → (Fin k → List Bool) → List Bool → Prop}
    {tTrue sTrue tFalse sFalse : ℕ}
    (yes_spec : TransformsTapes yes
      (fun input ws => P input ws ∧ (ws flag).head? = some true) Q tTrue sTrue)
    (no_spec : TransformsTapes no
      (fun input ws => P input ws ∧ (ws flag).head? ≠ some true) Q tFalse sFalse) :
    TransformsTapes (machine flag yes no) P Q
      (max tTrue tFalse + 1) (max sTrue sFalse) := by
  simpa only [ite_self] using transforms_branch flag yes no yes_spec no_spec

end NtimeDspace.BranchOnBit
