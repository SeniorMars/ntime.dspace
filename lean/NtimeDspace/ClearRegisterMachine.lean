import NtimeDspace.CopyRegisterMachine

/-!
A fixed two-state, two-work-tape register-clearing machine. The source word
marks the permitted destination extent. One forward scan clears those cells;
a reverse scan returns both heads to zero. The source, input, and output are
preserved. The destination may contain any word no longer than the source.
-/

namespace NtimeDspace.ClearRegisterMachine

open Turing Turing.MultiTapeTM

/-- `false` clears right; `true` rewinds left. The two states contain no word,
length, or position. The source is read without alteration. -/
def machine : MultiTapeTM 2 Bool Bool :=
  .ofTr false fun rewinding _ work =>
    if rewinding then
      match work 0 with
      | some _ => ⟨0, fun _ => (none, -1), none, some true⟩
      | none => ⟨0, fun _ => (none, 1), none, none⟩
    else
      match work 0 with
      | some _ =>
          ⟨0, fun i => (if i = 0 then none else some none, 1), none, some false⟩
      | none => ⟨0, fun _ => (none, -1), none, some true⟩

variable {input : List Bool}

def cfg (state : Option Bool) (ip : Fin (input.length + 2))
    (source destination : ℤ → Option Bool) (head : ℤ) (out : List Bool) :
    Cfg 2 Bool Bool input :=
  ⟨state, ip, fun i => if i = 0 then source else destination, fun _ => head, out⟩

theorem step_clear (ip : Fin (input.length + 2)) (source destination : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) (read : source head = some bit) :
    machine.step (cfg (some false) ip source destination head out) =
      cfg (some false) ip source (Function.update destination head none) (head + 1) out := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]
  · funext i
    simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]

theorem step_frontier (ip : Fin (input.length + 2)) (source destination : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (read : source head = none) :
    machine.step (cfg (some false) ip source destination head out) =
      cfg (some true) ip source destination (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read, sub_eq_add_neg]

theorem step_rewind (ip : Fin (input.length + 2)) (source destination : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) (read : source head = some bit) :
    machine.step (cfg (some true) ip source destination head out) =
      cfg (some true) ip source destination (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read, sub_eq_add_neg]

theorem step_delimiter (ip : Fin (input.length + 2)) (source destination : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (read : source head = none) :
    machine.step (cfg (some true) ip source destination head out) =
      cfg none ip source destination (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]

/-- A proof-side description of cells already erased. This function is not
computed or stored by the machine. -/
def erasedPrefix (bits : List Bool) (count : ℕ) : ℤ → Option Bool :=
  fun position => if 0 ≤ position ∧ position < (count : ℤ) then none
    else tapeOfList bits position

@[simp] theorem erasedPrefix_zero (bits : List Bool) :
    erasedPrefix bits 0 = tapeOfList bits := by
  funext position
  simp [erasedPrefix]

theorem erasedPrefix_succ (bits : List Bool) (count : ℕ) :
    Function.update (erasedPrefix bits count) (count : ℤ) none =
      erasedPrefix bits (count + 1) := by
  funext position
  simp only [Function.update_apply, erasedPrefix, Nat.cast_add, Nat.cast_one]
  split_ifs <;> first | rfl | omega

theorem erasedPrefix_complete (bits : List Bool) (count : ℕ)
    (within : bits.length ≤ count) : erasedPrefix bits count = fun _ => none := by
  funext position
  dsimp [erasedPrefix]
  split_ifs with inside
  · rfl
  · apply (tapeOfList_eq_none_iff bits position).mpr
    omega

theorem run_clear (ip : Fin (input.length + 2)) (first second out : List Bool)
    (count : ℕ) (within : count ≤ first.length) :
    machine.runFrom (cfg (some false) ip (tapeOfList first) (tapeOfList second) 0 out) count =
      cfg (some false) ip (tapeOfList first) (erasedPrefix second count) count out := by
  induction count with
  | zero => simp [runFrom]
  | succ count ih =>
      have before : count < first.length := by omega
      have read : tapeOfList first (count : ℤ) = some first[count] :=
        List.getElem?_eq_getElem before
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_clear ip _ _ _ out _ read, erasedPrefix_succ]
      simp

theorem run_to_rewind (ip : Fin (input.length + 2)) (first second out : List Bool)
    (shorter : second.length ≤ first.length) :
    machine.runFrom (cfg (some false) ip (tapeOfList first) (tapeOfList second) 0 out)
        (first.length + 1) =
      cfg (some true) ip (tapeOfList first) (fun _ => none) ((first.length : ℤ) - 1) out := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom,
    run_clear ip first second out _ le_rfl, erasedPrefix_complete second _ shorter,
    step_frontier]
  simp

theorem run_rewind (ip : Fin (input.length + 2)) (first out : List Bool)
    (destination : ℤ → Option Bool) (count : ℕ) (within : count ≤ first.length) :
    machine.runFrom
        (cfg (some true) ip (tapeOfList first) destination ((first.length : ℤ) - 1) out)
        count =
      cfg (some true) ip (tapeOfList first) destination
        ((first.length : ℤ) - 1 - count) out := by
  induction count with
  | zero => simp [runFrom]
  | succ count ih =>
      have index : first.length - 1 - count < first.length := by omega
      have read : tapeOfList first ((first.length : ℤ) - 1 - count) =
          some first[first.length - 1 - count] := by
        rw [show (first.length : ℤ) - 1 - count = ((first.length - 1 - count : ℕ) : ℤ) by omega]
        exact List.getElem?_eq_getElem index
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_rewind ip _ _ _ out _ read]
      congr 1
      push_cast
      ring

/-- At exactly `2*source.length+2` transitions the machine has halted, erased
the entire destination, and returned both work heads to zero. -/
theorem run_complete (ip : Fin (input.length + 2)) (first second out : List Bool)
    (shorter : second.length ≤ first.length) :
    machine.runFrom (cfg (some false) ip (tapeOfList first) (tapeOfList second) 0 out)
        (2 * first.length + 2) =
      cfg none ip (tapeOfList first) (fun _ => none) 0 out := by
  have split_time : 2 * first.length + 2 = (first.length + 1) + (first.length + 1) := by omega
  rw [split_time, runFrom, Function.iterate_add_apply]
  change machine.runFrom
    (machine.runFrom (cfg (some false) ip (tapeOfList first) (tapeOfList second) 0 out)
      (first.length + 1)) (first.length + 1) = _
  rw [run_to_rewind ip first second out shorter, runFrom, Function.iterate_succ_apply',
    ← runFrom, run_rewind ip first out _ _ le_rfl]
  have position : (first.length : ℤ) - 1 - first.length = -1 := by omega
  rw [position, step_delimiter ip _ _ _ out (by rfl)]
  norm_num

theorem head_in_window (ip : Fin (input.length + 2)) (first second out : List Bool)
    (shorter : second.length ≤ first.length) (steps : ℕ) (tape : Fin 2) :
    (machine.runFrom (cfg (some false) ip (tapeOfList first) (tapeOfList second) 0 out)
      steps).workTapePos tape ∈ Set.Icc (-1) (first.length : ℤ) := by
  by_cases clearing : steps ≤ first.length
  · rw [run_clear ip first second out steps clearing]
    simp only [cfg, Set.mem_Icc]
    constructor <;> omega
  · by_cases returning : steps ≤ 2 * first.length + 1
    · let elapsed := steps - (first.length + 1)
      have within : elapsed ≤ first.length := by dsimp [elapsed]; omega
      have split_time : steps = elapsed + (first.length + 1) := by dsimp [elapsed]; omega
      rw [split_time, runFrom, Function.iterate_add_apply]
      change (machine.runFrom
        (machine.runFrom (cfg (some false) ip (tapeOfList first) (tapeOfList second) 0 out)
          (first.length + 1)) elapsed).workTapePos tape ∈ _
      rw [run_to_rewind ip first second out shorter, run_rewind ip first out _ elapsed within]
      simp only [cfg, Set.mem_Icc]
      constructor <;> omega
    · have finished := run_complete ip first second out shorter
      rw [runFrom_eq_of_halt _ _ (by omega : 2 * first.length + 2 ≤ steps)
        (by rw [finished]; rfl), finished]
      simp [cfg]

/-- The bound counts actual visited cells on both tapes, for every run prefix,
including the right frontier and the left delimiter. -/
theorem every_prefix_space (ip : Fin (input.length + 2)) (first second out : List Bool)
    (shorter : second.length ≤ first.length) (path : machine.RunPath input)
    (initial : path.head =
      cfg (some false) ip (tapeOfList first) (tapeOfList second) 0 out) :
    path.space ≤ 2 * (first.length + 2) := by
  have bound := path.space_le_sum_card (S := fun _ => Finset.Icc (-1 : ℤ) first.length)
    (by
      intro c hc i
      obtain ⟨j, rfl⟩ := hc
      rw [runPath_apply_eq_runFrom, initial]
      simpa only [Finset.mem_Icc, Set.mem_Icc] using
        head_in_window ip first second out shorter j.val i)
  have size : (Finset.Icc (-1 : ℤ) (first.length : ℤ)).card = first.length + 2 := by
    rw [Int.card_Icc]
    omega
  simpa only [size, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] using bound

/-- A reuse macro in standard tape normal form. The destination may contain any
word within the source extent; after clearing it is blank everywhere. Both
heads reset, the source and read-only input are preserved, and no output is
emitted. The machine itself is independent of `L`. -/
theorem transforms_clear (L : ℕ) :
    TransformsTapes machine
      (fun _ ws => (ws 0).length ≤ L ∧ (ws 1).length ≤ (ws 0).length)
      (fun _ ws ws' emitted => ws' 0 = ws 0 ∧ ws' 1 = [] ∧ emitted = [])
      (2 * L + 2) (2 * (L + 2)) := by
  intro input ws out pre
  let begin := wordsCfg input (some machine.q₀) ws out
  have begin_eq : begin =
      cfg (some false) 1 (tapeOfList (ws 0)) (tapeOfList (ws 1)) 0 out := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [begin, wordsCfg, cfg]
    · rfl
    · rfl
  let path := MultiTapeNTM.RunPath.ofDeterministic machine begin (2 * (ws 0).length + 2)
  refine ⟨(fun i => if i = 0 then ws 0 else []), [], ⟨by simp, by simp, rfl⟩,
    path, rfl, ?_, ?_, ?_⟩
  · change machine.runFrom begin (2 * (ws 0).length + 2) = _
    rw [begin_eq, run_complete _ _ _ _ pre.2, List.append_nil]
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [cfg, wordsCfg]
    · rfl
    · rfl
  · change 2 * (ws 0).length + 2 ≤ 2 * L + 2
    omega
  · have bound := every_prefix_space (input := input) 1 (ws 0) (ws 1) out pre.2 path begin_eq
    exact bound.trans (by omega)

end NtimeDspace.ClearRegisterMachine
