import NtimeDspace.RewoundBinaryCounter

/-!
A fixed two-state, two-work-tape binary register-copy machine. Tape zero holds
the source word and tape one starts blank. The machine copies one bit per step,
then rewinds both heads together. The original register, read-only input and
write-only output are preserved. Every visited cell is accounted for, including
the right frontier and the left blank delimiter.
-/

namespace NtimeDspace.CopyRegisterMachine

open Turing Turing.MultiTapeTM

/-- `false` copies right; `true` rewinds left. The control contains no register
value or length. Both work heads always move together. -/
def machine : MultiTapeTM 2 Bool Bool :=
  .ofTr false fun rewinding _ work =>
    if rewinding then
      match work 0 with
      | some _ => ⟨0, fun _ => (none, -1), none, some true⟩
      | none => ⟨0, fun _ => (none, 1), none, none⟩
    else
      match work 0 with
      | some bit =>
          ⟨0, fun i => (if i = 0 then none else some (some bit), 1), none, some false⟩
      | none => ⟨0, fun _ => (none, -1), none, some true⟩

variable {input : List Bool}

def cfg (state : Option Bool) (ip : Fin (input.length + 2))
    (source destination : ℤ → Option Bool) (head : ℤ) (out : List Bool) :
    Cfg 2 Bool Bool input :=
  ⟨state, ip, fun i => if i = 0 then source else destination, fun _ => head, out⟩

theorem step_copy (ip : Fin (input.length + 2)) (source destination : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) (read : source head = some bit) :
    machine.step (cfg (some false) ip source destination head out) =
      cfg (some false) ip source (Function.update destination head (some bit)) (head + 1) out := by
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

/-- The semantic prefix description does not allocate a prefix in the machine;
the machine has written those cells one at a time. -/
theorem run_copy (ip : Fin (input.length + 2)) (bits out : List Bool)
    (count : ℕ) (within : count ≤ bits.length) :
    machine.runFrom (cfg (some false) ip (tapeOfList bits) (fun _ => none) 0 out) count =
      cfg (some false) ip (tapeOfList bits) (tapeOfList (bits.take count)) count out := by
  induction count with
  | zero => simp [runFrom, cfg]
  | succ count ih =>
      have before : count < bits.length := by omega
      have read : tapeOfList bits (count : ℤ) = some bits[count] :=
        List.getElem?_eq_getElem before
      have written : Function.update (tapeOfList (bits.take count)) (count : ℤ)
          (some bits[count]) = tapeOfList (bits.take (count + 1)) := by
        rw [List.take_succ_eq_append_getElem before, tapeOfList_append_single,
          List.length_take, Nat.min_eq_left (by omega : count ≤ bits.length)]
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_copy ip _ _ _ out _ read, written]
      simp

theorem run_to_rewind (ip : Fin (input.length + 2)) (bits out : List Bool) :
    machine.runFrom (cfg (some false) ip (tapeOfList bits) (fun _ => none) 0 out)
        (bits.length + 1) =
      cfg (some true) ip (tapeOfList bits) (tapeOfList bits) ((bits.length : ℤ) - 1) out := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, run_copy ip bits out _ le_rfl,
    List.take_length, step_frontier]
  simp

theorem run_rewind (ip : Fin (input.length + 2)) (bits out : List Bool)
    (count : ℕ) (within : count ≤ bits.length) :
    machine.runFrom
        (cfg (some true) ip (tapeOfList bits) (tapeOfList bits) ((bits.length : ℤ) - 1) out)
        count =
      cfg (some true) ip (tapeOfList bits) (tapeOfList bits)
        ((bits.length : ℤ) - 1 - count) out := by
  induction count with
  | zero => simp [runFrom]
  | succ count ih =>
      have index : bits.length - 1 - count < bits.length := by omega
      have read : tapeOfList bits ((bits.length : ℤ) - 1 - count) =
          some bits[bits.length - 1 - count] := by
        rw [show (bits.length : ℤ) - 1 - count = ((bits.length - 1 - count : ℕ) : ℤ) by omega]
        exact List.getElem?_eq_getElem index
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_rewind ip _ _ _ out _ read]
      congr 1
      push_cast
      ring

theorem run_complete (ip : Fin (input.length + 2)) (bits out : List Bool) :
    machine.runFrom (cfg (some false) ip (tapeOfList bits) (fun _ => none) 0 out)
        (2 * bits.length + 2) =
      cfg none ip (tapeOfList bits) (tapeOfList bits) 0 out := by
  have split_time : 2 * bits.length + 2 = (bits.length + 1) + (bits.length + 1) := by omega
  rw [split_time, runFrom, Function.iterate_add_apply]
  change machine.runFrom
    (machine.runFrom (cfg (some false) ip (tapeOfList bits) (fun _ => none) 0 out)
      (bits.length + 1)) (bits.length + 1) = _
  rw [run_to_rewind, runFrom, Function.iterate_succ_apply', ← runFrom,
    run_rewind ip bits out _ le_rfl]
  have position : (bits.length : ℤ) - 1 - bits.length = -1 := by omega
  rw [position, step_delimiter ip _ _ _ out (by rfl)]
  norm_num

/-- In both phases every head stays within one fixed interval, independently
of how often already visited cells are revisited. -/
theorem head_in_window (ip : Fin (input.length + 2)) (bits out : List Bool)
    (steps : ℕ) (tape : Fin 2) :
    (machine.runFrom (cfg (some false) ip (tapeOfList bits) (fun _ => none) 0 out)
      steps).workTapePos tape ∈ Set.Icc (-1) (bits.length : ℤ) := by
  by_cases copying : steps ≤ bits.length
  · rw [run_copy ip bits out steps copying]
    simp only [cfg, Set.mem_Icc]
    constructor <;> omega
  · by_cases returning : steps ≤ 2 * bits.length + 1
    · let elapsed := steps - (bits.length + 1)
      have within : elapsed ≤ bits.length := by dsimp [elapsed]; omega
      have split_time : steps = elapsed + (bits.length + 1) := by dsimp [elapsed]; omega
      rw [split_time, runFrom, Function.iterate_add_apply]
      change (machine.runFrom
        (machine.runFrom (cfg (some false) ip (tapeOfList bits) (fun _ => none) 0 out)
          (bits.length + 1)) elapsed).workTapePos tape ∈ _
      rw [run_to_rewind, run_rewind ip bits out elapsed within]
      simp only [cfg, Set.mem_Icc]
      constructor <;> omega
    · have finished := run_complete ip bits out
      rw [runFrom_eq_of_halt _ _ (by omega : 2 * bits.length + 2 ≤ steps)
        (by rw [finished]; rfl), finished]
      simp [cfg]

/-- Every run prefix uses at most `2*(L+2)` cells, summed over the two tapes. -/
theorem every_prefix_space (ip : Fin (input.length + 2)) (bits out : List Bool)
    (path : machine.RunPath input)
    (initial : path.head = cfg (some false) ip (tapeOfList bits) (fun _ => none) 0 out) :
    path.space ≤ 2 * (bits.length + 2) := by
  have bound := path.space_le_sum_card (S := fun _ => Finset.Icc (-1 : ℤ) bits.length)
    (by
      intro c hc i
      obtain ⟨j, rfl⟩ := hc
      rw [runPath_apply_eq_runFrom, initial]
      simpa only [Finset.mem_Icc, Set.mem_Icc] using head_in_window ip bits out j.val i)
  have size : (Finset.Icc (-1 : ℤ) (bits.length : ℤ)).card = bits.length + 2 := by
    rw [Int.card_Icc]
    omega
  simpa only [size, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] using bound

/-- A copy macro in normal form: the source is preserved, the initially empty
destination receives the same bits, both heads return to zero, and no output is
emitted. This is one fixed finite-state machine for every length bound. -/
theorem transforms_copy (L : ℕ) :
    TransformsTapes machine (fun _ ws => (ws 0).length ≤ L ∧ ws 1 = [])
      (fun _ ws ws' emitted => ws' 0 = ws 0 ∧ ws' 1 = ws 0 ∧ emitted = [])
      (2 * L + 2) (2 * (L + 2)) := by
  intro input ws out pre
  let begin := wordsCfg input (some machine.q₀) ws out
  have begin_eq : begin = cfg (some false) 1 (tapeOfList (ws 0)) (fun _ => none) 0 out := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [begin, wordsCfg, cfg, pre.2]
    · rfl
    · rfl
  let path := MultiTapeNTM.RunPath.ofDeterministic machine begin (2 * (ws 0).length + 2)
  refine ⟨fun _ => ws 0, [], ⟨rfl, rfl, rfl⟩, path, rfl, ?_, ?_, ?_⟩
  · change machine.runFrom begin (2 * (ws 0).length + 2) = _
    rw [begin_eq, run_complete, List.append_nil]
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      simp [cfg, wordsCfg]
    · rfl
    · rfl
  · change 2 * (ws 0).length + 2 ≤ 2 * L + 2
    omega
  · have bound := every_prefix_space (input := input) 1 (ws 0) out path begin_eq
    exact bound.trans (by omega)

end NtimeDspace.CopyRegisterMachine
