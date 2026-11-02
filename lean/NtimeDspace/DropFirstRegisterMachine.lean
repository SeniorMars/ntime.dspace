import NtimeDspace.RewoundBinaryCounter

/-!
An in-place one-work-tape machine removing the least-significant bit of a
little-endian binary word. Each remaining bit is read, carried one cell left
in finite control, and written there. The obsolete final cell is cleared,
then the head rewinds to zero. Input and output are unchanged.

The control has seven states, independently of the word length. Proof-side
prefix functions describe existing tape contents; the machine stores no list.
-/

namespace NtimeDspace.DropFirstRegisterMachine

open Turing Turing.MultiTapeTM
open BinaryCounterMachine (value)

inductive State where
  | start
  | scan
  | write (bit : Bool)
  | advance
  | clear
  | rewind
  deriving DecidableEq, Fintype

def machine : MultiTapeTM 1 Bool State :=
  .ofTr .start fun state _ work =>
    match state with
    | .start =>
        match work 0 with
        | none => ⟨0, fun _ => (none, 0), none, none⟩
        | some _ => ⟨0, fun _ => (none, 1), none, some .scan⟩
    | .scan =>
        match work 0 with
        | none => ⟨0, fun _ => (none, -1), none, some .clear⟩
        | some bit => ⟨0, fun _ => (none, -1), none, some (.write bit)⟩
    | .write bit => ⟨0, fun _ => (some (some bit), 1), none, some .advance⟩
    | .advance => ⟨0, fun _ => (none, 1), none, some .scan⟩
    | .clear => ⟨0, fun _ => (some none, -1), none, some .rewind⟩
    | .rewind =>
        match work 0 with
        | none => ⟨0, fun _ => (none, 1), none, none⟩
        | some _ => ⟨0, fun _ => (none, -1), none, some .rewind⟩

variable {input : List Bool}

def cfg (state : Option State) (ip : Fin (input.length + 2))
    (tape : ℤ → Option Bool) (head : ℤ) (out : List Bool) : Cfg 1 Bool State input :=
  ⟨state, ip, fun _ => tape, fun _ => head, out⟩

theorem step_start (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) (read : tape head = some bit) :
    machine.step (cfg (some .start) ip tape head out) =
      cfg (some .scan) ip tape (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]

theorem step_start_empty (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (read : tape head = none) :
    machine.step (cfg (some .start) ip tape head out) = cfg none ip tape head out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]

theorem step_scan (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) (read : tape head = some bit) :
    machine.step (cfg (some .scan) ip tape head out) =
      cfg (some (.write bit)) ip tape (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read, sub_eq_add_neg]

theorem step_frontier (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (read : tape head = none) :
    machine.step (cfg (some .scan) ip tape head out) =
      cfg (some .clear) ip tape (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read, sub_eq_add_neg]

theorem step_write (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) :
    machine.step (cfg (some (.write bit)) ip tape head out) =
      cfg (some .advance) ip (Function.update tape head (some bit)) (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply]

theorem step_advance (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) :
    machine.step (cfg (some .advance) ip tape head out) =
      cfg (some .scan) ip tape (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply]

theorem step_clear (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) :
    machine.step (cfg (some .clear) ip tape head out) =
      cfg (some .rewind) ip (Function.update tape head none) (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, sub_eq_add_neg]

theorem step_rewind (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) (read : tape head = some bit) :
    machine.step (cfg (some .rewind) ip tape head out) =
      cfg (some .rewind) ip tape (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read, sub_eq_add_neg]

theorem step_delimiter (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (read : tape head = none) :
    machine.step (cfg (some .rewind) ip tape head out) = cfg none ip tape (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]

/-- Contents after `count` bits have been shifted one cell left. -/
def shiftedPrefix (bits : List Bool) (count : ℕ) : ℤ → Option Bool :=
  fun position => if 0 ≤ position ∧ position < (count : ℤ)
    then tapeOfList bits (position + 1) else tapeOfList bits position

@[simp] theorem shiftedPrefix_zero (bits : List Bool) :
    shiftedPrefix bits 0 = tapeOfList bits := by
  funext position
  simp [shiftedPrefix]

theorem shiftedPrefix_succ (bits : List Bool) (count : ℕ) :
    Function.update (shiftedPrefix bits count) (count : ℤ)
        (tapeOfList bits ((count : ℤ) + 1)) = shiftedPrefix bits (count + 1) := by
  funext position
  by_cases same : position = (count : ℤ)
  · subst position
    simp [shiftedPrefix]
  · simp only [Function.update_apply, shiftedPrefix, Nat.cast_add, Nat.cast_one]
    split_ifs <;> first | rfl | omega

theorem shiftedPrefix_read (first : Bool) (bits : List Bool) (count : ℕ) :
    shiftedPrefix (first :: bits) count ((count : ℤ) + 1) = bits[count]? := by
  rw [shiftedPrefix, ite_eq_right (by omega)]
  change (first :: bits)[count + 1]? = bits[count]?
  rfl

/-- Clearing the old final cell is necessary: shifting the prefix alone still
leaves one obsolete symbol to its right. -/
theorem shiftedPrefix_complete (first : Bool) (bits : List Bool) :
    Function.update (shiftedPrefix (first :: bits) bits.length) (bits.length : ℤ) none =
      tapeOfList bits := by
  funext position
  cases position with
  | negSucc position => simp [shiftedPrefix, tapeOfList]
  | ofNat position =>
      simp only [Int.ofNat_eq_natCast]
      by_cases before : position < bits.length
      · simp only [Function.update_apply]
        rw [ite_eq_right (by omega), shiftedPrefix, ite_eq_left (by constructor <;> omega)]
        change (first :: bits)[position + 1]? = bits[position]?
        rfl
      · by_cases same : position = bits.length
        · subst position
          simp [tapeOfList]
        · have after : bits.length < position := by omega
          have old_blank : (first :: bits)[position]? = none := List.getElem?_eq_none (by simp; omega)
          simp [shiftedPrefix, before, same, tapeOfList, old_blank]

theorem run_copy_bit (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) (read : tape head = some bit) :
    machine.runFrom (cfg (some .scan) ip tape head out) 3 =
      cfg (some .scan) ip (Function.update tape (head - 1) (some bit)) (head + 1) out := by
  simp only [runFrom, Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_scan ip tape head out bit read, step_write, step_advance]
  congr 1
  ring

theorem run_scan (ip : Fin (input.length + 2)) (first : Bool) (bits out : List Bool)
    (count : ℕ) (within : count ≤ bits.length) :
    machine.runFrom (cfg (some .start) ip (tapeOfList (first :: bits)) 0 out)
        (1 + 3 * count) =
      cfg (some .scan) ip (shiftedPrefix (first :: bits) count) ((count : ℤ) + 1) out := by
  induction count with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, shiftedPrefix_zero, Nat.cast_zero, zero_add,
        runFrom, Function.iterate_one]
      exact step_start ip _ 0 out first rfl
  | succ count ih =>
      have before : count < bits.length := by omega
      have read : shiftedPrefix (first :: bits) count ((count : ℤ) + 1) = some bits[count] := by
        rw [shiftedPrefix_read]
        exact List.getElem?_eq_getElem before
      have value_read : tapeOfList (first :: bits) ((count : ℤ) + 1) = some bits[count] := by
        change (first :: bits)[count + 1]? = some bits[count]
        simpa only [List.getElem?_cons_succ] using List.getElem?_eq_getElem before
      rw [show 1 + 3 * (count + 1) = 3 + (1 + 3 * count) by omega,
        runFrom, Function.iterate_add_apply]
      change machine.runFrom (machine.runFrom _ (1 + 3 * count)) 3 = _
      rw [ih (by omega), run_copy_bit ip _ _ out _ read,
        show (count : ℤ) + 1 - 1 = count by omega, ← value_read, shiftedPrefix_succ]
      simp

theorem run_to_rewind (ip : Fin (input.length + 2)) (first : Bool) (bits out : List Bool) :
    machine.runFrom (cfg (some .start) ip (tapeOfList (first :: bits)) 0 out)
        (3 * bits.length + 3) =
      cfg (some .rewind) ip (tapeOfList bits) ((bits.length : ℤ) - 1) out := by
  rw [show 3 * bits.length + 3 = 2 + (1 + 3 * bits.length) by omega,
    runFrom, Function.iterate_add_apply]
  change machine.runFrom (machine.runFrom _ (1 + 3 * bits.length)) 2 = _
  rw [run_scan ip first bits out _ le_rfl]
  simp only [runFrom, Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_frontier ip _ _ out (by rw [shiftedPrefix_read]; simp), step_clear,
    show (bits.length : ℤ) + 1 - 1 = bits.length by omega, shiftedPrefix_complete]

theorem run_rewind (ip : Fin (input.length + 2)) (bits out : List Bool)
    (count : ℕ) (within : count ≤ bits.length) :
    machine.runFrom
        (cfg (some .rewind) ip (tapeOfList bits) ((bits.length : ℤ) - 1) out) count =
      cfg (some .rewind) ip (tapeOfList bits) ((bits.length : ℤ) - 1 - count) out := by
  induction count with
  | zero => simp [runFrom]
  | succ count ih =>
      have index : bits.length - 1 - count < bits.length := by omega
      have read : tapeOfList bits ((bits.length : ℤ) - 1 - count) =
          some bits[bits.length - 1 - count] := by
        rw [show (bits.length : ℤ) - 1 - count = ((bits.length - 1 - count : ℕ) : ℤ) by omega]
        exact List.getElem?_eq_getElem index
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_rewind ip _ _ out _ read]
      congr 1
      push_cast
      ring

theorem run_rewind_complete (ip : Fin (input.length + 2)) (bits out : List Bool) :
    machine.runFrom
        (cfg (some .rewind) ip (tapeOfList bits) ((bits.length : ℤ) - 1) out)
        (bits.length + 1) = cfg none ip (tapeOfList bits) 0 out := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, run_rewind ip bits out _ le_rfl,
    show (bits.length : ℤ) - 1 - bits.length = -1 by omega,
    step_delimiter ip _ _ out (by rfl)]
  norm_num

/-- A nonempty word of length `L` is shifted and reset in `4*L` transitions. -/
theorem run_nonempty (ip : Fin (input.length + 2)) (first : Bool) (bits out : List Bool) :
    machine.runFrom (cfg (some .start) ip (tapeOfList (first :: bits)) 0 out)
        (4 * (bits.length + 1)) = cfg none ip (tapeOfList bits) 0 out := by
  rw [show 4 * (bits.length + 1) = (bits.length + 1) + (3 * bits.length + 3) by omega,
    runFrom, Function.iterate_add_apply]
  change machine.runFrom (machine.runFrom _ (3 * bits.length + 3)) (bits.length + 1) = _
  rw [run_to_rewind, run_rewind_complete]

/-- Uniform bound also covering the empty register, which halts in one step. -/
theorem run_complete (ip : Fin (input.length + 2)) (bits out : List Bool) :
    machine.runFrom (cfg (some .start) ip (tapeOfList bits) 0 out) (4 * bits.length + 1) =
      cfg none ip (tapeOfList bits.tail) 0 out := by
  cases bits with
  | nil =>
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.tail_nil,
        runFrom, Function.iterate_one]
      exact step_start_empty ip _ 0 out rfl
  | cons first bits =>
      rw [List.length_cons, runFrom, Function.iterate_succ_apply', ← runFrom,
        run_nonempty, step_of_halt (by rfl)]
      rfl

theorem value_tail (bits : List Bool) : value bits.tail = value bits / 2 := by
  cases bits with
  | nil => rfl
  | cons bit bits => cases bit <;> simp [value]; omega

/-- A one-head run visits at most one cell for each configuration. This counts
visited cells, regardless of the changing number of nonblank symbols. -/
theorem path_space_le_length (path : machine.RunPath input) : path.space ≤ path.length + 1 := by
  simp only [MultiTapeNTM.RunPath.space, Fin.sum_univ_one,
    MultiTapeNTM.RunPath.spaceUsedByTape, MultiTapeNTM.RunPath.visitedByTapeHead]
  exact Finset.card_image_le.trans (by simp)

/-- Every prefix, including arbitrarily long prefixes after halting, has a
linear actual visited-cell bound. -/
theorem every_prefix_space (ip : Fin (input.length + 2)) (bits out : List Bool)
    (path : machine.RunPath input)
    (initial : path.head = cfg (some .start) ip (tapeOfList bits) 0 out) :
    path.space ≤ 4 * bits.length + 2 := by
  let finished := MultiTapeNTM.RunPath.ofDeterministic machine
    (cfg (some .start) ip (tapeOfList bits) 0 out) (4 * bits.length + 1)
  have final : finished.last = cfg none ip (tapeOfList bits.tail) 0 out := run_complete ip bits out
  have bound := RewoundBinaryCounter.path_space_le_halting_path path finished initial
    (by rw [final]; rfl)
  have finite_bound := path_space_le_length finished
  change finished.space ≤ (4 * bits.length + 1) + 1 at finite_bound
  exact bound.trans finite_bound

/-- Remove exactly the first bit in place, reset the work head, preserve input
and output, and divide the interpreted register value by two. -/
theorem transforms_drop (L : ℕ) :
    TransformsTapes machine (fun _ ws => (ws 0).length ≤ L)
      (fun _ ws ws' emitted => ws' 0 = (ws 0).tail ∧
        (ws' 0).length = (ws 0).length - 1 ∧ value (ws' 0) = value (ws 0) / 2 ∧ emitted = [])
      (4 * L + 1) (4 * L + 2) := by
  intro input ws out pre
  let begin := wordsCfg input (some machine.q₀) ws out
  have begin_eq : begin = cfg (some .start) 1 (tapeOfList (ws 0)) 0 out := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      exact congrArg tapeOfList (congrArg ws (Subsingleton.elim i 0))
    · rfl
    · rfl
  let path := MultiTapeNTM.RunPath.ofDeterministic machine begin (4 * (ws 0).length + 1)
  refine ⟨(fun _ => (ws 0).tail), [],
    ⟨rfl, List.length_tail, value_tail _, rfl⟩, path, rfl, ?_, ?_, ?_⟩
  · change machine.runFrom begin (4 * (ws 0).length + 1) = _
    rw [begin_eq, run_complete, List.append_nil]
    rfl
  · change 4 * (ws 0).length + 1 ≤ 4 * L + 1
    omega
  · exact (every_prefix_space (input := input) 1 (ws 0) out path begin_eq).trans (by omega)

end NtimeDspace.DropFirstRegisterMachine
