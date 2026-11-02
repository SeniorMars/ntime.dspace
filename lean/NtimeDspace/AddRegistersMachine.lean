import NtimeDspace.CompareRegistersMachine

/-!
A concrete three-work-tape ripple-carry adder for equal-length little-endian
binary words. Both source words are preserved. The third tape starts blank and
receives exactly `L+1` bits, including a final carry bit even when it is false.
The control stores only the phase and one carry bit. All heads move together,
then rewind to zero; the read-only input and write-only output are preserved.

The prefix lists below describe cells already written by individual machine
steps. They are proof-side objects, not buffers in the finite control.
-/

namespace NtimeDspace.AddRegistersMachine

open Turing Turing.MultiTapeTM
open BinaryCounterMachine (value)
open CompareRegistersMachine (value_append)

def bitValue (bit : Bool) : ℕ := if bit then 1 else 0

def sumBit (first second carry : Bool) : Bool := Bool.xor (Bool.xor first second) carry

def carryBit (first second carry : Bool) : Bool :=
  (first && second) || (first && carry) || (second && carry)

theorem fullAdder_correct (first second carry : Bool) :
    bitValue (sumBit first second carry) + 2 * bitValue (carryBit first second carry) =
      bitValue first + bitValue second + bitValue carry := by
  cases first <;> cases second <;> cases carry <;> rfl

@[simp] theorem value_singleton (bit : Bool) : value [bit] = bitValue bit := by
  simp [value, bitValue]

/-- Semantic prefix: the low bits already written and the current carry.
Out-of-range defaults are irrelevant under the scan's explicit length bound. -/
def sumPrefix (first second : List Bool) : ℕ → List Bool × Bool
  | 0 => ([], false)
  | count + 1 =>
      let previous := sumPrefix first second count
      let a := first[count]?.getD false
      let b := second[count]?.getD false
      (previous.1 ++ [sumBit a b previous.2], carryBit a b previous.2)

theorem prefix_length (first second : List Bool) (count : ℕ) :
    (sumPrefix first second count).1.length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [sumPrefix, ih]

/-- The carry is the high bit of the sum of the two prefixes. -/
theorem prefix_value (first second : List Bool) (same : first.length = second.length)
    (count : ℕ) (within : count ≤ first.length) :
    value (sumPrefix first second count).1 + 2 ^ count * bitValue (sumPrefix first second count).2 =
      value (first.take count) + value (second.take count) := by
  induction count with
  | zero => simp [sumPrefix, value, bitValue]
  | succ count ih =>
      have first_index : count < first.length := by omega
      have second_index : count < second.length := by omega
      have previous := ih (by omega)
      have adder := fullAdder_correct first[count] second[count] (sumPrefix first second count).2
      have weighted := congrArg (fun number => 2 ^ count * number) adder
      rw [List.take_succ_eq_append_getElem first_index,
        List.take_succ_eq_append_getElem second_index]
      simp only [sumPrefix, List.getElem?_eq_getElem first_index,
        List.getElem?_eq_getElem second_index, Option.getD_some, value_append,
        prefix_length, value_singleton, List.length_take,
        Nat.min_eq_left (by omega : count ≤ first.length),
        Nat.min_eq_left (by omega : count ≤ second.length), pow_succ]
      nlinarith

/-- The fixed-width result always includes its final carry bit. -/
def sumBits (first second : List Bool) : List Bool :=
  (sumPrefix first second first.length).1 ++ [(sumPrefix first second first.length).2]

theorem sumBits_length (first second : List Bool) :
    (sumBits first second).length = first.length + 1 := by
  simp [sumBits, prefix_length]

theorem sumBits_value (first second : List Bool) (same : first.length = second.length) :
    value (sumBits first second) = value first + value second := by
  rw [sumBits, value_append, value_singleton, prefix_length,
    prefix_value first second same _ le_rfl, List.take_length]
  rw [same, List.take_length]

@[simp] theorem sumBits_empty : sumBits [] [] = [false] := rfl

/-- First control bit: rewind phase. Second control bit: carry.
The length and numeric register values never occur in the control. -/
def machine : MultiTapeTM 3 Bool (Bool × Bool) :=
  .ofTr (false, false) fun state _ work =>
    if state.1 then
      match work 0 with
      | some _ => ⟨0, fun _ => (none, -1), none, some state⟩
      | none => ⟨0, fun _ => (none, 1), none, none⟩
    else
      match work 0, work 1 with
      | some first, some second =>
          ⟨0, fun i => (if i = 2 then some (some (sumBit first second state.2)) else none, 1),
            none, some (false, carryBit first second state.2)⟩
      | _, _ =>
          ⟨0, fun i => (if i = 2 then some (some state.2) else none, -1),
            none, some (true, state.2)⟩

variable {input : List Bool}

def cfg (state : Option (Bool × Bool)) (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool) :
    Cfg 3 Bool (Bool × Bool) input :=
  ⟨state, ip, fun i => if i = 0 then first else if i = 1 then second else result,
    fun _ => head, out⟩

theorem step_scan (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool)
    (carry a b : Bool) (read_first : first head = some a)
    (read_second : second head = some b) :
    machine.step (cfg (some (false, carry)) ip first second result head out) =
      cfg (some (false, carryBit a b carry)) ip first second
        (Function.update result head (some (sumBit a b carry))) (head + 1) out := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]
  · funext i
    simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]

theorem step_frontier (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool)
    (carry : Bool) (read_first : first head = none) :
    machine.step (cfg (some (false, carry)) ip first second result head out) =
      cfg (some (true, carry)) ip first second (Function.update result head (some carry))
        (head - 1) out := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · funext i
    simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, sub_eq_add_neg]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]

theorem step_rewind (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool)
    (carry bit : Bool) (read_first : first head = some bit) :
    machine.step (cfg (some (true, carry)) ip first second result head out) =
      cfg (some (true, carry)) ip first second result (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, sub_eq_add_neg]

theorem step_delimiter (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool)
    (carry : Bool) (read_first : first head = none) :
    machine.step (cfg (some (true, carry)) ip first second result head out) =
      cfg none ip first second result (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]

theorem run_scan (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) (count : ℕ) (within : count ≤ first.length) :
    machine.runFrom (cfg (some (false, false)) ip
        (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out) count =
      cfg (some (false, (sumPrefix first second count).2)) ip
        (tapeOfList first) (tapeOfList second) (tapeOfList (sumPrefix first second count).1) count out := by
  induction count with
  | zero => simp [runFrom, sumPrefix, cfg]
  | succ count ih =>
      have first_index : count < first.length := by omega
      have second_index : count < second.length := by omega
      have read_first : tapeOfList first (count : ℤ) = some first[count] :=
        List.getElem?_eq_getElem first_index
      have read_second : tapeOfList second (count : ℤ) = some second[count] :=
        List.getElem?_eq_getElem second_index
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_scan ip _ _ _ _ out _ _ _ read_first read_second]
      have written : Function.update (tapeOfList (sumPrefix first second count).1) (count : ℤ)
          (some (sumBit first[count] second[count] (sumPrefix first second count).2)) =
          tapeOfList ((sumPrefix first second count).1 ++
            [sumBit first[count] second[count] (sumPrefix first second count).2]) := by
        rw [tapeOfList_append_single, prefix_length]
      rw [written]
      simp [sumPrefix, List.getElem?_eq_getElem first_index,
        List.getElem?_eq_getElem second_index]

theorem run_to_rewind (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) :
    machine.runFrom (cfg (some (false, false)) ip
        (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out) (first.length + 1) =
      cfg (some (true, (sumPrefix first second first.length).2)) ip
        (tapeOfList first) (tapeOfList second) (tapeOfList (sumBits first second))
        ((first.length : ℤ) - 1) out := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom,
    run_scan ip first second out same _ le_rfl,
    step_frontier ip _ _ _ _ out _ (by simp)]
  rw [sumBits, tapeOfList_append_single, prefix_length]

theorem run_rewind (ip : Fin (input.length + 2)) (first second out : List Bool)
    (result : ℤ → Option Bool) (carry : Bool) (count : ℕ) (within : count ≤ first.length) :
    machine.runFrom
        (cfg (some (true, carry)) ip (tapeOfList first) (tapeOfList second)
          result ((first.length : ℤ) - 1) out) count =
      cfg (some (true, carry)) ip (tapeOfList first) (tapeOfList second)
        result ((first.length : ℤ) - 1 - count) out := by
  induction count with
  | zero => simp [runFrom]
  | succ count ih =>
      have index : first.length - 1 - count < first.length := by omega
      have read : tapeOfList first ((first.length : ℤ) - 1 - count) =
          some first[first.length - 1 - count] := by
        rw [show (first.length : ℤ) - 1 - count =
          ((first.length - 1 - count : ℕ) : ℤ) by omega]
        exact List.getElem?_eq_getElem index
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_rewind ip _ _ _ _ out carry _ read]
      congr 1
      push_cast
      ring

/-- Exact final tape contents and all head positions. -/
theorem run_complete (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) :
    machine.runFrom (cfg (some (false, false)) ip
        (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out)
        (2 * first.length + 2) =
      cfg none ip (tapeOfList first) (tapeOfList second)
        (tapeOfList (sumBits first second)) 0 out := by
  have split_time : 2 * first.length + 2 = (first.length + 1) + (first.length + 1) := by omega
  rw [split_time, runFrom, Function.iterate_add_apply]
  change machine.runFrom
    (machine.runFrom (cfg (some (false, false)) ip
      (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out)
      (first.length + 1)) (first.length + 1) = _
  rw [run_to_rewind ip first second out same, runFrom, Function.iterate_succ_apply',
    ← runFrom, run_rewind ip first second out _ _ _ le_rfl]
  have position : (first.length : ℤ) - 1 - first.length = -1 := by omega
  rw [position, step_delimiter ip _ _ _ _ out _ (by rfl)]
  norm_num

/-- All three heads stay between the left delimiter and the carry cell,
including every prefix after halting. -/
theorem head_in_window (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) (steps : ℕ) (tape : Fin 3) :
    (machine.runFrom (cfg (some (false, false)) ip
      (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out)
      steps).workTapePos tape ∈ Set.Icc (-1) (first.length : ℤ) := by
  by_cases scanning : steps ≤ first.length
  · rw [run_scan ip first second out same steps scanning]
    simp only [cfg, Set.mem_Icc]
    constructor <;> omega
  · by_cases returning : steps ≤ 2 * first.length + 1
    · let elapsed := steps - (first.length + 1)
      have within : elapsed ≤ first.length := by dsimp [elapsed]; omega
      have split_time : steps = elapsed + (first.length + 1) := by dsimp [elapsed]; omega
      rw [split_time, runFrom, Function.iterate_add_apply]
      change (machine.runFrom
        (machine.runFrom (cfg (some (false, false)) ip
          (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out)
          (first.length + 1)) elapsed).workTapePos tape ∈ _
      rw [run_to_rewind ip first second out same,
        run_rewind ip first second out _ _ elapsed within]
      simp only [cfg, Set.mem_Icc]
      constructor <;> omega
    · have finished := run_complete ip first second out same
      rw [runFrom_eq_of_halt _ _ (by omega : 2 * first.length + 2 ≤ steps)
        (by rw [finished]; rfl), finished]
      simp [cfg]

/-- Actual visited-cell space, summed over the three tapes, for every finite
run path from the specified input configuration. -/
theorem every_prefix_space (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) (path : machine.RunPath input)
    (initial : path.head = cfg (some (false, false)) ip
      (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out) :
    path.space ≤ 3 * (first.length + 2) := by
  have bound := path.space_le_sum_card (S := fun _ => Finset.Icc (-1 : ℤ) first.length)
    (by
      intro c hc i
      obtain ⟨j, rfl⟩ := hc
      rw [runPath_apply_eq_runFrom, initial]
      simpa only [Finset.mem_Icc, Set.mem_Icc] using
        head_in_window ip first second out same j.val i)
  have size : (Finset.Icc (-1 : ℤ) (first.length : ℤ)).card = first.length + 2 := by
    rw [Int.card_Icc]
    omega
  simpa only [size, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] using bound

/-- An addition macro with explicit equal-length and blank-result conditions.
The postcondition includes the exact bits, their numeric sum, and the output
width; `TransformsTapes` also requires all heads reset and no emitted output. -/
theorem transforms_add (L : ℕ) :
    TransformsTapes machine
      (fun _ ws => (ws 0).length ≤ L ∧ (ws 0).length = (ws 1).length ∧ ws 2 = [])
      (fun _ ws ws' emitted => ws' 0 = ws 0 ∧ ws' 1 = ws 1 ∧
        ws' 2 = sumBits (ws 0) (ws 1) ∧
        value (ws' 2) = value (ws 0) + value (ws 1) ∧
        (ws' 2).length = (ws 0).length + 1 ∧ emitted = [])
      (2 * L + 2) (3 * (L + 2)) := by
  intro input ws out pre
  let begin := wordsCfg input (some machine.q₀) ws out
  have begin_eq : begin = cfg (some (false, false)) 1
      (tapeOfList (ws 0)) (tapeOfList (ws 1)) (fun _ => none) 0 out := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [begin, wordsCfg, cfg, pre.2.2]
    · rfl
    · rfl
  let path := MultiTapeNTM.RunPath.ofDeterministic machine begin (2 * (ws 0).length + 2)
  let finalWords : Fin 3 → List Bool := fun i =>
    if i = 0 then ws 0 else if i = 1 then ws 1 else sumBits (ws 0) (ws 1)
  refine ⟨finalWords, [], ⟨rfl, rfl, rfl, sumBits_value (ws 0) (ws 1) pre.2.1,
    sumBits_length (ws 0) (ws 1), rfl⟩, path, rfl, ?_, ?_, ?_⟩
  · change machine.runFrom begin (2 * (ws 0).length + 2) = _
    rw [begin_eq, run_complete 1 (ws 0) (ws 1) out pre.2.1, List.append_nil]
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [cfg, wordsCfg, finalWords]
    · rfl
    · rfl
  · change 2 * (ws 0).length + 2 ≤ 2 * L + 2
    omega
  · have bound := every_prefix_space (input := input) 1 (ws 0) (ws 1) out pre.2.1 path begin_eq
    exact bound.trans (by omega)

end NtimeDspace.AddRegistersMachine
