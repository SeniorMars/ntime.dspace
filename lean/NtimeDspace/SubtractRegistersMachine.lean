import NtimeDspace.AddRegistersMachine

/-!
A concrete three-tape ripple-borrow subtraction machine for equal-length
little-endian words. Both sources are preserved. The result has L low difference
bits followed by one explicit borrow flag; when the first value is at least the
second, its numeric value is their natural subtraction. All heads reset to zero.
The control contains only the scan/rewind phase and one borrow bit.
-/

namespace NtimeDspace.SubtractRegistersMachine

open Turing Turing.MultiTapeTM
open BinaryCounterMachine (value)
open CompareRegistersMachine (value_append)

def bitValue (bit : Bool) : ℕ := if bit then 1 else 0

def differenceBit (first second borrow : Bool) : Bool := Bool.xor (Bool.xor first second) borrow

def borrowBit (first second borrow : Bool) : Bool :=
  (!first && second) || (!first && borrow) || (second && borrow)

theorem fullSubtractor_correct (first second borrow : Bool) :
    bitValue (differenceBit first second borrow) + bitValue second + bitValue borrow =
      bitValue first + 2 * bitValue (borrowBit first second borrow) := by
  cases first <;> cases second <;> cases borrow <;> rfl

@[simp] theorem value_singleton (bit : Bool) : value [bit] = bitValue bit := by
  simp [value, bitValue]

/-- Semantic prefix: the low bits already written and the current borrow.
Out-of-range defaults are irrelevant under the scan's explicit length bound. -/
def differencePrefix (first second : List Bool) : ℕ → List Bool × Bool
  | 0 => ([], false)
  | count + 1 =>
      let previous := differencePrefix first second count
      let a := first[count]?.getD false
      let b := second[count]?.getD false
      (previous.1 ++ [differenceBit a b previous.2], borrowBit a b previous.2)

theorem prefix_length (first second : List Bool) (count : ℕ) :
    (differencePrefix first second count).1.length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [differencePrefix, ih]

/-- Prefix invariant, including the outstanding borrow. -/
theorem prefix_value (first second : List Bool) (same : first.length = second.length)
    (count : ℕ) (within : count ≤ first.length) :
    value (differencePrefix first second count).1 + value (second.take count) =
      value (first.take count) + 2 ^ count * bitValue (differencePrefix first second count).2 := by
  induction count with
  | zero => simp [differencePrefix, value, bitValue]
  | succ count ih =>
      have first_index : count < first.length := by omega
      have second_index : count < second.length := by omega
      have previous := ih (by omega)
      have subtractor := fullSubtractor_correct first[count] second[count] (differencePrefix first second count).2
      have weighted := congrArg (fun number => 2 ^ count * number) subtractor
      rw [List.take_succ_eq_append_getElem first_index,
        List.take_succ_eq_append_getElem second_index]
      simp only [differencePrefix, List.getElem?_eq_getElem first_index,
        List.getElem?_eq_getElem second_index, Option.getD_some, value_append,
        prefix_length, value_singleton, List.length_take,
        Nat.min_eq_left (by omega : count ≤ first.length),
        Nat.min_eq_left (by omega : count ≤ second.length), pow_succ]
      nlinarith

/-- The fixed-width result always includes its final borrow bit. -/
def differenceBits (first second : List Bool) : List Bool :=
  (differencePrefix first second first.length).1 ++ [(differencePrefix first second first.length).2]

theorem differenceBits_length (first second : List Bool) :
    (differenceBits first second).length = first.length + 1 := by
  simp [differenceBits, prefix_length]

theorem final_borrow_false (first second : List Bool)
    (same : first.length = second.length) (ordered : value second ≤ value first) :
    (differencePrefix first second first.length).2 = false := by
  have balance := prefix_value first second same first.length le_rfl
  have taken : second.take first.length = second := by rw [same, List.take_length]
  rw [List.take_length, taken] at balance
  have small := CompareRegistersMachine.value_lt_pow_length
    (differencePrefix first second first.length).1
  rw [prefix_length] at small
  cases flag : (differencePrefix first second first.length).2
  · rfl
  · simp only [flag, bitValue, ↓reduceIte, mul_one] at balance
    omega

theorem differenceBits_value (first second : List Bool)
    (same : first.length = second.length) (ordered : value second ≤ value first) :
    value (differenceBits first second) = value first - value second := by
  have balance := prefix_value first second same first.length le_rfl
  have taken : second.take first.length = second := by rw [same, List.take_length]
  rw [List.take_length, taken,
    final_borrow_false first second same ordered] at balance
  simp only [bitValue, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] at balance
  rw [differenceBits, value_append, value_singleton, prefix_length,
    final_borrow_false first second same ordered]
  simp only [bitValue, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
  omega

@[simp] theorem differenceBits_empty : differenceBits [] [] = [false] := rfl

/-- First control bit: rewind phase. Second control bit: borrow.
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
          ⟨0, fun i => (if i = 2 then some (some (differenceBit first second state.2)) else none, 1),
            none, some (false, borrowBit first second state.2)⟩
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
    (borrow a b : Bool) (read_first : first head = some a)
    (read_second : second head = some b) :
    machine.step (cfg (some (false, borrow)) ip first second result head out) =
      cfg (some (false, borrowBit a b borrow)) ip first second
        (Function.update result head (some (differenceBit a b borrow))) (head + 1) out := by
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
    (borrow : Bool) (read_first : first head = none) :
    machine.step (cfg (some (false, borrow)) ip first second result head out) =
      cfg (some (true, borrow)) ip first second (Function.update result head (some borrow))
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
    (borrow bit : Bool) (read_first : first head = some bit) :
    machine.step (cfg (some (true, borrow)) ip first second result head out) =
      cfg (some (true, borrow)) ip first second result (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, sub_eq_add_neg]

theorem step_delimiter (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool)
    (borrow : Bool) (read_first : first head = none) :
    machine.step (cfg (some (true, borrow)) ip first second result head out) =
      cfg none ip first second result (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]

theorem run_scan (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) (count : ℕ) (within : count ≤ first.length) :
    machine.runFrom (cfg (some (false, false)) ip
        (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out) count =
      cfg (some (false, (differencePrefix first second count).2)) ip
        (tapeOfList first) (tapeOfList second) (tapeOfList (differencePrefix first second count).1) count out := by
  induction count with
  | zero => simp [runFrom, differencePrefix, cfg]
  | succ count ih =>
      have first_index : count < first.length := by omega
      have second_index : count < second.length := by omega
      have read_first : tapeOfList first (count : ℤ) = some first[count] :=
        List.getElem?_eq_getElem first_index
      have read_second : tapeOfList second (count : ℤ) = some second[count] :=
        List.getElem?_eq_getElem second_index
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_scan ip _ _ _ _ out _ _ _ read_first read_second]
      have written : Function.update (tapeOfList (differencePrefix first second count).1) (count : ℤ)
          (some (differenceBit first[count] second[count] (differencePrefix first second count).2)) =
          tapeOfList ((differencePrefix first second count).1 ++
            [differenceBit first[count] second[count] (differencePrefix first second count).2]) := by
        rw [tapeOfList_append_single, prefix_length]
      rw [written]
      simp [differencePrefix, List.getElem?_eq_getElem first_index,
        List.getElem?_eq_getElem second_index]

theorem run_to_rewind (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) :
    machine.runFrom (cfg (some (false, false)) ip
        (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out) (first.length + 1) =
      cfg (some (true, (differencePrefix first second first.length).2)) ip
        (tapeOfList first) (tapeOfList second) (tapeOfList (differenceBits first second))
        ((first.length : ℤ) - 1) out := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom,
    run_scan ip first second out same _ le_rfl,
    step_frontier ip _ _ _ _ out _ (by simp)]
  rw [differenceBits, tapeOfList_append_single, prefix_length]

theorem run_rewind (ip : Fin (input.length + 2)) (first second out : List Bool)
    (result : ℤ → Option Bool) (borrow : Bool) (count : ℕ) (within : count ≤ first.length) :
    machine.runFrom
        (cfg (some (true, borrow)) ip (tapeOfList first) (tapeOfList second)
          result ((first.length : ℤ) - 1) out) count =
      cfg (some (true, borrow)) ip (tapeOfList first) (tapeOfList second)
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
        step_rewind ip _ _ _ _ out borrow _ read]
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
        (tapeOfList (differenceBits first second)) 0 out := by
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

/-- All three heads stay between the left delimiter and the borrow cell,
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

/-- Subtraction macro with explicit order, equal-length, and blank-result
conditions. The postcondition includes the exact bits and numeric difference;
`TransformsTapes` requires all heads reset and no emitted output. -/
theorem transforms_subtract (L : ℕ) :
    TransformsTapes machine
      (fun _ ws => (ws 0).length ≤ L ∧ (ws 0).length = (ws 1).length ∧ ws 2 = [] ∧
        value (ws 1) ≤ value (ws 0))
      (fun _ ws ws' emitted => ws' 0 = ws 0 ∧ ws' 1 = ws 1 ∧
        ws' 2 = differenceBits (ws 0) (ws 1) ∧
        value (ws' 2) = value (ws 0) - value (ws 1) ∧
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
      fin_cases i <;> simp [begin, wordsCfg, cfg, pre.2.2.1]
    · rfl
    · rfl
  let path := MultiTapeNTM.RunPath.ofDeterministic machine begin (2 * (ws 0).length + 2)
  let finalWords : Fin 3 → List Bool := fun i =>
    if i = 0 then ws 0 else if i = 1 then ws 1 else differenceBits (ws 0) (ws 1)
  refine ⟨finalWords, [], ⟨rfl, rfl, rfl, differenceBits_value (ws 0) (ws 1) pre.2.1 pre.2.2.2,
    differenceBits_length (ws 0) (ws 1), rfl⟩, path, rfl, ?_, ?_, ?_⟩
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

end NtimeDspace.SubtractRegistersMachine
