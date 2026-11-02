import NtimeDspace.CopyRegisterMachine

/-!
A concrete three-work-tape comparator for equal-length little-endian binary
words. The two source words are preserved. The initially blank third tape
receives one Boolean, true exactly when the first numeric value is smaller.
The finite control remembers only the comparison of the bits scanned so far;
each new differing, more significant bit overrides it. All heads return to
zero. Input and output are preserved. Space below counts all visited cells,
including the two source frontiers and left delimiters.
-/

namespace NtimeDspace.CompareRegistersMachine

open Turing Turing.MultiTapeTM
open BinaryCounterMachine (value)

/-- A new, more significant unequal pair decides the comparison. -/
def updateFlag (flag first second : Bool) : Bool :=
  if first = second then flag else !first && second

theorem value_append (first second : List Bool) :
    value (first ++ second) = value first + 2 ^ first.length * value second := by
  induction first with
  | nil => simp [value]
  | cons bit bits ih =>
      cases bit <;> simp [value, ih, pow_succ] <;> ring

theorem value_lt_pow_length (bits : List Bool) : value bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [value]
  | cons bit bits ih =>
      cases bit <;> simp only [value, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, pow_succ] <;> omega

theorem updateFlag_correct (first second : List Bool) (same : first.length = second.length)
    (a b : Bool) :
    updateFlag (decide (value first < value second)) a b =
      decide (value (first ++ [a]) < value (second ++ [b])) := by
  have first_bound := value_lt_pow_length first
  have second_bound := value_lt_pow_length second
  rw [← same] at second_bound
  cases a <;> cases b <;>
    simp [updateFlag, value_append, value, ← same] <;> omega

/-- The first control bit selects rewind; the second is the comparison flag.
The control contains neither the register length nor either numeric value. -/
def machine : MultiTapeTM 3 Bool (Bool × Bool) :=
  .ofTr (false, false) fun state _ work =>
    if state.1 then
      match work 0 with
      | some _ =>
          ⟨0, fun i => (none, if i = 2 then 0 else -1), none, some state⟩
      | none =>
          ⟨0, fun i => (none, if i = 2 then 0 else 1), none, none⟩
    else
      match work 0, work 1 with
      | some first, some second =>
          ⟨0, fun i => (none, if i = 2 then 0 else 1), none,
            some (false, updateFlag state.2 first second)⟩
      | _, _ =>
          ⟨0, fun i => (if i = 2 then some (some state.2) else none,
            if i = 2 then 0 else -1), none, some (true, state.2)⟩

variable {input : List Bool}

def cfg (state : Option (Bool × Bool)) (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool) :
    Cfg 3 Bool (Bool × Bool) input :=
  ⟨state, ip, fun i => if i = 0 then first else if i = 1 then second else result,
    fun i => if i = 2 then 0 else head, out⟩

theorem step_scan (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool)
    (flag a b : Bool) (read_first : first head = some a)
    (read_second : second head = some b) :
    machine.step (cfg (some (false, flag)) ip first second result head out) =
      cfg (some (false, updateFlag flag a b)) ip first second result (head + 1) out := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first, read_second]

theorem step_frontier (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool)
    (flag : Bool) (read_first : first head = none) :
    machine.step (cfg (some (false, flag)) ip first second result head out) =
      cfg (some (true, flag)) ip first second (Function.update result 0 (some flag))
        (head - 1) out := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first,
      sub_eq_add_neg]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]

theorem step_rewind (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool)
    (flag bit : Bool) (read_first : first head = some bit) :
    machine.step (cfg (some (true, flag)) ip first second result head out) =
      cfg (some (true, flag)) ip first second result (head - 1) out := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first,
      sub_eq_add_neg]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]

theorem step_delimiter (ip : Fin (input.length + 2))
    (first second result : ℤ → Option Bool) (head : ℤ) (out : List Bool)
    (flag : Bool) (read_first : first head = none) :
    machine.step (cfg (some (true, flag)) ip first second result head out) =
      cfg none ip first second result (head + 1) out := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read_first]

/-- The finite flag equals the numeric comparison of the prefixes already read.
Prefix lists occur only in this specification, not in the machine's control. -/
theorem run_scan (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) (count : ℕ) (within : count ≤ first.length) :
    machine.runFrom (cfg (some (false, false)) ip
        (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out) count =
      cfg (some (false, decide (value (first.take count) < value (second.take count))))
        ip (tapeOfList first) (tapeOfList second) (fun _ => none) count out := by
  induction count with
  | zero => simp [runFrom, value]
  | succ count ih =>
      have first_index : count < first.length := by omega
      have second_index : count < second.length := by omega
      have read_first : tapeOfList first (count : ℤ) = some first[count] :=
        List.getElem?_eq_getElem first_index
      have read_second : tapeOfList second (count : ℤ) = some second[count] :=
        List.getElem?_eq_getElem second_index
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_scan ip _ _ _ _ out _ _ _ read_first read_second,
        updateFlag_correct _ _ (by simp [List.length_take, same]),
        ← List.take_succ_eq_append_getElem first_index,
        ← List.take_succ_eq_append_getElem second_index]
      simp

theorem blank_write (flag : Bool) :
    Function.update (fun _ : ℤ => (none : Option Bool)) 0 (some flag) =
      tapeOfList [flag] := by
  funext z
  cases z with
  | negSucc n => simp [tapeOfList]
  | ofNat n =>
      cases n with
      | zero => simp [tapeOfList]
      | succ n =>
          have nonzero : (n : ℤ) + 1 ≠ 0 := by omega
          simp [tapeOfList, nonzero]

theorem run_to_rewind (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) :
    machine.runFrom (cfg (some (false, false)) ip
        (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out) (first.length + 1) =
      cfg (some (true, decide (value first < value second))) ip
        (tapeOfList first) (tapeOfList second)
        (tapeOfList [decide (value first < value second)]) ((first.length : ℤ) - 1) out := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom,
    run_scan ip first second out same _ le_rfl, List.take_length,
    show second.take first.length = second by rw [same, List.take_length],
    step_frontier ip _ _ _ _ out _ (by simp), blank_write]

theorem run_rewind (ip : Fin (input.length + 2)) (first second out : List Bool)
    (result : ℤ → Option Bool) (flag : Bool) (count : ℕ) (within : count ≤ first.length) :
    machine.runFrom
        (cfg (some (true, flag)) ip (tapeOfList first) (tapeOfList second)
          result ((first.length : ℤ) - 1) out) count =
      cfg (some (true, flag)) ip (tapeOfList first) (tapeOfList second)
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
        step_rewind ip _ _ _ _ out flag _ read]
      congr 1
      push_cast
      ring

/-- Exact numeric result and full final configuration, including all three
head positions and preservation of both input and output. -/
theorem run_complete (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) :
    machine.runFrom (cfg (some (false, false)) ip
        (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out)
        (2 * first.length + 2) =
      cfg none ip (tapeOfList first) (tapeOfList second)
        (tapeOfList [decide (value first < value second)]) 0 out := by
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

/-- Each source may visit its two delimiters; the result head never leaves zero. -/
def visitedWindow (length : ℕ) (tape : Fin 3) : Finset ℤ :=
  if tape = 2 then {0} else Finset.Icc (-1) length

theorem cfg_head_mem_window (state : Option (Bool × Bool))
    (ip : Fin (input.length + 2)) (first second result : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (length : ℕ) (lower : -1 ≤ head)
    (upper : head ≤ length) (tape : Fin 3) :
    (cfg state ip first second result head out).workTapePos tape ∈ visitedWindow length tape := by
  fin_cases tape <;> simp [cfg, visitedWindow, lower, upper]

/-- Every prefix, including prefixes after halting, has both source heads in
`[-1,L]` and the result head at zero. -/
theorem head_in_window (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) (steps : ℕ) (tape : Fin 3) :
    (machine.runFrom (cfg (some (false, false)) ip
      (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out)
      steps).workTapePos tape ∈ visitedWindow first.length tape := by
  by_cases scanning : steps ≤ first.length
  · rw [run_scan ip first second out same steps scanning]
    exact cfg_head_mem_window _ _ _ _ _ _ _ _ (by omega) (by omega) tape
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
      exact cfg_head_mem_window _ _ _ _ _ _ _ _ (by omega) (by omega) tape
    · have finished := run_complete ip first second out same
      rw [runFrom_eq_of_halt _ _ (by omega : 2 * first.length + 2 ≤ steps)
        (by rw [finished]; rfl), finished]
      exact cfg_head_mem_window _ _ _ _ _ _ _ _ (by omega) (by omega) tape

/-- The bound sums actual visited cells over all three work tapes, for every
finite run path starting with the two words and a blank result tape. -/
theorem every_prefix_space (ip : Fin (input.length + 2)) (first second out : List Bool)
    (same : first.length = second.length) (path : machine.RunPath input)
    (initial : path.head = cfg (some (false, false)) ip
      (tapeOfList first) (tapeOfList second) (fun _ => none) 0 out) :
    path.space ≤ 2 * (first.length + 2) + 1 := by
  have bound := path.space_le_sum_card (S := visitedWindow first.length)
    (by
      intro c hc i
      obtain ⟨j, rfl⟩ := hc
      rw [runPath_apply_eq_runFrom, initial]
      exact head_in_window ip first second out same j.val i)
  have size : (Finset.Icc (-1 : ℤ) (first.length : ℤ)).card = first.length + 2 := by
    rw [Int.card_Icc]
    omega
  simpa [visitedWindow, Fin.sum_univ_succ, size, show
    first.length + 2 + (first.length + 2 + 1) = 2 * (first.length + 2) + 1 by omega]
    using bound

/-- A comparison macro in normal form. The length equality and blank result
tape are explicit preconditions. Both sources are preserved and all three heads
reset to zero. The singleton result is the numeric comparison, including false
for two empty words and whenever the numeric values are equal. -/
theorem transforms_compare (L : ℕ) :
    TransformsTapes machine
      (fun _ ws => (ws 0).length ≤ L ∧ (ws 0).length = (ws 1).length ∧ ws 2 = [])
      (fun _ ws ws' emitted => ws' 0 = ws 0 ∧ ws' 1 = ws 1 ∧
        ws' 2 = [decide (value (ws 0) < value (ws 1))] ∧ emitted = [])
      (2 * L + 2) (2 * (L + 2) + 1) := by
  intro input ws out pre
  let begin := wordsCfg input (some machine.q₀) ws out
  have begin_eq : begin = cfg (some (false, false)) 1
      (tapeOfList (ws 0)) (tapeOfList (ws 1)) (fun _ => none) 0 out := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [begin, wordsCfg, cfg, pre.2.2]
    · funext i
      simp [begin, wordsCfg, cfg]
    · rfl
  let path := MultiTapeNTM.RunPath.ofDeterministic machine begin (2 * (ws 0).length + 2)
  let finalWords : Fin 3 → List Bool := fun i =>
    if i = 0 then ws 0 else if i = 1 then ws 1 else [decide (value (ws 0) < value (ws 1))]
  refine ⟨finalWords, [], ⟨rfl, rfl, rfl, rfl⟩, path, rfl, ?_, ?_, ?_⟩
  · change machine.runFrom begin (2 * (ws 0).length + 2) = _
    rw [begin_eq, run_complete 1 (ws 0) (ws 1) out pre.2.1, List.append_nil]
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [cfg, wordsCfg, finalWords]
    · funext i
      simp [cfg, wordsCfg]
    · rfl
  · change 2 * (ws 0).length + 2 ≤ 2 * L + 2
    omega
  · have bound := every_prefix_space (input := input) 1 (ws 0) (ws 1) out pre.2.1 path begin_eq
    exact bound.trans (by omega)

end NtimeDspace.CompareRegistersMachine
