import NtimeDspace.CompareRegistersMachine

/-!
In-place fixed-width normalization in the CSLib multitape model. Tape zero is
the register and tape one is an unchanged word marking the desired width.
The finite control scans the marker, erases exactly its next two register
cells, and rewinds both heads. Thus any register with between `L` and `L+2`
bits becomes its low `L` bits. There is no auxiliary tape to clean afterward.
The arithmetic preservation theorem additionally requires value below `2^L`.
-/

namespace NtimeDspace.NormalizeRegisterMachine

open Turing Turing.MultiTapeTM BinaryCounterMachine

inductive State
  | scan | eraseSecond | align | rewind
  deriving DecidableEq

instance : Fintype State :=
  ⟨{.scan, .eraseSecond, .align, .rewind}, by intro state; cases state <;> simp⟩

/-- The only two writes blank cells `L` and `L+1` of tape zero. The marker is
read but never written; all heads move together. -/
def machine : MultiTapeTM 2 Bool State :=
  .ofTr .scan fun state _ work =>
    match state with
    | .scan =>
        match work 1 with
        | some _ => ⟨0, fun _ => (none, 1), none, some .scan⟩
        | none => ⟨0, fun i => (if i = 0 then some none else none, 1), none, some .eraseSecond⟩
    | .eraseSecond =>
        ⟨0, fun i => (if i = 0 then some none else none, -1), none, some .align⟩
    | .align => ⟨0, fun _ => (none, -1), none, some .rewind⟩
    | .rewind =>
        match work 1 with
        | some _ => ⟨0, fun _ => (none, -1), none, some .rewind⟩
        | none => ⟨0, fun _ => (none, 1), none, none⟩

variable {input : List Bool}

def cfg (state : Option State) (ip : Fin (input.length + 2))
    (source marker : ℤ → Option Bool) (head : ℤ) (out : List Bool) : Cfg 2 Bool State input :=
  ⟨state, ip, fun i => if i = 0 then source else marker, fun _ => head, out⟩

theorem step_scan (ip : Fin (input.length + 2)) (source marker : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) (read : marker head = some bit) :
    machine.step (cfg (some .scan) ip source marker head out) =
      cfg (some .scan) ip source marker (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]

theorem step_first_erase (ip : Fin (input.length + 2)) (source marker : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (read : marker head = none) :
    machine.step (cfg (some .scan) ip source marker head out) =
      cfg (some .eraseSecond) ip (Function.update source head none) marker (head + 1) out := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]
  · funext i
    simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]
  · simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]

theorem step_second_erase (ip : Fin (input.length + 2)) (source marker : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) :
    machine.step (cfg (some .eraseSecond) ip source marker head out) =
      cfg (some .align) ip (Function.update source head none) marker (head - 1) out := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, cfg, Action.apply]
  · simp [machine, cfg, Action.apply]
  · funext i
    fin_cases i <;> simp [machine, cfg, Action.apply]
  · funext i
    simp [machine, cfg, Action.apply, sub_eq_add_neg]
  · simp [machine, cfg, Action.apply]

theorem step_align (ip : Fin (input.length + 2)) (source marker : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) :
    machine.step (cfg (some .align) ip source marker head out) =
      cfg (some .rewind) ip source marker (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, sub_eq_add_neg]

theorem step_rewind (ip : Fin (input.length + 2)) (source marker : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : Bool) (read : marker head = some bit) :
    machine.step (cfg (some .rewind) ip source marker head out) =
      cfg (some .rewind) ip source marker (head - 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read, sub_eq_add_neg]

theorem step_delimiter (ip : Fin (input.length + 2)) (source marker : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (read : marker head = none) :
    machine.step (cfg (some .rewind) ip source marker head out) =
      cfg none ip source marker (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, read]

theorem erase_two_eq_take (source : List Bool) (L : ℕ) (length : source.length ≤ L + 2) :
    Function.update (Function.update (tapeOfList source) (L : ℤ) none)
      ((L : ℤ) + 1) none = tapeOfList (source.take L) := by
  funext z
  cases z with
  | negSucc j => simp [Function.update_apply, tapeOfList]
  | ofNat j =>
      by_cases before : j < L
      · simp [tapeOfList, before,
          show j ≠ L by omega, show (j : ℤ) ≠ (L : ℤ) + 1 by omega]
      · by_cases first : j = L
        · subst j
          simp [tapeOfList]
        · by_cases second : j = L + 1
          · subst j
            simp [tapeOfList]
          · have outside : source.length ≤ j := by omega
            simp [tapeOfList, before, first,
              show (j : ℤ) ≠ (L : ℤ) + 1 by omega, List.getElem?_eq_none outside]

theorem run_scan (ip : Fin (input.length + 2)) (source : ℤ → Option Bool)
    (marker out : List Bool) (count : ℕ) (within : count ≤ marker.length) :
    machine.runFrom (cfg (some .scan) ip source (tapeOfList marker) 0 out) count =
      cfg (some .scan) ip source (tapeOfList marker) count out := by
  induction count with
  | zero => simp [runFrom]
  | succ count ih =>
      have index : count < marker.length := by omega
      have read : tapeOfList marker (count : ℤ) = some marker[count] :=
        List.getElem?_eq_getElem index
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_scan ip _ _ _ out _ read]
      simp

theorem run_first_erase (ip : Fin (input.length + 2)) (source : ℤ → Option Bool)
    (marker out : List Bool) :
    machine.runFrom (cfg (some .scan) ip source (tapeOfList marker) 0 out) (marker.length + 1) =
      cfg (some .eraseSecond) ip (Function.update source (marker.length : ℤ) none)
        (tapeOfList marker) ((marker.length : ℤ) + 1) out := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, run_scan ip source marker out _ le_rfl,
    step_first_erase ip source _ _ out (by simp)]

theorem run_second_erase (ip : Fin (input.length + 2)) (source : ℤ → Option Bool)
    (marker out : List Bool) :
    machine.runFrom (cfg (some .scan) ip source (tapeOfList marker) 0 out) (marker.length + 2) =
      cfg (some .align) ip
        (Function.update (Function.update source (marker.length : ℤ) none)
          ((marker.length : ℤ) + 1) none)
        (tapeOfList marker) marker.length out := by
  rw [show marker.length + 2 = (marker.length + 1) + 1 by omega,
    runFrom, Function.iterate_succ_apply', ← runFrom, run_first_erase, step_second_erase]
  simp

theorem run_to_rewind (ip : Fin (input.length + 2)) (source marker out : List Bool)
    (length : source.length ≤ marker.length + 2) :
    machine.runFrom (cfg (some .scan) ip (tapeOfList source) (tapeOfList marker) 0 out)
        (marker.length + 3) =
      cfg (some .rewind) ip (tapeOfList (source.take marker.length))
        (tapeOfList marker) ((marker.length : ℤ) - 1) out := by
  rw [show marker.length + 3 = (marker.length + 2) + 1 by omega,
    runFrom, Function.iterate_succ_apply', ← runFrom, run_second_erase, step_align,
    erase_two_eq_take source marker.length length]

theorem run_rewind (ip : Fin (input.length + 2)) (source : ℤ → Option Bool)
    (marker out : List Bool) (count : ℕ) (within : count ≤ marker.length) :
    machine.runFrom (cfg (some .rewind) ip source (tapeOfList marker)
        ((marker.length : ℤ) - 1) out) count =
      cfg (some .rewind) ip source (tapeOfList marker)
        ((marker.length : ℤ) - 1 - count) out := by
  induction count with
  | zero => simp [runFrom]
  | succ count ih =>
      have index : marker.length - 1 - count < marker.length := by omega
      have read : tapeOfList marker ((marker.length : ℤ) - 1 - count) =
          some marker[marker.length - 1 - count] := by
        rw [show (marker.length : ℤ) - 1 - count =
          ((marker.length - 1 - count : ℕ) : ℤ) by omega]
        exact List.getElem?_eq_getElem index
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
        step_rewind ip _ _ _ out _ read]
      congr 1
      push_cast
      ring

theorem run_complete (ip : Fin (input.length + 2)) (source marker out : List Bool)
    (length : source.length ≤ marker.length + 2) :
    machine.runFrom (cfg (some .scan) ip (tapeOfList source) (tapeOfList marker) 0 out)
        (2 * marker.length + 4) =
      cfg none ip (tapeOfList (source.take marker.length)) (tapeOfList marker) 0 out := by
  rw [show 2 * marker.length + 4 = (marker.length + 1) + (marker.length + 3) by omega,
    runFrom, Function.iterate_add_apply]
  change machine.runFrom
    (machine.runFrom (cfg (some .scan) ip (tapeOfList source) (tapeOfList marker) 0 out)
      (marker.length + 3)) (marker.length + 1) = _
  rw [run_to_rewind ip source marker out length, runFrom, Function.iterate_succ_apply',
    ← runFrom, run_rewind ip _ marker out _ le_rfl,
    show (marker.length : ℤ) - 1 - marker.length = -1 by omega,
    step_delimiter ip _ _ _ out (by rfl)]
  norm_num

theorem head_in_window (ip : Fin (input.length + 2)) (source marker out : List Bool)
    (length : source.length ≤ marker.length + 2) (steps : ℕ) (tape : Fin 2) :
    (machine.runFrom (cfg (some .scan) ip (tapeOfList source) (tapeOfList marker) 0 out)
      steps).workTapePos tape ∈ Set.Icc (-1) ((marker.length : ℤ) + 1) := by
  by_cases scanning : steps ≤ marker.length
  · rw [run_scan ip _ marker out steps scanning]
    simp only [cfg, Set.mem_Icc]
    constructor <;> omega
  · by_cases first : steps = marker.length + 1
    · rw [first, run_first_erase]
      simp only [cfg, Set.mem_Icc]
      constructor <;> omega
    · by_cases second : steps = marker.length + 2
      · rw [second, run_second_erase]
        simp [cfg]
      · by_cases returning : steps ≤ 2 * marker.length + 3
        · let elapsed := steps - (marker.length + 3)
          have within : elapsed ≤ marker.length := by dsimp [elapsed]; omega
          have split_time : steps = elapsed + (marker.length + 3) := by dsimp [elapsed]; omega
          rw [split_time, runFrom, Function.iterate_add_apply]
          change (machine.runFrom
            (machine.runFrom (cfg (some .scan) ip (tapeOfList source) (tapeOfList marker) 0 out)
              (marker.length + 3)) elapsed).workTapePos tape ∈ _
          rw [run_to_rewind ip source marker out length, run_rewind ip _ marker out elapsed within]
          simp only [cfg, Set.mem_Icc]
          constructor <;> omega
        · have complete := run_complete ip source marker out length
          rw [runFrom_eq_of_halt _ _ (by omega : 2 * marker.length + 4 ≤ steps)
            (by rw [complete]; rfl), complete]
          simp only [cfg, Set.mem_Icc]
          constructor <;> omega

/-- Every computation prefix, including one extending beyond the halt, visits
at most the interval `[-1,L+1]` on each of the two tapes. -/
theorem every_prefix_space (ip : Fin (input.length + 2)) (source marker out : List Bool)
    (length : source.length ≤ marker.length + 2) (path : machine.RunPath input)
    (initial : path.head = cfg (some .scan) ip (tapeOfList source) (tapeOfList marker) 0 out) :
    path.space ≤ 2 * (marker.length + 3) := by
  have bound := path.space_le_sum_card
    (S := fun _ => Finset.Icc (-1 : ℤ) ((marker.length : ℤ) + 1))
    (by
      intro conf member tape
      obtain ⟨j, rfl⟩ := member
      rw [runPath_apply_eq_runFrom, initial]
      simpa only [Finset.mem_Icc, Set.mem_Icc] using
        head_in_window ip source marker out length j.val tape)
  have size : (Finset.Icc (-1 : ℤ) ((marker.length : ℤ) + 1)).card = marker.length + 3 := by
    rw [Int.card_Icc]
    omega
  simpa only [size, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] using bound

/-- Discarding high binary digits preserves a number known to fit within the
retained width. This does not require the original encoding to be minimal. -/
theorem value_take_eq (source : List Bool) (L : ℕ) (small : value source < 2 ^ L) :
    value (source.take L) = value source := by
  by_cases enough : L ≤ source.length
  · have split_value := CompareRegistersMachine.value_append (source.take L) (source.drop L)
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left enough] at split_value
    have high_zero : value (source.drop L) = 0 := by
      by_contra nonzero
      have high_positive : 1 ≤ value (source.drop L) := Nat.one_le_iff_ne_zero.mpr nonzero
      have lower := Nat.mul_le_mul_left (2 ^ L) high_positive
      simp only [Nat.mul_one] at lower
      omega
    rw [high_zero, Nat.mul_zero, Nat.add_zero] at split_value
    exact split_value.symm
  · rw [List.take_of_length_le (by omega : source.length ≤ L)]

/-- Truncate a possibly non-residue scratch word in place. The numeric value
need not be preserved; exact tape contents are, however, completely specified.
The machine is independent of `L`, which is read from the marker tape. -/
theorem transforms_truncate (L : ℕ) :
    TransformsTapes machine
      (fun _ ws => L ≤ (ws 0).length ∧ (ws 0).length ≤ L + 2 ∧ (ws 1).length = L)
      (fun _ ws ws' emitted => ws' 0 = (ws 0).take L ∧ ws' 1 = ws 1 ∧
        (ws' 0).length = L ∧ emitted = [])
      (2 * L + 4) (2 * (L + 3)) := by
  intro input ws out pre
  let begin := wordsCfg input (some machine.q₀) ws out
  have begin_eq : begin = cfg (some .scan) 1 (tapeOfList (ws 0)) (tapeOfList (ws 1)) 0 out := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
    · rfl
  have length : (ws 0).length ≤ (ws 1).length + 2 := by omega
  let path := MultiTapeNTM.RunPath.ofDeterministic machine begin (2 * L + 4)
  let final : Fin 2 → List Bool := fun i => if i = 0 then (ws 0).take L else ws 1
  refine ⟨final, [], ⟨rfl, rfl, ?_, rfl⟩, path, rfl, ?_, le_rfl, ?_⟩
  · exact List.length_take.trans (Nat.min_eq_left pre.1)
  · change machine.runFrom begin (2 * L + 4) = _
    rw [begin_eq, ← pre.2.2, run_complete 1 (ws 0) (ws 1) out length, List.append_nil]
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [cfg, wordsCfg, final, pre.2.2]
    · rfl
    · rfl
  · have bound := every_prefix_space (input := input) 1 (ws 0) (ws 1) out length path begin_eq
    simpa only [pre.2.2] using bound

/-- In-place fixed-width normalization preserves a residue's value, both head
origins, the entire marker word, and the input/output tapes. No scratch remains. -/
theorem transforms_normalize (L : ℕ) :
    TransformsTapes machine
      (fun _ ws => (L ≤ (ws 0).length ∧ (ws 0).length ≤ L + 2 ∧ (ws 1).length = L) ∧
        value (ws 0) < 2 ^ L)
      (fun _ ws ws' emitted => ws' 0 = (ws 0).take L ∧ ws' 1 = ws 1 ∧
        (ws' 0).length = L ∧ value (ws' 0) = value (ws 0) ∧ emitted = [])
      (2 * L + 4) (2 * (L + 3)) := by
  apply (transforms_truncate L).imp (fun _ _ pre => pre.1)
  · intro _ ws ws' emitted pre post
    exact ⟨post.1, post.2.1, post.2.2.1,
      by rw [post.1]; exact value_take_eq (ws 0) L pre.2, post.2.2.2⟩
  · exact le_rfl
  · exact le_rfl

end NtimeDspace.NormalizeRegisterMachine
