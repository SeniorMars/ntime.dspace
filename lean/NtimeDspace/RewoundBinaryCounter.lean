import NtimeDspace.BinaryCounterMachine
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork

/-!
The binary increment primitive followed by a rewind, on the same tape. The
finite three-state machine leaves the incremented word with its head at zero,
so the result is a reusable tape transformation. Space is charged to the union
of positions actually visited, not the sum of two allocated buffers.
-/

namespace NtimeDspace.RewoundBinaryCounter

open Turing Turing.MultiTapeTM BinaryCounterMachine

noncomputable def machine : MultiTapeTM 1 Bool (Unit ⊕ RewindWorkState) :=
  BinaryCounterMachine.machine.seq (rewindWork Bool)

theorem carryLength_lt_result_length (bits : List Bool) :
    carryLength bits < (incrementBits bits).length := by
  induction bits with
  | nil => simp [carryLength, incrementBits]
  | cons b bits ih => cases b <;> simp [carryLength, incrementBits]; omega

/-- A single fixed binary machine increments every word of length at most L,
resets its work head, changes neither input nor output, and uses at most 2L+3
steps and L+2 visited cells. The cell at -1 is the rewind delimiter. -/
theorem transforms_increment (L : ℕ) :
    TransformsTapes machine (fun _ ws => (ws 0).length ≤ L)
      (fun _ ws ws' emitted => ws' 0 = incrementBits (ws 0) ∧ emitted = [])
      (2 * L + 3) (L + 2) := by
  unfold machine
  intro input ws out length_bound
  let bits := ws 0
  let c := carryLength bits
  have ws_const : ws = fun _ => bits := by
    funext i
    exact congrArg ws (Subsingleton.elim i 0)
  let ip : Fin (input.length + 2) := 1
  let begin := cfg ip (tapeOfList bits) 0 out
  let middle : Cfg 1 Bool Unit input :=
    ⟨none, ip, fun _ => tapeOfList (incrementBits bits), fun _ => (c : ℤ), out⟩
  let p₀ := MultiTapeNTM.RunPath.ofDeterministic BinaryCounterMachine.machine begin (c + 1)
  have last₀ : p₀.last = middle := run_word ip bits out
  let second : Cfg 1 Bool RewindWorkState input :=
    ⟨some .start, ip, fun _ => tapeOfList (incrementBits bits), fun _ => (c : ℤ), out⟩
  let p₁ := MultiTapeNTM.RunPath.ofDeterministic (rewindWork Bool) second (c + 2)
  have rewind_bound : c ≤ (incrementBits bits).length :=
    Nat.le_of_lt (carryLength_lt_result_length bits)
  have last₁ : p₁.last = wordsCfg input none (fun _ => incrementBits bits) out := by
    exact runFrom_rewindWork_none ip (tapeOfList (incrementBits bits)) out rfl rewind_bound
  obtain ⟨path, start, finish, time, members⟩ :=
    exists_runPath_seq (p₀ := p₀) (p₁ := p₁) (by rw [last₀])
      (by change second = p₀.last.withState (some .start); rw [last₀]; rfl)
      (by rw [last₁]; rfl)
  refine ⟨fun _ => incrementBits bits, [], ⟨rfl, rfl⟩, path, ?_, ?_, ?_, ?_⟩
  · rw [start, ws_const]
    rfl
  · rw [finish, last₁, List.append_nil]
    rfl
  · change path.length ≤ 2 * L + 3
    change path.length ≤ (c + 1) + (c + 2) at time
    have : c ≤ L := (carryLength_le bits).trans length_bound
    omega
  · have all_heads : ∀ conf ∈ path, ∀ i : Fin 1,
        conf.workTapePos i ∈ Finset.Icc (-1 : ℤ) L := by
      intro conf hconf i
      have index : i = 0 := Subsingleton.elim _ _
      rw [index]
      rcases members conf hconf with ⟨left, hleft, same⟩ | ⟨right, hright, same⟩
      · obtain ⟨j, rfl⟩ := hleft
        have pos := congrArg (fun v => v.workTapePos 0) same
        change conf.workTapePos 0 = (p₀ j).workTapePos 0 at pos
        rw [pos]
        obtain ⟨rest, eq, stop⟩ := carry_decomposition bits
        have tapeEq := congrArg tapeOfList eq
        have interval := head_in_interval ip (tapeOfList bits) 0 out c
          (by rw [tapeEq]; exact word_ones _ rest)
          (by rw [tapeEq]; exact word_stop _ rest stop) j.val
        have : c ≤ L := (carryLength_le bits).trans length_bound
        change (BinaryCounterMachine.machine.runFrom begin j.val).workTapePos 0 ∈
          Finset.Icc (-1 : ℤ) L
        simp only [Set.mem_Icc, zero_add] at interval
        simp only [Finset.mem_Icc]
        dsimp [begin]
        constructor <;> omega
      · obtain ⟨j, rfl⟩ := hright
        have pos := congrArg (fun v => v.workTapePos 0) same
        change conf.workTapePos 0 = (p₁ j).workTapePos 0 at pos
        rw [pos]
        have interval := workTapePos_runFrom_rewindWork (Symbol := Bool) none ip
          (tapeOfList (incrementBits bits)) out rfl rewind_bound j.val
        have : c ≤ L := (carryLength_le bits).trans length_bound
        change ((rewindWork Bool).runFrom second j.val).workTapePos 0 ∈
          Finset.Icc (-1 : ℤ) L
        simp only [Set.mem_Icc] at interval
        simp only [Finset.mem_Icc]
        change ((rewindWork Bool).runFrom second j.val).workTapePos 0 ≥ -1 ∧
          ((rewindWork Bool).runFrom second j.val).workTapePos 0 ≤ (L : ℤ)
        exact ⟨interval.1, interval.2.trans (by exact_mod_cast this)⟩
    have space := path.space_le_sum_card all_heads
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul,
      Int.card_Icc] at space
    have size : ((L : ℤ) + 1 - -1).toNat = L + 2 := by omega
    simpa only [size] using space

/-- Reuse within one fixed width requires an explicit no-overflow condition.
The returned word again meets the length invariant and its value increases by
one; this does not silently assume that arbitrary repetitions fit. -/
theorem transforms_bounded_increment (L : ℕ) :
    TransformsTapes machine
      (fun _ ws => (ws 0).length ≤ L ∧ value (ws 0) + 1 < 2 ^ L)
      (fun _ ws ws' emitted => ws' 0 = incrementBits (ws 0) ∧
        (ws' 0).length ≤ L ∧ value (ws' 0) = value (ws 0) + 1 ∧ emitted = [])
      (2 * L + 3) (L + 2) := by
  apply (transforms_increment L).imp
  · intro _ _ h
    exact h.1
  · intro _ ws ws' emitted hP hQ
    refine ⟨hQ.1, ?_, ?_, hQ.2⟩
    · rw [hQ.1]
      exact increment_length_le L (ws 0) hP.1 hP.2
    · rw [hQ.1, value_incrementBits]
  · exact le_rfl
  · exact le_rfl

/-- A halting path of a deterministic machine bounds every run prefix from
the same configuration, including prefixes extending beyond the halt. -/
theorem path_space_le_halting_path {k : ℕ} {State Symbol : Type*}
    {tm : MultiTapeTM k Symbol State} {input : List Symbol}
    (path finished : tm.RunPath input) (same_start : path.head = finished.head)
    (halts : finished.last.Halted) : path.space ≤ finished.space := by
  apply MultiTapeNTM.RunPath.space_le_of_subset
  intro c hc
  obtain ⟨j, rfl⟩ := hc
  by_cases before : j.val ≤ finished.length
  · refine ⟨⟨j.val, by omega⟩, ?_⟩
    rw [runPath_apply_eq_runFrom, runPath_apply_eq_runFrom, same_start]
  · refine ⟨Fin.last finished.length, ?_⟩
    have halted_run : (tm.runFrom finished.head finished.length).Halted := by
      have last_eq := runPath_apply_eq_runFrom finished (Fin.last finished.length)
      change finished.last = tm.runFrom finished.head finished.length at last_eq
      rwa [← last_eq]
    rw [runPath_apply_eq_runFrom, runPath_apply_eq_runFrom, same_start,
      runFrom_eq_of_halt _ _ (by omega : finished.length ≤ j.val) halted_run]
    rfl

/-- The reusable increment specification also controls every computation
prefix, rather than only the one terminating path used to prove correctness. -/
theorem every_prefix_space (L : ℕ) (input : List Bool) (ws : Fin 1 → List Bool)
    (out : List Bool) (length_bound : (ws 0).length ≤ L)
    (path : machine.RunPath input)
    (initial : path.head = wordsCfg input (some machine.q₀) ws out) :
    path.space ≤ L + 2 := by
  obtain ⟨ws', emitted, _, finished, start, stop, _, space⟩ :=
    transforms_increment L input ws out length_bound
  apply (path_space_le_halting_path path finished (initial.trans start.symm) ?_).trans space
  rw [stop]
  rfl

end NtimeDspace.RewoundBinaryCounter
