import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
import Mathlib.Tactic

/-!
A concrete one-work-tape binary incrementer. Bits are stored least significant
first. Its sole live control state carries one: a one becomes zero and the head
moves right; a zero or blank becomes one and the machine halts. It leaves the
head at the resolved carry, so rewinding is a separate operation.

The bounds below concern actual CSLib configurations and visited tape cells,
including the final head position. They do not claim that the paper's complete
counter has been compiled.
-/

namespace NtimeDspace.BinaryCounterMachine

open Turing Turing.MultiTapeTM

/-- The control state has no unbounded data; all numeric data live on the tape. -/
def machine : MultiTapeTM 1 Bool Unit :=
  .ofTr () fun _ _ work =>
    if work 0 = some true then
      ⟨0, fun _ => (some (some false), 1), none, some ()⟩
    else
      ⟨0, fun _ => (some (some true), 0), none, none⟩

variable {input : List Bool}

def cfg (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) : Cfg 1 Bool Unit input :=
  ⟨some (), ip, fun _ => tape, fun _ => head, out⟩

/-- Tape after clearing the first `count` carry bits, with every other cell
unchanged. This is a semantic description, not a buffer allocated by the machine. -/
def cleared (tape : ℤ → Option Bool) (start : ℤ) (count : ℕ) : ℤ → Option Bool :=
  fun z => if start ≤ z ∧ z < start + count then some false else tape z

theorem cleared_zero (tape : ℤ → Option Bool) (start : ℤ) :
    cleared tape start 0 = tape := by
  funext z
  simp [cleared]

theorem cleared_frontier (tape : ℤ → Option Bool) (start : ℤ) (count : ℕ) :
    cleared tape start count (start + count) = tape (start + count) := by
  simp [cleared]

theorem cleared_succ (tape : ℤ → Option Bool) (start : ℤ) (count : ℕ) :
    Function.update (cleared tape start count) (start + count) (some false) =
      cleared tape start (count + 1) := by
  funext z
  simp only [Function.update_apply, cleared, Nat.cast_add, Nat.cast_one]
  split_ifs <;> first | rfl | omega

theorem step_one (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : tape head = some true) :
    machine.step (cfg ip tape head out) =
      cfg ip (Function.update tape head (some false)) (head + 1) out := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, bit]

theorem step_stop (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (head : ℤ) (out : List Bool) (bit : tape head ≠ some true) :
    machine.step (cfg ip tape head out) =
      ⟨none, ip, fun _ => Function.update tape head (some true), fun _ => head, out⟩ := by
  rw [step_of_state rfl]
  simp [machine, cfg, Action.apply, Cfg.workTapeSymbols, bit]

/-- After each proper carry step the head advances by one and exactly the
traversed one bits have become zero. -/
theorem run_carry (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (start : ℤ) (out : List Bool) (count : ℕ)
    (ones : ∀ j < count, tape (start + j) = some true) :
    machine.runFrom (cfg ip tape start out) count =
      cfg ip (cleared tape start count) (start + count) out := by
  induction count with
  | zero => simp [runFrom, cleared_zero]
  | succ count ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom,
      ih (fun j hj => ones j (by omega)),
      step_one ip _ _ out (by rw [cleared_frontier]; exact ones count (by omega)),
      cleared_succ]
    simp [Nat.cast_add, Nat.cast_one, add_assoc]

/-- Functional correctness on a tape with a finite initial run of one bits. -/
theorem run_increment (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (start : ℤ) (out : List Bool) (count : ℕ)
    (ones : ∀ j < count, tape (start + j) = some true)
    (stop : tape (start + count) ≠ some true) :
    machine.runFrom (cfg ip tape start out) (count + 1) =
      ⟨none, ip,
        fun _ => Function.update (cleared tape start count) (start + count) (some true),
        fun _ => start + count, out⟩ := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom,
    run_carry ip tape start out count ones, step_stop]
  rwa [cleared_frontier]

/-- Every prefix, including prefixes after halting, stays in the same fixed
interval. Repeated visits cannot increase this interval. -/
theorem head_in_interval (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (start : ℤ) (out : List Bool) (count : ℕ)
    (ones : ∀ j < count, tape (start + j) = some true)
    (stop : tape (start + count) ≠ some true) (steps : ℕ) :
    (machine.runFrom (cfg ip tape start out) steps).workTapePos 0 ∈
      Set.Icc start (start + count) := by
  by_cases early : steps ≤ count
  · rw [run_carry ip tape start out steps (fun j hj => ones j (by omega))]
    simp only [cfg, Set.mem_Icc]
    constructor <;> omega
  · have finish := run_increment ip tape start out count ones stop
    rw [runFrom_eq_of_halt _ _ (by omega : count + 1 ≤ steps)
      (by rw [finish]), finish]
    simp only [Set.mem_Icc, le_add_iff_nonneg_right, Nat.cast_nonneg, le_refl, and_self]

/-- Actual visited-cell bound for every run path starting in the specified
configuration; this is not a bound on nonblank cells or on a returned object. -/
theorem path_space_le (ip : Fin (input.length + 2)) (tape : ℤ → Option Bool)
    (start : ℤ) (out : List Bool) (count : ℕ)
    (ones : ∀ j < count, tape (start + j) = some true)
    (stop : tape (start + count) ≠ some true)
    (path : machine.RunPath input) (initial : path.head = cfg ip tape start out) :
    path.space ≤ count + 1 := by
  have bound := path.space_le_sum_card (S := fun _ => Finset.Icc start (start + count))
    (by
      intro c hc i
      obtain ⟨j, rfl⟩ := hc
      have index : i = 0 := Subsingleton.elim _ _
      rw [index, runPath_apply_eq_runFrom, initial]
      simpa only [Finset.mem_Icc, Set.mem_Icc] using
        head_in_interval ip tape start out count ones stop j.val)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul,
    Int.card_Icc] at bound
  have size : (start + (count : ℤ) + 1 - start).toNat = count + 1 := by omega
  simpa only [size] using bound

/-- Number of low one bits before the first zero or end of the word. -/
def carryLength : List Bool → ℕ
  | true :: bits => carryLength bits + 1
  | _ => 0

/-- Ordinary binary increment, allowing an extra high bit on overflow. -/
def incrementBits : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: incrementBits bits

/-- Numeric interpretation of a little-endian word, including leading zeroes. -/
def value : List Bool → ℕ
  | [] => 0
  | bit :: bits => (if bit then 1 else 0) + 2 * value bits

theorem value_incrementBits (bits : List Bool) :
    value (incrementBits bits) = value bits + 1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => cases bit <;> simp [incrementBits, value, ih] <;> omega

theorem carryLength_le (bits : List Bool) : carryLength bits ≤ bits.length := by
  induction bits with
  | nil => simp [carryLength]
  | cons bit bits ih => cases bit <;> simp [carryLength]; omega

/-- A fixed-width counter can be reused if its next value still fits. Without
this condition an all-one word legitimately grows by one cell. -/
theorem increment_length_le (L : ℕ) (bits : List Bool) (length_bound : bits.length ≤ L)
    (room : value bits + 1 < 2 ^ L) : (incrementBits bits).length ≤ L := by
  induction L generalizing bits with
  | zero =>
      have : bits = [] := List.length_eq_zero_iff.mp (by omega)
      simp [this, value] at room
  | succ L ih =>
      cases bits with
      | nil => simp [incrementBits]
      | cons bit bits =>
          cases bit with
          | false => simpa [incrementBits] using length_bound
          | true =>
              have tail_room : value bits + 1 < 2 ^ L := by
                simp only [value, ↓reduceIte, pow_succ] at room
                omega
              have bound := ih bits (by simpa using length_bound) tail_room
              simpa [incrementBits] using Nat.add_le_add_right bound 1

theorem carry_decomposition (bits : List Bool) :
    ∃ rest, bits = List.replicate (carryLength bits) true ++ rest ∧
      rest.head? ≠ some true := by
  induction bits with
  | nil => exact ⟨[], rfl, by decide⟩
  | cons bit bits ih =>
    cases bit with
    | false => exact ⟨false :: bits, rfl, by simp⟩
    | true =>
      obtain ⟨rest, eq, stop⟩ := ih
      refine ⟨rest, ?_, stop⟩
      simpa [carryLength, List.replicate_succ] using congrArg (true :: ·) eq

theorem incrementBits_replicate (count : ℕ) (rest : List Bool)
    (stop : rest.head? ≠ some true) :
    incrementBits (List.replicate count true ++ rest) =
      List.replicate count false ++ true :: rest.drop 1 := by
  induction count with
  | zero =>
      cases rest with
      | nil => rfl
      | cons b bs => cases b <;> simp_all [incrementBits]
  | succ count ih => simp [List.replicate_succ, incrementBits, ih]

theorem cleared_word (count : ℕ) (rest : List Bool) :
    cleared (tapeOfList (List.replicate count true ++ rest)) 0 count =
      tapeOfList (List.replicate count false ++ rest) := by
  funext z
  cases z with
  | negSucc n => simp [cleared, tapeOfList]
  | ofNat n =>
      by_cases h : n < count <;>
        simp [cleared, tapeOfList, List.getElem?_append, h]

theorem write_frontier (count : ℕ) (rest : List Bool) :
    Function.update (tapeOfList (List.replicate count false ++ rest))
        (count : ℤ) (some true) =
      tapeOfList (List.replicate count false ++ true :: rest.drop 1) := by
  funext z
  cases z with
  | negSucc n => simp [tapeOfList]
  | ofNat n =>
      by_cases h : n < count
      · simp [tapeOfList, List.getElem?_append, h, show n ≠ count by omega]
      · by_cases eq : n = count
        · subst n
          simp [tapeOfList]
        · have gt : count < n := by omega
          have diff : n - count = (n - count - 1) + 1 := by omega
          have ne : Int.ofNat n ≠ (count : ℤ) := by
            change (n : ℤ) ≠ (count : ℤ)
            exact_mod_cast eq
          simp only [Function.update_apply, ne, ↓reduceIte,
            tapeOfList, List.getElem?_append, List.length_replicate, h]
          rw [diff, List.getElem?_cons_succ, List.getElem?_drop]
          simp only [add_comm]

theorem word_ones (count : ℕ) (rest : List Bool) (j : ℕ) (hj : j < count) :
    tapeOfList (List.replicate count true ++ rest) (0 + (j : ℤ)) = some true := by
  simp [tapeOfList, List.getElem?_append, hj]

theorem word_stop (count : ℕ) (rest : List Bool) (stop : rest.head? ≠ some true) :
    tapeOfList (List.replicate count true ++ rest) (0 + (count : ℤ)) ≠ some true := by
  cases rest with
  | nil => simp [tapeOfList]
  | cons b bs => simpa [tapeOfList, List.getElem?_append] using stop

/-- The concrete finite-state machine implements binary increment on every
finite word, preserving the read-only input head and the output. -/
theorem run_word (ip : Fin (input.length + 2)) (bits out : List Bool) :
    machine.runFrom (cfg ip (tapeOfList bits) 0 out) (carryLength bits + 1) =
      ⟨none, ip, fun _ => tapeOfList (incrementBits bits),
        fun _ => (carryLength bits : ℤ), out⟩ := by
  obtain ⟨rest, eq, stop⟩ := carry_decomposition bits
  have tapeEq := congrArg tapeOfList eq
  have result := run_increment ip (tapeOfList bits) 0 out (carryLength bits)
    (by rw [tapeEq]; exact word_ones _ rest) (by rw [tapeEq]; exact word_stop _ rest stop)
  have tapes : Function.update (cleared (tapeOfList bits) 0 (carryLength bits))
      (0 + (carryLength bits : ℤ)) (some true) = tapeOfList (incrementBits bits) := by
    rw [tapeEq, cleared_word, zero_add, write_frontier,
      congrArg incrementBits eq, incrementBits_replicate _ rest stop]
  rw [tapes] at result
  simpa only [zero_add] using result

/-- For an L-bit counter every computation prefix visits at most L+1 cells.
The extra cell is necessary for overflow of an all-one word. -/
theorem word_path_space (ip : Fin (input.length + 2)) (bits out : List Bool)
    (path : machine.RunPath input) (initial : path.head = cfg ip (tapeOfList bits) 0 out) :
    path.space ≤ bits.length + 1 := by
  obtain ⟨rest, eq, stop⟩ := carry_decomposition bits
  have tapeEq := congrArg tapeOfList eq
  have bound := path_space_le ip (tapeOfList bits) 0 out (carryLength bits)
    (by rw [tapeEq]; exact word_ones _ rest) (by rw [tapeEq]; exact word_stop _ rest stop) path initial
  exact bound.trans (Nat.add_le_add_right (carryLength_le bits) 1)

end NtimeDspace.BinaryCounterMachine
