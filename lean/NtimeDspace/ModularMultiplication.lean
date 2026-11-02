import NtimeDspace.BinaryCounterMachine

/-!
The arithmetic invariant for least-significant-bit modular multiplication.
The procedure only adds and reduces residues; multiplication occurs in its
specification. Register-machine refinement is a separate obligation: this
file establishes the invariant to be maintained by that concrete loop.
-/

namespace NtimeDspace.ModularMultiplication

open BinaryCounterMachine

/-- Add the current multiplicand exactly when the current driver bit is one. -/
def addBit (modulus : ℕ) (bit : Bool) (current accumulator : ℕ) : ℕ :=
  if bit then (accumulator + current) % modulus else accumulator % modulus

/-- Residue doubling avoids allocating a full integer product. -/
def double (modulus current : ℕ) : ℕ := (current + current) % modulus

/-- Tail-recursive double-and-add multiplication on a little-endian driver. -/
def loop (modulus : ℕ) : List Bool → ℕ → ℕ → ℕ
  | [], _, accumulator => accumulator % modulus
  | bit :: rest, current, accumulator =>
      loop modulus rest (double modulus current)
        (addBit modulus bit current accumulator)

/-- One round preserves the represented residue, including modulus zero.
For the machine implementation the modulus will be positive. -/
theorem round_invariant (modulus : ℕ) (bit : Bool) (rest : List Bool)
    (current accumulator : ℕ) :
    (addBit modulus bit current accumulator +
      double modulus current * value rest) % modulus =
      (accumulator + current * value (bit :: rest)) % modulus := by
  cases bit <;> simp only [addBit, Bool.false_eq_true, ↓reduceIte, double,
    value]
  · rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod,
      ← Nat.mul_mod, ← Nat.add_mod]
    congr 1
    ring
  · rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod,
      ← Nat.mul_mod, ← Nat.add_mod]
    congr 1
    ring

/-- Full functional correctness of the scalar double-and-add procedure. -/
theorem loop_correct (modulus : ℕ) (bits : List Bool) (current accumulator : ℕ) :
    loop modulus bits current accumulator =
      (accumulator + current * value bits) % modulus := by
  induction bits generalizing current accumulator with
  | nil => simp [loop, value]
  | cons bit rest ih =>
      rw [loop, ih, round_invariant]

/-- Start with a zero accumulator. The result is the product residue. -/
def multiply (modulus multiplicand : ℕ) (multiplier : List Bool) : ℕ :=
  loop modulus multiplier multiplicand 0

theorem multiply_correct (modulus multiplicand : ℕ) (multiplier : List Bool) :
    multiply modulus multiplicand multiplier =
      multiplicand * value multiplier % modulus := by
  simp [multiply, loop_correct]

theorem addBit_lt (modulus : ℕ) (positive : 0 < modulus) (bit : Bool)
    (current accumulator : ℕ) :
    addBit modulus bit current accumulator < modulus := by
  cases bit <;> exact Nat.mod_lt _ positive

theorem double_lt (modulus : ℕ) (positive : 0 < modulus) (current : ℕ) :
    double modulus current < modulus := Nat.mod_lt _ positive

theorem loop_lt (modulus : ℕ) (positive : 0 < modulus) (bits : List Bool)
    (current accumulator : ℕ) :
    loop modulus bits current accumulator < modulus := by
  rw [loop_correct]
  exact Nat.mod_lt _ positive

/-- Word-level state used solely to state the machine loop invariant. -/
structure Registers where
  driver : List Bool
  current : ℕ
  accumulator : ℕ
  deriving DecidableEq

/-- The empty-driver case preserves already reduced registers. -/
def round (modulus : ℕ) (registers : Registers) : Registers :=
  match registers.driver with
  | [] => registers
  | bit :: rest => ⟨rest, double modulus registers.current,
      addBit modulus bit registers.current registers.accumulator⟩

def residue (modulus : ℕ) (registers : Registers) : ℕ :=
  (registers.accumulator + registers.current * value registers.driver) % modulus

theorem round_driver (modulus : ℕ) (registers : Registers) :
    (round modulus registers).driver = registers.driver.tail := by
  cases registers with
  | mk driver current accumulator => cases driver <;> rfl

theorem round_residue (modulus : ℕ) (registers : Registers) :
    residue modulus (round modulus registers) = residue modulus registers := by
  cases registers with
  | mk driver current accumulator =>
      cases driver with
      | nil => rfl
      | cons bit rest => exact round_invariant modulus bit rest current accumulator

/-- The two mutable arithmetic registers remain reduced at every round. -/
theorem round_bounded (modulus : ℕ) (positive : 0 < modulus) (registers : Registers)
    (current_lt : registers.current < modulus)
    (accumulator_lt : registers.accumulator < modulus) :
    (round modulus registers).current < modulus ∧
      (round modulus registers).accumulator < modulus := by
  cases registers with
  | mk driver current accumulator =>
      cases driver with
      | nil => exact ⟨current_lt, accumulator_lt⟩
      | cons bit rest => exact ⟨double_lt _ positive _, addBit_lt _ positive _ _ _⟩

/-- When the driver is empty, the invariant identifies the reduced accumulator
without an extra modular reduction. -/
theorem result_of_empty (modulus : ℕ) (registers : Registers)
    (empty : registers.driver = []) (accumulator_lt : registers.accumulator < modulus) :
    residue modulus registers = registers.accumulator := by
  simp [residue, empty, value, Nat.mod_eq_of_lt accumulator_lt]

end NtimeDspace.ModularMultiplication
