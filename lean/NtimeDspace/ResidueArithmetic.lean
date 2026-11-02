import NtimeDspace.ModularPowerSpace

/-!
# Uniform binary residue arithmetic

The modulus and operands are natural-number data, encoded in canonical binary.
Every space certificate is global on all encoded pairs or triples; positivity,
primality, and reduced operands are needed only for the algebraic and numerical
bounds. No machine is specialized to a field characteristic.

The certificates construct actual finite-control machines through Complexitylib's
checked arithmetic combinators. They bound work space linearly in the full
encoded argument, without asserting a particular running time.
-/

namespace NtimeDspace.ResidueArithmetic

open Turing Turing.MultiTapeTM ComputableInSpace

abbrev Pair := ℕ × ℕ
abbrev Triple := ModularPowerSpace.Triple

def encPairNat : Pair ↪ List Bool := encPair encNat encNat
abbrev encTriple : Triple ↪ List Bool := ModularPowerSpace.encTriple

def normalize (p a : ℕ) : ℕ := a % p
def add (p a b : ℕ) : ℕ := (a + b) % p
def mul (p a b : ℕ) : ℕ := (a * b) % p

/-- Reducing both operands before the subtraction prevents natural-number
truncation from changing the field difference. -/
def sub (p a b : ℕ) : ℕ := (a % p + p - b % p) % p
def neg (p a : ℕ) : ℕ := (p - a % p) % p

abbrev power (p a e : ℕ) : ℕ := ModularPowerSpace.power p a e
abbrev inverse (p a : ℕ) : ℕ := ModularPowerSpace.inverse p a

/-! These total-function conventions matter when bounding arbitrary callback
states. A loop requiring reduced accumulators must handle modulus zero; the
global certificates below do not assume it has already done so. -/

theorem normalize_zero_modulus (a : ℕ) : normalize 0 a = a := by simp [normalize]

theorem add_zero_modulus (a b : ℕ) : add 0 a b = a + b := by simp [add]

theorem mul_zero_modulus (a b : ℕ) : mul 0 a b = a * b := by simp [mul]

theorem sub_zero_modulus (a b : ℕ) : sub 0 a b = a - b := by simp [sub]

theorem neg_zero_modulus (a : ℕ) : neg 0 a = 0 := by simp [neg]

theorem power_zero_modulus (a e : ℕ) : power 0 a e = 0 :=
  ModularPowerSpace.power_zero_modulus a e

theorem inverse_zero_modulus (a : ℕ) : inverse 0 a = 0 := by
  simp [inverse, ModularPowerSpace.inverse, ModularPowerSpace.power_zero_modulus]

private theorem pairFirst_inSpace :
    ComputableInSpace (fun input : Pair => input.1) encPairNat encNat
      (fun input => (encPairNat input).length) := fst _ _

private theorem pairSecond_inSpace :
    ComputableInSpace (fun input : Pair => input.2) encPairNat encNat
      (fun input => (encPairNat input).length) := snd _ _

private theorem tripleFirst_inSpace :
    ComputableInSpace (fun input : Triple => input.1) encTriple encNat
      (fun input => (encTriple input).length) := fst _ _

private theorem tripleRest_inSpace :
    ComputableInSpace (fun input : Triple => input.2) encTriple encPairNat
      (fun input => (encTriple input).length) := snd _ _

private theorem tripleSecond_inSpace :
    ComputableInSpace (fun input : Triple => input.2.1) encTriple encNat
      (fun input => (encTriple input).length) := fst' tripleRest_inSpace

private theorem tripleThird_inSpace :
    ComputableInSpace (fun input : Triple => input.2.2) encTriple encNat
      (fun input => (encTriple input).length) := snd' tripleRest_inSpace

theorem normalize_inSpace :
    ComputableInSpace (fun input : Pair => normalize input.1 input.2)
      encPairNat encNat (fun input => (encPairNat input).length) :=
  budget_natMod pairSecond_inSpace pairFirst_inSpace

theorem add_inSpace :
    ComputableInSpace (fun input : Triple => add input.1 input.2.1 input.2.2)
      encTriple encNat (fun input => (encTriple input).length) :=
  budget_natMod (budget_natAdd tripleSecond_inSpace tripleThird_inSpace) tripleFirst_inSpace

theorem mul_inSpace :
    ComputableInSpace (fun input : Triple => mul input.1 input.2.1 input.2.2)
      encTriple encNat (fun input => (encTriple input).length) :=
  budget_natMod (budget_natMul tripleSecond_inSpace tripleThird_inSpace) tripleFirst_inSpace

theorem sub_inSpace :
    ComputableInSpace (fun input : Triple => sub input.1 input.2.1 input.2.2)
      encTriple encNat (fun input => (encTriple input).length) :=
  budget_natMod
    (budget_natSub
      (budget_natAdd (budget_natMod tripleSecond_inSpace tripleFirst_inSpace) tripleFirst_inSpace)
      (budget_natMod tripleThird_inSpace tripleFirst_inSpace)) tripleFirst_inSpace

theorem neg_inSpace :
    ComputableInSpace (fun input : Pair => neg input.1 input.2)
      encPairNat encNat (fun input => (encPairNat input).length) :=
  budget_natMod
    (budget_natSub pairFirst_inSpace (budget_natMod pairSecond_inSpace pairFirst_inSpace))
    pairFirst_inSpace

theorem power_inSpace :
    ComputableInSpace (fun input : Triple => power input.1 input.2.1 input.2.2)
      encTriple encNat (fun input => (encTriple input).length) :=
  ModularPowerSpace.power_inSpace

theorem inverse_inSpace :
    ComputableInSpace (fun input : Pair => inverse input.1 input.2)
      encPairNat encNat (fun input => (encPairNat input).length) :=
  ModularPowerSpace.inverse_inSpace

theorem normalize_cast (p a : ℕ) : (normalize p a : ZMod p) = (a : ZMod p) :=
  ZMod.natCast_mod a p

theorem add_cast (p a b : ℕ) : (add p a b : ZMod p) = (a : ZMod p) + (b : ZMod p) := by
  rw [add, ZMod.natCast_mod, Nat.cast_add]

theorem mul_cast (p a b : ℕ) : (mul p a b : ZMod p) = (a : ZMod p) * (b : ZMod p) := by
  rw [mul, ZMod.natCast_mod, Nat.cast_mul]

theorem sub_cast (p a b : ℕ) (positive : 0 < p) :
    (sub p a b : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  have noUnderflow : b % p ≤ a % p + p := by have := Nat.mod_lt b positive; omega
  rw [sub, ZMod.natCast_mod, Nat.cast_sub noUnderflow, Nat.cast_add,
    ZMod.natCast_mod, ZMod.natCast_mod, ZMod.natCast_self, add_zero]

theorem neg_cast (p a : ℕ) (positive : 0 < p) :
    (neg p a : ZMod p) = -(a : ZMod p) := by
  rw [neg, ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt a positive).le,
    ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

theorem power_cast (p a e : ℕ) (nonzero : p ≠ 0) :
    (power p a e : ZMod p) = (a : ZMod p) ^ e :=
  ModularPowerSpace.power_cast p a e nonzero

theorem inverse_cast (p a : ℕ) [Fact p.Prime] :
    (inverse p a : ZMod p) = (a : ZMod p)⁻¹ :=
  ModularPowerSpace.inverse_cast p a

theorem normalize_lt_modulus (p a : ℕ) (positive : 0 < p) : normalize p a < p :=
  Nat.mod_lt _ positive

theorem add_lt_modulus (p a b : ℕ) (positive : 0 < p) : add p a b < p :=
  Nat.mod_lt _ positive

theorem mul_lt_modulus (p a b : ℕ) (positive : 0 < p) : mul p a b < p :=
  Nat.mod_lt _ positive

theorem sub_lt_modulus (p a b : ℕ) (positive : 0 < p) : sub p a b < p :=
  Nat.mod_lt _ positive

theorem neg_lt_modulus (p a : ℕ) (positive : 0 < p) : neg p a < p :=
  Nat.mod_lt _ positive

theorem power_lt_modulus (p a e : ℕ) (positive : 0 < p) : power p a e < p :=
  ModularPowerSpace.power_lt_modulus p a e positive

theorem inverse_lt_modulus (p a : ℕ) (positive : 0 < p) : inverse p a < p :=
  ModularPowerSpace.inverse_lt_modulus p a positive

theorem normalize_eq (p a : ℕ) (reduced : a < p) : normalize p a = a :=
  Nat.mod_eq_of_lt reduced

theorem normalize_idempotent (p a : ℕ) : normalize p (normalize p a) = normalize p a :=
  Nat.mod_mod a p

theorem normalize_val (p a : ℕ) : normalize p a = (a : ZMod p).val :=
  (ZMod.val_natCast p a).symm

theorem encPairNat_length (input : Pair) :
    (encPairNat input).length =
      2 * (encNat input.1).length + (encNat input.2).length + 1 := by
  simp only [encPairNat, length_encPair]
  omega

theorem encTriple_length (input : Triple) :
    (encTriple input).length = 2 * (encNat input.1).length +
      2 * (encNat input.2.1).length + (encNat input.2.2).length + 2 :=
  ModularPowerSpace.encTriple_length input

/-- The input modulus is included in the bound; it is not hidden in finite
control. This statement also covers the zero bound. -/
theorem encPairNat_length_le (p a : ℕ) (bound : a ≤ p) :
    (encPairNat (p, a)).length ≤ 3 * (p.log2 + 1) + 1 := by
  have hp := length_encNat_le_log2 (Nat.le_refl p)
  have ha := length_encNat_le_log2 bound
  rw [encPairNat_length]
  dsimp only
  omega

theorem encTriple_length_le (p a b : ℕ) (first : a ≤ p) (second : b ≤ p) :
    (encTriple (p, a, b)).length ≤ 5 * (p.log2 + 1) + 2 := by
  have hp := length_encNat_le_log2 (Nat.le_refl p)
  have ha := length_encNat_le_log2 first
  have hb := length_encNat_le_log2 second
  rw [encTriple_length]
  dsimp only
  omega

/-- Every canonical output residue has logarithmic encoded width. Combining
this with a global callback certificate requires a reachable-state invariant. -/
theorem residue_encoding_length (p a : ℕ) (reduced : a < p) :
    (encNat a).length ≤ p.log2 + 1 :=
  length_encNat_le_log2 reduced.le

end NtimeDspace.ResidueArithmetic
