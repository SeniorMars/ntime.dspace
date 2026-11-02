import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.FieldTheory.Finite.Basic

/-!
# Modular exponentiation in globally linear work space

The runtime repeats modular multiplication on a three-register state. It does
not construct the unreduced natural power. Modulus zero is handled explicitly:
both the seed and each transition use accumulator zero. Consequently malformed
zero-modulus inputs cannot cause the iteration state to grow with the exponent.

The space certificate below constructs an actual finite-control CSLib machine
through the checked arithmetic and bounded-iteration combinators. The bound is
linear in the complete binary encoding of `(modulus, base, exponent)`; this is
not a time bound or a bound in the logarithm of that encoding length.
-/

namespace NtimeDspace.ModularPowerSpace

open Turing Turing.MultiTapeTM ComputableInSpace

abbrev Triple := ℕ × ℕ × ℕ

def encTriple : Triple ↪ List Bool := encPair encNat (encPair encNat encNat)

def seed (p a : ℕ) : Triple := (p, a, if p = 0 then 0 else 1 % p)

def step (state : Triple) : Triple :=
  (state.1, state.2.1, if state.1 = 0 then 0 else state.2.2 * state.2.1 % state.1)

/-- Repeated reduced multiplication, with no natural-power operation in its
executing definition. The number of repetitions is the encoded exponent. -/
def power (p a e : ℕ) : ℕ := (step^[e] (seed p a)).2.2

theorem iterate_seed (p a e : ℕ) :
    step^[e] (seed p a) = (p, a, if p = 0 then 0 else a ^ e % p) := by
  induction e with
  | zero => simp [seed]
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases zero : p = 0
    · simp [step, zero]
    · simp [step, zero, pow_succ, Nat.mul_mod]

theorem power_correct (p a e : ℕ) : power p a e = if p = 0 then 0 else a ^ e % p := by
  unfold power
  rw [iterate_seed]

theorem power_correct_of_ne_zero (p a e : ℕ) (nonzero : p ≠ 0) :
    power p a e = a ^ e % p := by simp [power_correct, nonzero]

theorem power_zero_modulus (a e : ℕ) : power 0 a e = 0 := by simp [power_correct]

theorem power_lt_modulus (p a e : ℕ) (positive : 0 < p) : power p a e < p := by
  rw [power_correct_of_ne_zero p a e (Nat.ne_of_gt positive)]
  exact Nat.mod_lt _ positive

/-- Every accumulator is reduced, including the explicit zero-modulus case. -/
theorem accumulator_le_modulus (p a e : ℕ) : (step^[e] (seed p a)).2.2 ≤ p := by
  rw [iterate_seed]
  dsimp only
  split_ifs with zero
  · omega
  · exact Nat.le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero zero))

theorem encTriple_length (input : Triple) :
    (encTriple input).length = 2 * (encNat input.1).length +
      2 * (encNat input.2.1).length + (encNat input.2.2).length + 2 := by
  simp only [encTriple, length_encPair]
  omega

/-- A bound on all iteration states, independent of the number of repetitions.
It covers every natural input, without primality or positive-modulus premises. -/
theorem iterate_encoding_length (input : Triple) (iterations : ℕ) :
    (encTriple (step^[iterations] (seed input.1 input.2.1))).length ≤
      2 * ((encTriple input).length + 1) := by
  have reduced := accumulator_le_modulus input.1 input.2.1 iterations
  have digits : (encNat (step^[iterations] (seed input.1 input.2.1)).2.2).length ≤
      (encNat input.1).length := by
    simp only [length_encNat_eq_size]
    exact Nat.size_le_size reduced
  rw [encTriple_length, encTriple_length]
  rw [iterate_seed] at digits ⊢
  dsimp only at digits ⊢
  omega

private theorem first_inSpace :
    ComputableInSpace (fun input : Triple => input.1) encTriple encNat
      (fun input => (encTriple input).length) := fst _ _

private theorem pair_inSpace :
    ComputableInSpace (fun input : Triple => input.2) encTriple (encPair encNat encNat)
      (fun input => (encTriple input).length) := snd _ _

private theorem second_inSpace :
    ComputableInSpace (fun input : Triple => input.2.1) encTriple encNat
      (fun input => (encTriple input).length) := fst' pair_inSpace

private theorem third_inSpace :
    ComputableInSpace (fun input : Triple => input.2.2) encTriple encNat
      (fun input => (encTriple input).length) := snd' pair_inSpace

/-- The transition has a global linear-space certificate, even on states that
are not reduced or not reachable from a seed. -/
theorem step_inSpace :
    ComputableInSpace step encTriple encTriple (fun state => (encTriple state).length) := by
  have accumulator := budget_ite (budget_natIsZero first_inSpace)
    (budget_const (encB := encNat) 0 (.refl _))
    (budget_natMod (budget_natMul third_inSpace second_inSpace) first_inSpace)
  apply (budget_prod first_inSpace (budget_prod second_inSpace accumulator)).of_enc_eq
  intro state
  simp only [step, encTriple, decide_eq_true_eq]

theorem seed_inSpace :
    ComputableInSpace (fun input : Triple => seed input.1 input.2.1) encTriple encTriple
      (fun input => (encTriple input).length) := by
  have accumulator := budget_ite (budget_natIsZero first_inSpace)
    (budget_const (encB := encNat) 0 (.refl _))
    (budget_natMod (budget_const 1 (.refl _)) first_inSpace)
  apply (budget_prod first_inSpace (budget_prod second_inSpace accumulator)).of_enc_eq
  intro input
  simp only [seed, encTriple, decide_eq_true_eq]

theorem iterate_inSpace :
    ComputableInSpace (fun input : Triple => step^[input.2.2] (seed input.1 input.2.1))
      encTriple encTriple (fun input => (encTriple input).length) := by
  exact budget_iterate third_inSpace seed_inSpace step_inSpace
    (B := fun input => 2 * ((encTriple input).length + 1))
    (fun input iterations _ => iterate_encoding_length input iterations) (linear_mul 2)

/-- One finite-control CSLib machine computes modular exponentiation on all
binary triples in work space linear in the complete input encoding. There is
no assumed arithmetic callback or bound on the numerical exponent. -/
theorem power_inSpace :
    ComputableInSpace (fun input : Triple => power input.1 input.2.1 input.2.2)
      encTriple encNat (fun input => (encTriple input).length) :=
  snd' (snd' iterate_inSpace)

theorem power_cast (p a e : ℕ) (nonzero : p ≠ 0) :
    (power p a e : ZMod p) = (a : ZMod p) ^ e := by
  rw [power_correct_of_ne_zero p a e nonzero, ZMod.natCast_mod, Nat.cast_pow]

/-- Zero is sent to zero before the Fermat exponent is used. In particular the
prime-two, zero-residue case does not evaluate `0^0` as an inverse. -/
def inverse (p a : ℕ) : ℕ := if a % p = 0 then 0 else power p a (p - 2)

theorem inverse_lt_modulus (p a : ℕ) (positive : 0 < p) : inverse p a < p := by
  unfold inverse
  split_ifs
  · exact positive
  · exact power_lt_modulus p a (p - 2) positive

/-- This implementation is globally linear-space on every natural input pair;
primality is required only by the algebraic correctness theorem below. -/
theorem inverse_inSpace :
    ComputableInSpace (fun input : ℕ × ℕ => inverse input.1 input.2)
      (encPair encNat encNat) encNat
      (fun input => (encPair encNat encNat input).length) := by
  have modulus := fst encNat encNat
  have base := snd encNat encNat
  have exponent := budget_natSub modulus (budget_const (encB := encNat) 2 (.refl _))
  have arguments := budget_prod modulus (budget_prod base exponent)
  have powered := budget_comp_linear power_inSpace arguments
  have isZero := budget_natIsZero (budget_natMod base modulus)
  apply (budget_ite isZero (budget_const (encB := encNat) 0 (.refl _)) powered).of_enc_eq
  intro input
  simp only [inverse, decide_eq_true_eq]

/-- For a prime modulus the computed natural residue casts to the exact field
inverse, including zero. No nonzero-input premise is hidden in this statement. -/
theorem inverse_cast (p a : ℕ) [Fact p.Prime] :
    (inverse p a : ZMod p) = (a : ZMod p)⁻¹ := by
  have prime : p.Prime := Fact.out
  by_cases zero : a % p = 0
  · have castZero : (a : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff a p).mpr (Nat.dvd_of_mod_eq_zero zero)
    simp [inverse, zero, castZero]
  · have castNonzero : (a : ZMod p) ≠ 0 := by
      intro equality
      exact zero (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff a p).mp equality))
    rw [inverse, ite_eq_right zero, power_cast p a (p - 2) prime.ne_zero]
    apply (mul_eq_one_iff_eq_inv₀ castNonzero).mp
    rw [← pow_succ]
    have exponent : p - 2 + 1 = p - 1 := by have := prime.two_le; omega
    rw [exponent]
    exact ZMod.pow_card_sub_one_eq_one castNonzero

end NtimeDspace.ModularPowerSpace
