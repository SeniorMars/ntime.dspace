import NtimeDspace.ResidueArithmetic
import NtimeDspace.ModularBinomial

/-!
# Uniform reciprocal-coefficient leaf arithmetic

The executing loop has four natural registers: modulus, multiplicity,
descending index, and reduced accumulator. It constructs neither a natural
binomial coefficient nor an unreduced natural power. Zero-modulus guards
make the iteration bounds valid for all encoded inputs. The field identities
require primality only; the machine-space certificates are global.

These certificates implement the arithmetic of one reciprocal leaf. Fetching
the indexed factor and storing the surrounding convolution stack are separate.
-/

namespace NtimeDspace.ReciprocalLeafSpace

open Turing Turing.MultiTapeTM ComputableInSpace
open ResidueArithmetic

abbrev Quad := ℕ × ℕ × ℕ × ℕ

def encQuad : Quad ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))

/-- Normalize the initial accumulator; modulus zero has the bounded default 0. -/
def binomialSeed (p multiplicity index accumulator : ℕ) : Quad :=
  (p, multiplicity, index, if p = 0 then 0 else normalize p accumulator)

/-- One descending iteration. Every multiplication is reduced separately. -/
def binomialStep (state : Quad) : Quad :=
  if state.2.2.1 = 0 then state
  else (state.1, state.2.1, state.2.2.1 - 1,
    if state.1 = 0 then 0 else
      mul state.1
        (mul state.1 state.2.2.2 (add state.1 state.2.1 (state.2.2.1 - 1)))
        (inverse state.1 state.2.2.1))

def binomialLoop (p multiplicity index accumulator : ℕ) : ℕ :=
  (binomialStep^[index] (binomialSeed p multiplicity index accumulator)).2.2.2

def binomial (p multiplicity index : ℕ) : ℕ :=
  binomialLoop p multiplicity index 1

def reciprocal (p a multiplicity index : ℕ) : ℕ :=
  mul p
    (mul p (power p (neg p 1) index) (binomial p multiplicity index))
    (power p (inverse p a) (multiplicity + index))

theorem iterate_binomial_cast (p multiplicity index accumulator : ℕ) [Fact p.Prime] :
    ((binomialStep^[index] (p, multiplicity, index, accumulator)).2.2.2 : ZMod p) =
      HermiteRecovery.modularBinomialLoop (multiplicity : ZMod p) index
        (accumulator : ZMod p) := by
  have nonzero : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction index generalizing accumulator with
  | zero => rfl
  | succ index ih =>
    rw [Function.iterate_succ_apply]
    simp only [binomialStep, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ↓reduceIte, Nat.add_sub_cancel, nonzero]
    rw [ih, HermiteRecovery.modularBinomialLoop, mul_cast, mul_cast, add_cast,
      inverse_cast]
    simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]

theorem binomialLoop_cast (p multiplicity index accumulator : ℕ) [Fact p.Prime] :
    (binomialLoop p multiplicity index accumulator : ZMod p) =
      HermiteRecovery.modularBinomialLoop (multiplicity : ZMod p) index
        (accumulator : ZMod p) := by
  have nonzero : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  simp only [binomialLoop, binomialSeed, nonzero, ↓reduceIte]
  rw [iterate_binomial_cast, normalize_cast]

theorem binomial_cast (p multiplicity index : ℕ) [Fact p.Prime] :
    (binomial p multiplicity index : ZMod p) =
      HermiteRecovery.modularBinomial multiplicity index := by
  simpa only [binomial, HermiteRecovery.modularBinomial, Nat.cast_one] using
    binomialLoop_cast p multiplicity index 1

theorem reciprocal_cast (p a multiplicity index : ℕ) [Fact p.Prime] :
    (reciprocal p a multiplicity index : ZMod p) =
      HermiteRecovery.modularReciprocalCoefficient (a : ZMod p) multiplicity index := by
  have prime : p.Prime := Fact.out
  rw [reciprocal, mul_cast, mul_cast, power_cast p _ _ prime.ne_zero,
    power_cast p _ _ prime.ne_zero, neg_cast p 1 prime.pos, binomial_cast, inverse_cast]
  simp only [Nat.cast_one, HermiteRecovery.modularReciprocalCoefficient]

def Bounds (p multiplicity index : ℕ) (state : Quad) : Prop :=
  state.1 = p ∧ state.2.1 = multiplicity ∧ state.2.2.1 ≤ index ∧ state.2.2.2 ≤ p

theorem seed_bounds (p multiplicity index accumulator : ℕ) :
    Bounds p multiplicity index (binomialSeed p multiplicity index accumulator) := by
  refine ⟨rfl, rfl, le_rfl, ?_⟩
  dsimp only [binomialSeed]
  split_ifs with zero
  · omega
  · exact (normalize_lt_modulus p accumulator (Nat.pos_of_ne_zero zero)).le

theorem step_bounds (p multiplicity index : ℕ) (state : Quad)
    (bounds : Bounds p multiplicity index state) :
    Bounds p multiplicity index (binomialStep state) := by
  obtain ⟨modulus, coefficient, remaining, accumulator⟩ := bounds
  unfold binomialStep
  split_ifs with finished zero
  · exact ⟨modulus, coefficient, remaining, accumulator⟩
  · exact ⟨modulus, coefficient, by dsimp; omega, by dsimp; omega⟩
  · refine ⟨modulus, coefficient, by dsimp; omega, ?_⟩
    exact modulus ▸ (mul_lt_modulus _ _ _ (Nat.pos_of_ne_zero zero)).le

theorem iterate_bounds (p multiplicity index accumulator iterations : ℕ) :
    Bounds p multiplicity index
      (binomialStep^[iterations] (binomialSeed p multiplicity index accumulator)) := by
  induction iterations with
  | zero => exact seed_bounds p multiplicity index accumulator
  | succ iterations ih =>
    rw [Function.iterate_succ_apply']
    exact step_bounds p multiplicity index _ ih

theorem binomialLoop_le_modulus (p multiplicity index accumulator : ℕ) :
    binomialLoop p multiplicity index accumulator ≤ p :=
  (iterate_bounds p multiplicity index accumulator index).2.2.2

theorem binomialLoop_zero_modulus (multiplicity index accumulator : ℕ) :
    binomialLoop 0 multiplicity index accumulator = 0 :=
  Nat.eq_zero_of_le_zero (binomialLoop_le_modulus 0 multiplicity index accumulator)

theorem binomialLoop_lt_modulus (p multiplicity index accumulator : ℕ) (positive : 0 < p) :
    binomialLoop p multiplicity index accumulator < p := by
  have seed : (binomialSeed p multiplicity index accumulator).2.2.2 < p := by
    simpa [binomialSeed, positive.ne'] using normalize_lt_modulus p accumulator positive
  have preserves : ∀ state : Quad, state.1 = p → state.2.2.2 < p →
      (binomialStep state).1 = p ∧ (binomialStep state).2.2.2 < p := by
    intro state same small
    unfold binomialStep
    split_ifs with finished zero
    · exact ⟨same, small⟩
    · exact ⟨same, positive⟩
    · exact ⟨same, same ▸ mul_lt_modulus _ _ _ (Nat.pos_of_ne_zero zero)⟩
  have invariant : ∀ iterations,
      (binomialStep^[iterations] (binomialSeed p multiplicity index accumulator)).1 = p ∧
      (binomialStep^[iterations] (binomialSeed p multiplicity index accumulator)).2.2.2 < p := by
    intro iterations
    induction iterations with
    | zero => exact ⟨rfl, seed⟩
    | succ iterations ih =>
      rw [Function.iterate_succ_apply']
      exact preserves _ ih.1 ih.2
  exact (invariant index).2

theorem reciprocal_lt_modulus (p a multiplicity index : ℕ) (positive : 0 < p) :
    reciprocal p a multiplicity index < p := mul_lt_modulus _ _ _ positive

theorem reciprocal_zero_modulus (a multiplicity index : ℕ) :
    reciprocal 0 a multiplicity index = 0 := by
  simp [reciprocal, ResidueArithmetic.power_zero_modulus, ResidueArithmetic.mul_zero_modulus]

theorem reciprocal_le_modulus (p a multiplicity index : ℕ) :
    reciprocal p a multiplicity index ≤ p := by
  by_cases zero : p = 0
  · simp [zero, reciprocal_zero_modulus]
  · exact (reciprocal_lt_modulus p a multiplicity index (Nat.pos_of_ne_zero zero)).le

/-- The returned natural is the canonical representative, not only a value
congruent to the required field coefficient. -/
theorem reciprocal_eq_val (p a multiplicity index : ℕ) [Fact p.Prime] :
    reciprocal p a multiplicity index =
      (HermiteRecovery.modularReciprocalCoefficient (a : ZMod p) multiplicity index).val := by
  have value := congrArg ZMod.val (reciprocal_cast p a multiplicity index)
  rw [ZMod.val_natCast_of_lt
    (reciprocal_lt_modulus p a multiplicity index (Fact.out : p.Prime).pos)] at value
  exact value

theorem encQuad_length (input : Quad) :
    (encQuad input).length = 2 * (encNat input.1).length +
      2 * (encNat input.2.1).length + 2 * (encNat input.2.2.1).length +
      (encNat input.2.2.2).length + 3 := by
  simp only [encQuad, length_encPair]
  omega

/-- All iterations have bounded encoding length, without a prime, positivity,
reduced-input, or iteration-count premise. -/
theorem iterate_encoding_length (input : Quad) (iterations : ℕ) :
    (encQuad (binomialStep^[iterations]
      (binomialSeed input.1 input.2.1 input.2.2.1 input.2.2.2))).length ≤
        2 * ((encQuad input).length + 1) := by
  obtain ⟨modulus, coefficient, remaining, accumulator⟩ :=
    iterate_bounds input.1 input.2.1 input.2.2.1 input.2.2.2 iterations
  have remainingDigits := Nat.size_le_size remaining
  have accumulatorDigits := Nat.size_le_size accumulator
  simp only [← length_encNat_eq_size] at remainingDigits accumulatorDigits
  rw [encQuad_length, encQuad_length, modulus, coefficient]
  omega

private theorem first_inSpace :
    ComputableInSpace (fun x : Quad => x.1) encQuad encNat
      (fun x => (encQuad x).length) := fst _ _

private theorem rest_inSpace :
    ComputableInSpace (fun x : Quad => x.2) encQuad ResidueArithmetic.encTriple
      (fun x => (encQuad x).length) := snd _ _

private theorem second_inSpace :
    ComputableInSpace (fun x : Quad => x.2.1) encQuad encNat
      (fun x => (encQuad x).length) := fst' rest_inSpace

private theorem lastPair_inSpace :
    ComputableInSpace (fun x : Quad => x.2.2) encQuad encPairNat
      (fun x => (encQuad x).length) := snd' rest_inSpace

private theorem third_inSpace :
    ComputableInSpace (fun x : Quad => x.2.2.1) encQuad encNat
      (fun x => (encQuad x).length) := fst' lastPair_inSpace

private theorem fourth_inSpace :
    ComputableInSpace (fun x : Quad => x.2.2.2) encQuad encNat
      (fun x => (encQuad x).length) := snd' lastPair_inSpace

theorem binomialStep_inSpace :
    ComputableInSpace binomialStep encQuad encQuad (fun x => (encQuad x).length) := by
  have previous := budget_natSub third_inSpace (budget_const (encB := encNat) 1 (.refl _))
  have numerator := budget_comp_linear add_inSpace
    (budget_prod first_inSpace (budget_prod second_inSpace previous))
  have product := budget_comp_linear mul_inSpace
    (budget_prod first_inSpace (budget_prod fourth_inSpace numerator))
  have inverted := budget_comp_linear inverse_inSpace
    (budget_prod first_inSpace third_inSpace)
  have divided := budget_comp_linear mul_inSpace
    (budget_prod first_inSpace (budget_prod product inverted))
  have guarded := budget_ite (budget_natIsZero first_inSpace)
    (budget_const (encB := encNat) 0 (.refl _)) divided
  have advanced := budget_prod first_inSpace
    (budget_prod second_inSpace (budget_prod previous guarded))
  have unchanged := budget_prod first_inSpace
    (budget_prod second_inSpace (budget_prod third_inSpace fourth_inSpace))
  apply (budget_ite (budget_natIsZero third_inSpace) unchanged advanced).of_enc_eq
  intro state
  simp only [binomialStep, decide_eq_true_eq, encQuad]

theorem binomialSeed_inSpace :
    ComputableInSpace (fun input : Quad =>
      binomialSeed input.1 input.2.1 input.2.2.1 input.2.2.2)
      encQuad encQuad (fun input => (encQuad input).length) := by
  have reduced := budget_comp_linear normalize_inSpace
    (budget_prod first_inSpace fourth_inSpace)
  have guarded := budget_ite (budget_natIsZero first_inSpace)
    (budget_const (encB := encNat) 0 (.refl _)) reduced
  apply (budget_prod first_inSpace
    (budget_prod second_inSpace (budget_prod third_inSpace guarded))).of_enc_eq
  intro input
  simp only [binomialSeed, decide_eq_true_eq, encQuad]

theorem binomialIterate_inSpace :
    ComputableInSpace (fun input : Quad => binomialStep^[input.2.2.1]
      (binomialSeed input.1 input.2.1 input.2.2.1 input.2.2.2))
      encQuad encQuad (fun input => (encQuad input).length) := by
  exact budget_iterate third_inSpace binomialSeed_inSpace binomialStep_inSpace
    (B := fun input => 2 * ((encQuad input).length + 1))
    (fun input iterations _ => iterate_encoding_length input iterations) (linear_mul 2)

theorem binomialLoop_inSpace :
    ComputableInSpace (fun input : Quad =>
      binomialLoop input.1 input.2.1 input.2.2.1 input.2.2.2)
      encQuad encNat (fun input => (encQuad input).length) :=
  snd' (snd' (snd' binomialIterate_inSpace))

theorem binomial_inSpace :
    ComputableInSpace (fun input : Triple => binomial input.1 input.2.1 input.2.2)
      ResidueArithmetic.encTriple encNat
      (fun input => (ResidueArithmetic.encTriple input).length) := by
  have modulus := fst encNat (encPair encNat encNat)
  have remaining := snd encNat (encPair encNat encNat)
  have arguments := budget_prod modulus
    (budget_prod (fst' remaining)
      (budget_prod (snd' remaining) (budget_const (encB := encNat) 1 (.refl _))))
  have computed := budget_comp_linear binomialLoop_inSpace arguments
  exact computed

/-- One uniform finite-control machine implements the reciprocal leaf in work
space linear in the full binary tuple. All arithmetic certificates are proved;
factor access is not an unencoded callback to this machine. -/
theorem reciprocal_inSpace :
    ComputableInSpace (fun input : Quad =>
      reciprocal input.1 input.2.1 input.2.2.1 input.2.2.2)
      encQuad encNat (fun input => (encQuad input).length) := by
  have minusOne := budget_comp_linear neg_inSpace
    (budget_prod first_inSpace (budget_const (encB := encNat) 1 (.refl _)))
  have sign := budget_comp_linear power_inSpace
    (budget_prod first_inSpace (budget_prod minusOne fourth_inSpace))
  have choose := budget_comp_linear binomial_inSpace
    (budget_prod first_inSpace (budget_prod third_inSpace fourth_inSpace))
  have signed := budget_comp_linear mul_inSpace
    (budget_prod first_inSpace (budget_prod sign choose))
  have inverted := budget_comp_linear inverse_inSpace
    (budget_prod first_inSpace second_inSpace)
  have powered := budget_comp_linear power_inSpace
    (budget_prod first_inSpace
      (budget_prod inverted (budget_natAdd third_inSpace fourth_inSpace)))
  exact budget_comp_linear mul_inSpace
    (budget_prod first_inSpace (budget_prod signed powered))

end NtimeDspace.ReciprocalLeafSpace
