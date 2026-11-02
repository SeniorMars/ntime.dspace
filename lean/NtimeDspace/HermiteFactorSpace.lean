import NtimeDspace.ResidueArithmetic
import NtimeDspace.ScalarRecoveryLoop

/-!
# Uniform access to the factors of a consecutive-node Hermite weight

The modulus, node count, distinguished node, interpolation order, and queried
slot are binary natural inputs. The accessor computes one pair of natural
registers and constructs neither a factor list nor a field-valued table.
Its space certificate covers every input, including invalid node indices and
zero moduli. Algebraic correctness is asserted for a valid distinguished node.
-/

namespace NtimeDspace.HermiteFactorSpace

open Turing Turing.MultiTapeTM ComputableInSpace

abbrev Input := ℕ × ℕ × ℕ × ℕ × ℕ

def encInput : Input ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat)))

abbrev encFactor : (ℕ × ℕ) ↪ List Bool := ResidueArithmetic.encPairNat

/-- Slot zero is the distinguished node. The following slots enumerate all
other node indices in order; unused slots return the unit factor. -/
def factor (p Q node order : ℕ) : ℕ → ℕ × ℕ
  | 0 => (ResidueArithmetic.normalize p (node + 1), 1)
  | slot + 1 =>
    if slot < Q - 1 then
      let other := if slot < node then slot else slot + 1
      (ResidueArithmetic.sub p (node + 1) (other + 1), order)
    else (ResidueArithmetic.normalize p 1, 1)

private theorem first_inSpace :
    ComputableInSpace (fun input : Input => input.1) encInput encNat
      (fun input => (encInput input).length) := fst _ _

private theorem rest_inSpace :
    ComputableInSpace (fun input : Input => input.2) encInput
      (encPair encNat (encPair encNat (encPair encNat encNat)))
      (fun input => (encInput input).length) := snd _ _

private theorem second_inSpace :
    ComputableInSpace (fun input : Input => input.2.1) encInput encNat
      (fun input => (encInput input).length) := fst' rest_inSpace

private theorem third_inSpace :
    ComputableInSpace (fun input : Input => input.2.2.1) encInput encNat
      (fun input => (encInput input).length) := fst' (snd' rest_inSpace)

private theorem fourth_inSpace :
    ComputableInSpace (fun input : Input => input.2.2.2.1) encInput encNat
      (fun input => (encInput input).length) := fst' (snd' (snd' rest_inSpace))

private theorem fifth_inSpace :
    ComputableInSpace (fun input : Input => input.2.2.2.2) encInput encNat
      (fun input => (encInput input).length) := snd' (snd' (snd' rest_inSpace))

/-- One finite-control machine computes the accessor globally in space linear
in the complete encoded argument. There is no factor-read callback premise. -/
theorem factor_inSpace :
    ComputableInSpace (fun input : Input =>
      factor input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2)
      encInput encFactor (fun input => (encInput input).length) := by
  have one := budget_const (encIn := encInput) (encB := encNat) 1 (.refl _)
  have nodeValue := budget_natSucc third_inSpace
  have normalized := budget_comp_linear ResidueArithmetic.normalize_inSpace
    (budget_prod first_inSpace nodeValue)
  have predecessor := budget_natPred fifth_inSpace
  have other := budget_ite (budget_natLt predecessor third_inSpace)
    predecessor (budget_natSucc predecessor)
  have difference := budget_comp_linear ResidueArithmetic.sub_inSpace
    (budget_prod first_inSpace (budget_prod nodeValue (budget_natSucc other)))
  have defaultValue := budget_comp_linear ResidueArithmetic.normalize_inSpace
    (budget_prod first_inSpace one)
  have following := budget_ite (budget_natLt predecessor (budget_natPred second_inSpace))
    (budget_prod difference fourth_inSpace) (budget_prod defaultValue one)
  apply (budget_ite (budget_natIsZero fifth_inSpace)
    (budget_prod normalized one) following).of_enc_eq
  rintro ⟨p, Q, node, order, slot⟩
  cases slot <;> simp [factor, decide_eq_true_eq, encFactor, ResidueArithmetic.encPairNat]

/-- The explicit natural accessor agrees with every slot of the existing
Hermite-factor specification, including its unused default slots. -/
theorem factor_cast (p Q order slot : ℕ) [Fact p.Prime] (node : Fin Q) :
    (((factor p Q node.val order slot).1 : ZMod p),
      (factor p Q node.val order slot).2) =
      ScalarRecoveryLoop.factorAccessor
        (fun i : Fin Q => ((i.val + 1 : ℕ) : ZMod p)) node order slot := by
  cases slot with
  | zero => simp [factor, ScalarRecoveryLoop.factorAccessor, ResidueArithmetic.normalize_cast]
  | succ slot =>
    by_cases inside : slot < Q - 1
    · simp only [factor, inside, ↓reduceIte, ScalarRecoveryLoop.factorAccessor]
      rw [ResidueArithmetic.sub_cast _ _ _ (Fact.out : p.Prime).pos]
      rfl
    · simp [factor, inside, ScalarRecoveryLoop.factorAccessor, ResidueArithmetic.normalize_cast]

theorem factor_value_lt (p Q node order slot : ℕ) (positive : 0 < p) :
    (factor p Q node order slot).1 < p := by
  cases slot with
  | zero => exact ResidueArithmetic.normalize_lt_modulus _ _ positive
  | succ slot =>
    by_cases inside : slot < Q - 1
    · simpa only [factor, inside, ↓reduceIte] using
        ResidueArithmetic.sub_lt_modulus p (node + 1)
          ((if slot < node then slot else slot + 1) + 1) positive
    · simpa only [factor, inside, ↓reduceIte] using
        ResidueArithmetic.normalize_lt_modulus p 1 positive

theorem factor_multiplicity_le (p Q node order slot : ℕ) :
    (factor p Q node order slot).2 ≤ max 1 order := by
  cases slot with
  | zero => exact le_max_left _ _
  | succ slot =>
    by_cases inside : slot < Q - 1
    · simpa only [factor, inside, ↓reduceIte] using le_max_right 1 order
    · simpa only [factor, inside, ↓reduceIte] using le_max_left 1 order

theorem encInput_length (input : Input) :
    (encInput input).length = 2 * ((encNat input.1).length +
      (encNat input.2.1).length + (encNat input.2.2.1).length +
      (encNat input.2.2.2.1).length) + (encNat input.2.2.2.2).length + 4 := by
  simp only [encInput, length_encPair]
  omega

/-- A bounded scalar envelope includes all five arguments, including the
modulus and the queried index. -/
theorem encInput_length_le (p Q node order slot bound : ℕ)
    (hp : p ≤ bound) (hQ : Q ≤ bound) (hn : node ≤ bound)
    (ho : order ≤ bound) (hs : slot ≤ bound) :
    (encInput (p, Q, node, order, slot)).length ≤ 9 * (bound.log2 + 1) + 4 := by
  have bp := length_encNat_le_log2 hp
  have bQ := length_encNat_le_log2 hQ
  have bn := length_encNat_le_log2 hn
  have bo := length_encNat_le_log2 ho
  have bs := length_encNat_le_log2 hs
  rw [encInput_length]
  dsimp only
  omega

end NtimeDspace.HermiteFactorSpace
