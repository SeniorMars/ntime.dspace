import NtimeDspace.AffineScheduleEvaluation

/-!
# Explicit joint affine-seed encoding

Both affine matrices and both offset families have fixed scalar bit positions.
The decoder reads counter bits on demand, and its inverse encodes the layout
with a scalar place-value scan. No vector table or chosen inverse is executed.
This bijection establishes functional enumeration, not machine-resource bounds.
-/

namespace NtimeDspace.AffineSeedEncoding

open scoped BigOperators
open HashSchedules AffineScheduleEvaluation

variable {bits inputBits Q : ℕ}

/-- Two independent affine matrices and their two offset families. -/
abbrev Seed (inputBits Q bits : ℕ) :=
  AffineSeed (Fin inputBits) (Fin Q × Fin bits) (ZMod 2) ×
    AffineSeed (Fin inputBits) (Fin Q × Fin bits) (ZMod 2)

def totalBits (inputBits Q bits : ℕ) : ℕ := 2 * Q * bits * (inputBits + 1)

abbrev SeedCoordinate (inputBits Q bits : ℕ) :=
  ((Fin 2 × Fin Q) × Fin bits) × Fin (inputBits + 1)

/-- Family, node, output bit, then input slot. The last input slot is the
offset; the others are matrix entries. All maps use arithmetic finite products. -/
def coordinateEquiv (inputBits Q bits : ℕ) :
    SeedCoordinate inputBits Q bits ≃ Fin (totalBits inputBits Q bits) :=
  (Equiv.prodCongr
    ((Equiv.prodCongr (finProdFinEquiv (m := 2) (n := Q)) (Equiv.refl (Fin bits))).trans
      finProdFinEquiv)
    (Equiv.refl (Fin (inputBits + 1)))).trans finProdFinEquiv

def seedSlot (family : Fin 2) (output : Fin Q × Fin bits) (input : Fin (inputBits + 1)) :
    Fin (totalBits inputBits Q bits) :=
  coordinateEquiv inputBits Q bits (((family, output.1), output.2), input)

theorem seedSlot_val (family : Fin 2) (output : Fin Q × Fin bits)
    (input : Fin (inputBits + 1)) :
    (seedSlot family output input).val =
      input.val + (inputBits + 1) * (output.2.val + bits * (output.1.val + Q * family.val)) := rfl

/-- Recover both affine families by reading the specified bit positions. -/
def seedOfVector (vector : Fin (totalBits inputBits Q bits) → ZMod 2) : Seed inputBits Q bits :=
  ((fun output input => vector (seedSlot 0 output input.castSucc),
      fun output => vector (seedSlot 0 output (Fin.last inputBits))),
    (fun output input => vector (seedSlot 1 output input.castSucc),
      fun output => vector (seedSlot 1 output (Fin.last inputBits))))

/-- Read one entry of the flattened seed without constructing its bit vector. -/
def seedVector (seed : Seed inputBits Q bits) : Fin (totalBits inputBits Q bits) → ZMod 2 :=
  fun index =>
    let coordinate := (coordinateEquiv inputBits Q bits).symm index
    let family := if coordinate.1.1.1.val = 0 then seed.1 else seed.2
    let output := (coordinate.1.1.2, coordinate.1.2)
    if matrix : coordinate.2.val < inputBits then
      family.1 output ⟨coordinate.2.val, matrix⟩
    else family.2 output

theorem seedVector_slot (seed : Seed inputBits Q bits) (family : Fin 2)
    (output : Fin Q × Fin bits) (input : Fin (inputBits + 1)) :
    seedVector seed (seedSlot family output input) =
      if matrix : input.val < inputBits then
        (if family.val = 0 then seed.1 else seed.2).1 output ⟨input.val, matrix⟩
      else (if family.val = 0 then seed.1 else seed.2).2 output := by
  simp only [seedVector, seedSlot, Equiv.symm_apply_apply]

theorem seedOfVector_seedVector (seed : Seed inputBits Q bits) :
    seedOfVector (seedVector seed) = seed := by
  apply Prod.ext <;> apply Prod.ext
  · funext output input
    simp [seedOfVector, seedVector_slot]
  · funext output
    simp [seedOfVector, seedVector_slot]
  · funext output input
    simp [seedOfVector, seedVector_slot]
  · funext output
    simp [seedOfVector, seedVector_slot]

theorem seedVector_seedOfVector (vector : Fin (totalBits inputBits Q bits) → ZMod 2) :
    seedVector (seedOfVector vector) = vector := by
  funext index
  obtain ⟨⟨⟨⟨family, node⟩, bit⟩, input⟩, rfl⟩ :=
    (coordinateEquiv inputBits Q bits).surjective index
  change seedVector (seedOfVector vector) (seedSlot family (node, bit) input) = _
  rw [seedVector_slot]
  fin_cases family <;> cases input using Fin.lastCases <;>
    simp [seedOfVector, seedSlot]

/-- Explicit flattening and reconstruction of the entire joint affine seed. -/
def seedVectorEquiv (inputBits Q bits : ℕ) :
    Seed inputBits Q bits ≃ (Fin (totalBits inputBits Q bits) → ZMod 2) where
  toFun := seedVector
  invFun := seedOfVector
  left_inv := seedOfVector_seedVector
  right_inv := seedVector_seedOfVector

/-- Enumerate a joint seed by a single natural binary counter. -/
def seedDecode (mask : Fin (2 ^ totalBits inputBits Q bits)) : Seed inputBits Q bits :=
  seedOfVector (binaryDecode mask)

/-- Explicit inverse: scan the joint seed's bit layout into one scalar. -/
def seedEncode (seed : Seed inputBits Q bits) : Fin (2 ^ totalBits inputBits Q bits) :=
  binaryEncode (seedVector seed)

theorem seedEncode_decode (mask : Fin (2 ^ totalBits inputBits Q bits)) :
    seedEncode (seedDecode mask) = mask := by
  rw [seedEncode, seedDecode, seedVector_seedOfVector, binaryEncode_decode]

theorem seedDecode_encode (seed : Seed inputBits Q bits) : seedDecode (seedEncode seed) = seed := by
  rw [seedDecode, seedEncode, binaryDecode_encode, seedOfVector_seedVector]

/-- No chosen inverse occurs in either direction of this seed equivalence. -/
def seedEquiv (inputBits Q bits : ℕ) : Fin (2 ^ totalBits inputBits Q bits) ≃ Seed inputBits Q bits where
  toFun := seedDecode
  invFun := seedEncode
  left_inv := seedEncode_decode
  right_inv := seedDecode_encode

theorem seedDecode_bijective :
    Function.Bijective (seedDecode (inputBits := inputBits) (Q := Q) (bits := bits)) :=
  (seedEquiv inputBits Q bits).bijective

/-- Enumerate all joint seeds with one binary counter and one scalar sum. -/
def sumSeeds {R : Type*} [AddMonoid R] (inputBits Q bits : ℕ)
    (callback : Seed inputBits Q bits → R) (accumulator : R) : R :=
  GroupedAssignmentEvaluation.scanSum (fun mask => callback (seedDecode mask)) accumulator

theorem sumSeeds_correct {R : Type*} [AddCommMonoid R] (inputBits Q bits : ℕ)
    (callback : Seed inputBits Q bits → R) (accumulator : R) :
    sumSeeds inputBits Q bits callback accumulator =
      (∑ seed : Seed inputBits Q bits, callback seed) + accumulator := by
  rw [sumSeeds, GroupedAssignmentEvaluation.scanSum_correct]
  apply congrArg (· + accumulator)
  exact (seedEquiv inputBits Q bits).sum_comp callback

end NtimeDspace.AffineSeedEncoding
