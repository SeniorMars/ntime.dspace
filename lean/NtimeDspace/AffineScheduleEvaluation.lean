import NtimeDspace.SpectralIndexing
import NtimeDspace.GroupedAssignmentEvaluation

/-!
# Scalar binary encoding and affine schedules

Binary vectors are bit accessors. Their inverse encoding uses a scalar sum of
place values. Affine coordinates likewise use a scalar sum; decoding a group
never executes the chosen inverse from the algebraic schedule specification.
The joint seed layout gives each matrix entry and offset its own bit position.
These arithmetic procedures do not assert machine-space bounds.
-/

namespace NtimeDspace.AffineScheduleEvaluation

open scoped BigOperators
open GroupedAssignmentEvaluation HashSchedules

variable {bits inputBits Q : ℕ}

/-- Read one bit without constructing a vector. -/
def binaryDecode (mask : Fin (2 ^ bits)) : Fin bits → ZMod 2 :=
  fun bit => if mask.val.testBit bit.val then 1 else 0

theorem binaryDecode_eq (mask : Fin (2 ^ bits)) :
    binaryDecode mask = SchedulePlacement.binaryCode (Nat.le_refl _) mask := rfl

theorem binaryDecode_val (mask : Fin (2 ^ bits)) (bit : Fin bits) :
    (binaryDecode mask bit).val = mask.val / 2 ^ bit.val % 2 := by
  have bound : mask.val / 2 ^ bit.val % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [binaryDecode, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  split_ifs with odd
  · simp only [ZMod.val_one]
    omega
  · simp only [ZMod.val_zero]
    omega

/-- Encode an accessor using one scalar sum, with no stored bit collection. -/
def binaryValue (vector : Fin bits → ZMod 2) : ℕ :=
  scanSum (fun bit => (vector bit).val * 2 ^ bit.val) 0

theorem binaryValue_decode (mask : Fin (2 ^ bits)) : binaryValue (binaryDecode mask) = mask.val := by
  rw [binaryValue, scanSum_correct, add_zero]
  simp_rw [binaryDecode_val]
  rw [Fin.sum_univ_eq_sum_range (fun bit => mask.val / 2 ^ bit % 2 * 2 ^ bit),
    SpectralIndexing.radix_sum, Nat.mod_eq_of_lt mask.isLt]

theorem binaryValue_lt (vector : Fin bits → ZMod 2) : binaryValue vector < 2 ^ bits := by
  obtain ⟨mask, same⟩ := (SchedulePlacement.binaryEquiv bits).surjective vector
  change binaryDecode mask = vector at same
  rw [← same, binaryValue_decode]
  exact mask.isLt

def binaryEncode (vector : Fin bits → ZMod 2) : Fin (2 ^ bits) :=
  ⟨binaryValue vector, binaryValue_lt vector⟩

theorem binaryEncode_decode (mask : Fin (2 ^ bits)) : binaryEncode (binaryDecode mask) = mask :=
  Fin.ext (binaryValue_decode mask)

theorem binaryDecode_encode (vector : Fin bits → ZMod 2) :
    binaryDecode (binaryEncode vector) = vector := by
  obtain ⟨mask, same⟩ := (SchedulePlacement.binaryEquiv bits).surjective vector
  change binaryDecode mask = vector at same
  rw [← same, binaryEncode_decode]

theorem binaryEncode_eq (vector : Fin bits → ZMod 2) :
    binaryEncode vector = (SchedulePlacement.binaryEquiv bits).symm vector := by
  apply (SchedulePlacement.binaryEquiv bits).injective
  exact (binaryDecode_encode vector).trans (by simp)

/-- Both directions of this equivalence are explicit scalar procedures. -/
def binaryEquiv (bits : ℕ) : Fin (2 ^ bits) ≃ (Fin bits → ZMod 2) where
  toFun := binaryDecode
  invFun := binaryEncode
  left_inv := binaryEncode_decode
  right_inv := binaryDecode_encode

/-- Evaluate one affine output coordinate, retaining only its scalar sum. -/
def affineValue (seed : AffineSeed (Fin inputBits) (Fin Q × Fin bits) (ZMod 2))
    (input : Fin inputBits → ZMod 2) (output : Fin Q × Fin bits) : ZMod 2 :=
  scanSum (fun coordinate => seed.1 output coordinate * input coordinate) (seed.2 output)

theorem affineValue_correct (seed : AffineSeed (Fin inputBits) (Fin Q × Fin bits) (ZMod 2))
    (input : Fin inputBits → ZMod 2) (output : Fin Q × Fin bits) :
    affineValue seed input output = affineEval seed input output := by
  rw [affineValue, scanSum_correct]
  rfl

/-- Decode one node's output block into its ordinary group index. -/
def group (seed : AffineSeed (Fin inputBits) (Fin Q × Fin bits) (ZMod 2))
    (input : Fin inputBits → ZMod 2) (node : Fin Q) : Fin (2 ^ bits) :=
  binaryEncode (fun bit => affineValue seed input (node, bit))

theorem group_correct (seed : AffineSeed (Fin inputBits) (Fin Q × Fin bits) (ZMod 2))
    (input : Fin inputBits → ZMod 2) (node : Fin Q) :
    group seed input node = (SchedulePlacement.binaryEquiv bits).symm
      (fun bit => affineEval seed input (node, bit)) := by
  unfold group
  simp only [affineValue_correct, binaryEncode_eq]

end NtimeDspace.AffineScheduleEvaluation
