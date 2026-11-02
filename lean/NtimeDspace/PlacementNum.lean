import NtimeDspace.MeasTerm
import NtimeDspace.WSchedulePlacement
import NtimeDspace.LocalTape

/-!
# Hash placement on numbers

A seed of `WSchedulePlacement` (two affine maps over `ZMod 2`) is decoded from
a number `s`: bit `seedPos h o c` is coefficient `c` of output `o` of map `h`,
and the bit at coordinate `IB` is the offset. The groups of a variable or a
constraint at a node are then numbers (`grpN`), and the label of an incidence
is the base-`r²` number of its group pairs (`labelN`), with `r = 2^bits`.
-/

namespace NtimeDspace.Placement

open WeightedSystem HashSchedules SchedulePlacement WSchedulePlacement LocalSim

variable {n : ℕ}

/-- The position of coefficient `c` (or the offset, at `c = IB`) of output `o` of map `h`. -/
def seedPos (Q bits IB h o c : ℕ) : ℕ := h * (Q * bits * (IB + 1)) + o * (IB + 1) + c

/-- A bit as an element of `ZMod 2`. -/
def zbit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- One affine map of the seed numbered `s`. -/
def mapOf (Q bits IB s h : ℕ) : AffineSeed (Fin IB) (Fin Q × Fin bits) (ZMod 2) :=
  (fun o c => zbit (s.testBit (seedPos Q bits IB h (o.1 * bits + o.2) c)),
    fun o => zbit (s.testBit (seedPos Q bits IB h (o.1 * bits + o.2) IB)))

/-- The seed numbered `s`. -/
def seedOf (S : System n) (Q bits s : ℕ) : Seed S (Fin Q) bits :=
  (mapOf Q bits (inputBits S) s 0, mapOf Q bits (inputBits S) s 1)

/-- Output bit `j` at `node` of map `h` on the input with binary digits of `x`. -/
def parityN (Q bits IB s h node j x : ℕ) : ℕ :=
  ((∑ c ∈ Finset.range IB, (s.testBit (seedPos Q bits IB h (node * bits + j) c)).toNat *
      (x.testBit c).toNat) + (s.testBit (seedPos Q bits IB h (node * bits + j) IB)).toNat) % 2

/-- The group (a number below `2^bits`) of input `x` at `node` under map `h`. -/
def grpN (Q bits IB s h node x : ℕ) : ℕ :=
  ∑ j ∈ Finset.range bits, parityN Q bits IB s h node j x * 2 ^ j

theorem zbit_val (b : Bool) : (zbit b).val = b.toNat := by cases b <;> rfl

theorem val_natCast_two (m : ℕ) : ((m : ZMod 2)).val = m % 2 := ZMod.val_natCast 2 m

/-- The affine map on the binary code of `x`, as a number. -/
theorem affineEval_binary (Q bits IB s h : ℕ) {size : ℕ} (fits : size ≤ 2 ^ IB) (x : Fin size)
    (o : Fin Q × Fin bits) :
    (affineEval (mapOf Q bits IB s h) (binaryCode fits x) o).val =
      parityN Q bits IB s h o.1 o.2 x := by
  have hcast : affineEval (mapOf Q bits IB s h) (binaryCode fits x) o =
      (((∑ c ∈ Finset.range IB, (s.testBit (seedPos Q bits IB h (o.1 * bits + o.2) c)).toNat *
        ((x : ℕ).testBit c).toNat) + (s.testBit (seedPos Q bits IB h (o.1 * bits + o.2) IB)).toNat :
          ℕ) : ZMod 2) := by
    unfold affineEval mapOf binaryCode
    push_cast
    rw [← Fin.sum_univ_eq_sum_range (fun c => ((s.testBit (seedPos Q bits IB h (o.1 * bits + o.2) c)).toNat : ZMod 2) *
      (((x : ℕ).testBit c).toNat : ZMod 2))]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      simp only [zbit]
      cases s.testBit (seedPos Q bits IB h (o.1 * bits + o.2) c) <;>
        cases (x : ℕ).testBit c <;> simp
    · simp only [zbit]; cases s.testBit (seedPos Q bits IB h (o.1 * bits + o.2) IB) <;> simp
  rw [hcast, val_natCast_two]
  rfl

theorem binaryEquiv_symm_val (bits : ℕ) (f : Fin bits → ZMod 2) :
    ((binaryEquiv bits).symm f : ℕ) =
      ∑ j ∈ Finset.range bits, (if h : j < bits then (f ⟨j, h⟩).val else 0) * 2 ^ j := by
  set x := ∑ j ∈ Finset.range bits, (if h : j < bits then (f ⟨j, h⟩).val else 0) * 2 ^ j
  have hlt : ∀ j < bits, (if h : j < bits then (f ⟨j, h⟩).val else 0) < 2 := by
    intro j hj; rw [dif_pos hj]; exact ZMod.val_lt _
  have hx : x < 2 ^ bits := packDigits_lt (by norm_num) bits _ hlt
  have key : binaryEquiv bits ⟨x, hx⟩ = f := by
    funext bit
    change (if x.testBit bit.val then (1 : ZMod 2) else 0) = f bit
    have hd := packDigits_div_pow_mod (R := 2) (by norm_num) bits _ hlt bit.val
    rw [if_pos bit.isLt, dif_pos bit.isLt] at hd
    have hd' : x / 2 ^ (bit : ℕ) % 2 = (f bit).val := hd
    rw [Nat.testBit_eq_decide_div_mod_eq, hd']
    have hfv : f bit = (((f bit).val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val _).symm
    by_cases h1 : (f bit).val = 1
    · rw [if_pos (by simp [h1]), hfv, h1]; simp
    · have h0 : (f bit).val = 0 := by have := ZMod.val_lt (f bit); omega
      rw [if_neg (by simp [h1]), hfv, h0]; simp
  rw [← key, Equiv.symm_apply_apply]

variable (S : System n) (Q bits s : ℕ)

theorem variableGroup_seedOf (node : Fin Q) (v : Fin n) :
    (WSchedulePlacement.variableGroup S bits (seedOf S Q bits s) node v : ℕ) = grpN Q bits (inputBits S) s 0 node v := by
  unfold WSchedulePlacement.variableGroup grpN
  rw [binaryEquiv_symm_val]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [dif_pos (Finset.mem_range.mp hj)]
  congr 1
  exact affineEval_binary Q bits (inputBits S) s 0 _ v (node, ⟨j, Finset.mem_range.mp hj⟩)

theorem constraintGroup_seedOf (node : Fin Q) (e : Fin S.constraints.length) :
    (WSchedulePlacement.constraintGroup S bits (seedOf S Q bits s) node e : ℕ) =
      grpN Q bits (inputBits S) s 1 node e := by
  unfold WSchedulePlacement.constraintGroup grpN
  rw [binaryEquiv_symm_val]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [dif_pos (Finset.mem_range.mp hj)]
  congr 1
  exact affineEval_binary Q bits (inputBits S) s 1 _ e (node, ⟨j, Finset.mem_range.mp hj⟩)

theorem grpN_lt (IB h node x : ℕ) : grpN Q bits IB s h node x < 2 ^ bits :=
  packDigits_lt (by norm_num) bits _ fun j _ => Nat.mod_lt _ (by norm_num)

/-- The label number of the incidence with variable `v` and constraint `e`. -/
def labelN (IB v e : ℕ) : ℕ :=
  ∑ node ∈ Finset.range Q,
    (grpN Q bits IB s 1 node e + 2 ^ bits * grpN Q bits IB s 0 node v) * (2 ^ bits * 2 ^ bits) ^ node

theorem incidenceLabel_seedOf (inc : Incidence S) :
    (WSchedulePlacement.incidenceLabel S bits (seedOf S Q bits s) inc : TensorEvaluation.Label (2 ^ bits) Q) =
      SpectralIndexing.label (2 ^ bits) Q (Nat.two_pow_pos bits)
        (labelN Q bits s (inputBits S) (incidenceVariable S inc) inc.1) := by
  funext node
  have hcode : ∀ j < Q, grpN Q bits (inputBits S) s 1 j inc.1 +
      2 ^ bits * grpN Q bits (inputBits S) s 0 j (incidenceVariable S inc) < 2 ^ bits * 2 ^ bits := by
    intro j _
    have h1 := grpN_lt Q bits s (inputBits S) 1 j inc.1
    have h0 := grpN_lt Q bits s (inputBits S) 0 j (incidenceVariable S inc)
    nlinarith
  have hdig := packDigits_div_pow_mod (R := 2 ^ bits * 2 ^ bits) (by positivity) Q _ hcode node.val
  rw [if_pos node.isLt] at hdig
  have hpos : 0 < 2 ^ bits := Nat.two_pow_pos bits
  apply Prod.ext
  · apply Fin.ext
    rw [ProgTerm.label_fst]
    change _ = labelN Q bits s (inputBits S) (incidenceVariable S inc) inc.1 /
      (2 ^ bits * 2 ^ bits) ^ (node : ℕ) % (2 ^ bits * 2 ^ bits) / 2 ^ bits
    rw [show labelN Q bits s (inputBits S) (incidenceVariable S inc) inc.1 /
      (2 ^ bits * 2 ^ bits) ^ (node : ℕ) % (2 ^ bits * 2 ^ bits) = _ from hdig]
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (grpN_lt Q bits s _ 1 _ _), zero_add]
    exact variableGroup_seedOf S Q bits s node _
  · apply Fin.ext
    rw [ProgTerm.label_snd]
    change _ = labelN Q bits s (inputBits S) (incidenceVariable S inc) inc.1 /
      (2 ^ bits * 2 ^ bits) ^ (node : ℕ) % (2 ^ bits * 2 ^ bits) % 2 ^ bits
    rw [show labelN Q bits s (inputBits S) (incidenceVariable S inc) inc.1 /
      (2 ^ bits * 2 ^ bits) ^ (node : ℕ) % (2 ^ bits * 2 ^ bits) = _ from hdig]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (grpN_lt Q bits s _ 1 _ _)]
    exact constraintGroup_seedOf S Q bits s node _

end NtimeDspace.Placement
