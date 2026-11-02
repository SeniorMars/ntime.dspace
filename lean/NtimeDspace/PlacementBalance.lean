import NtimeDspace.PlacementRank

/-!
# Balanced seeds on numbers

`balN` is the balance condition of `WSchedulePlacement.Balanced` stated on seed
numbers and checked by counting: every label bucket and every group bucket is
small. `balN_of_balanced` transfers balance from the spec, and
`exists_seed_number` shows every seed is `seedOf s` for some `s` below
`2^(2 Q bits (IB + 1))`, so the existence of a balanced seed gives a balanced
seed number in range.
-/

namespace NtimeDspace.Placement

open WeightedSystem HashSchedules SchedulePlacement WSchedulePlacement LocalSim

variable {n : ℕ} (S : System n) (Q bits : ℕ)

/-- The label number of an incidence under seed number `s`. -/
def incLabelN (s : ℕ) (inc : Incidence S) : ℕ :=
  labelN Q bits s (inputBits S) (incidenceVariable S inc) inc.1

/-- The balance condition on seed numbers. -/
def balN (s : ℕ) : Prop :=
  (∀ m < (2 ^ bits * 2 ^ bits) ^ Q,
    (∑ inc : Incidence S, if incLabelN S Q bits s inc = m then 1 else 0) *
      (2 ^ bits * 2 ^ bits) ^ Q ≤ 2 * incidenceCount S) ∧
  (∀ node < Q, ∀ g < 2 ^ bits,
    (∑ v ∈ Finset.range n, if grpN Q bits (inputBits S) s 0 node v = g then 1 else 0) * 2 ^ bits ≤
      2 * n)

instance (s : ℕ) : Decidable (balN S Q bits s) := by unfold balN; infer_instance

theorem incLabelN_lt (s : ℕ) (inc : Incidence S) :
    incLabelN S Q bits s inc < (2 ^ bits * 2 ^ bits) ^ Q := by
  apply packDigits_lt (by positivity)
  intro j _
  have h1 := grpN_lt Q bits s (inputBits S) 1 j inc.1
  have h0 := grpN_lt Q bits s (inputBits S) 0 j (incidenceVariable S inc)
  nlinarith

theorem label_injective_lt {m m' : ℕ} (hm : m < (2 ^ bits * 2 ^ bits) ^ Q)
    (hm' : m' < (2 ^ bits * 2 ^ bits) ^ Q)
    (h : SpectralIndexing.label (2 ^ bits) Q (Nat.two_pow_pos bits) m =
      SpectralIndexing.label (2 ^ bits) Q (Nat.two_pow_pos bits) m') : m = m' :=
  congrArg Fin.val (SpectralIndexing.label_injective (2 ^ bits) Q (Nat.two_pow_pos bits)
    (a₁ := ⟨m, hm⟩) (a₂ := ⟨m', hm'⟩) h)

theorem balN_of_balanced (s : ℕ) (hbal : Balanced S bits (seedOf S Q bits s)) : balN S Q bits s := by
  have hpos : (0 : ℚ) < ((2 : ℚ) ^ bits) ^ (2 * Q) := by positivity
  constructor
  · intro m hm
    have h := hbal.1 (SpectralIndexing.label (2 ^ bits) Q (Nat.two_pow_pos bits) m)
    simp only [Fintype.card_fin] at h
    have hcount : HashVariance.bucketCount (incidenceLabel S bits (seedOf S Q bits s))
        (SpectralIndexing.label (2 ^ bits) Q (Nat.two_pow_pos bits) m) =
        ((∑ inc : Incidence S, if incLabelN S Q bits s inc = m then 1 else 0 : ℕ) : ℚ) := by
      unfold HashVariance.bucketCount
      push_cast
      refine Finset.sum_congr rfl fun inc _ => ?_
      have hl := incidenceLabel_seedOf S Q bits s inc
      by_cases he : incLabelN S Q bits s inc = m
      · rw [if_pos he]
        rw [if_pos]
        change (incidenceLabel S bits (seedOf S Q bits s) inc : TensorEvaluation.Label (2 ^ bits) Q) = _
        rw [hl]; unfold incLabelN at he; rw [he]
      · rw [if_neg he, if_neg]
        intro h'
        apply he
        apply label_injective_lt Q bits (incLabelN_lt S Q bits s inc) hm
        change (incidenceLabel S bits (seedOf S Q bits s) inc : TensorEvaluation.Label (2 ^ bits) Q) = _ at h'
        rw [hl] at h'
        exact h'
    rw [hcount, le_div_iff₀ hpos] at h
    have h2 : ((2 : ℚ) ^ bits) ^ (2 * Q) = (((2 ^ bits * 2 ^ bits) ^ Q : ℕ) : ℚ) := by
      push_cast; rw [pow_mul, sq]
    rw [h2] at h
    exact_mod_cast h
  · intro node hnode g hg
    have h := hbal.2 ⟨node, hnode⟩ ⟨g, hg⟩
    have hcount : HashVariance.bucketCount (variableGroup S bits (seedOf S Q bits s) ⟨node, hnode⟩)
        ⟨g, hg⟩ = ((∑ v ∈ Finset.range n,
          if grpN Q bits (inputBits S) s 0 node v = g then 1 else 0 : ℕ) : ℚ) := by
      unfold HashVariance.bucketCount
      push_cast
      rw [← Fin.sum_univ_eq_sum_range (fun v => if grpN Q bits (inputBits S) s 0 node v = g then
        (1 : ℚ) else 0)]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hv := variableGroup_seedOf S Q bits s ⟨node, hnode⟩ v
      by_cases he : grpN Q bits (inputBits S) s 0 node v = g
      · rw [if_pos (Fin.ext (hv.trans he)), if_pos he]
      · rw [if_neg (fun h' => he (hv.symm.trans (congrArg Fin.val h'))), if_neg he]
    rw [hcount, le_div_iff₀ (by positivity)] at h
    exact_mod_cast h

/-! ### Every seed has a number -/

/-- The block length of one map, `Q bits (IB + 1)`. -/
def blk (IB : ℕ) : ℕ := Q * bits * (IB + 1)

/-- The digit at position `p` of the number of `seed`. -/
noncomputable def seedDigit (IB : ℕ) (seed : AffineSeed (Fin IB) (Fin Q × Fin bits) (ZMod 2) ×
    AffineSeed (Fin IB) (Fin Q × Fin bits) (ZMod 2)) (p : ℕ) : ℕ :=
  let h := p / blk Q bits IB
  let rest := p % blk Q bits IB
  let o := rest / (IB + 1)
  let c := rest % (IB + 1)
  if hq : o / bits < Q ∧ o % bits < bits then
    let map := if h = 0 then seed.1 else seed.2
    if hc : c < IB then (map.1 (⟨o / bits, hq.1⟩, ⟨o % bits, hq.2⟩) ⟨c, hc⟩).val
    else (map.2 (⟨o / bits, hq.1⟩, ⟨o % bits, hq.2⟩)).val
  else 0

theorem seedDigit_lt (IB : ℕ) (seed : AffineSeed (Fin IB) (Fin Q × Fin bits) (ZMod 2) ×
    AffineSeed (Fin IB) (Fin Q × Fin bits) (ZMod 2)) (p : ℕ) : seedDigit Q bits IB seed p < 2 := by
  unfold seedDigit
  simp only
  split_ifs <;> first | exact ZMod.val_lt _ | omega

theorem zbit_val_eq (z : ZMod 2) : zbit (decide (z.val = 1)) = z := by
  have h := ZMod.val_lt z
  have hz : z = ((z.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val z).symm
  have : z.val = 0 ∨ z.val = 1 := by omega
  rcases this with h0 | h1
  · rw [hz, h0]; rfl
  · rw [hz, h1]; rfl

theorem seedPos_decode (IB h : ℕ) (hh : h < 2) (node : Fin Q) (b : Fin bits) (c : ℕ) (hc : c ≤ IB) :
    let p := seedPos Q bits IB h (node * bits + b) c
    p / blk Q bits IB = h ∧ p % blk Q bits IB / (IB + 1) = node * bits + b ∧
      p % blk Q bits IB % (IB + 1) = c ∧ (node * bits + b) / bits = node ∧
      (node * bits + b) % bits = b := by
  have hb : 0 < bits := lt_of_le_of_lt (Nat.zero_le _) b.isLt
  have ho : (node : ℕ) * bits + b < Q * bits := by
    have := node.isLt; have := b.isLt; nlinarith
  have hr : ((node : ℕ) * bits + b) * (IB + 1) + c < blk Q bits IB := by
    unfold blk; nlinarith
  have e1 : seedPos Q bits IB h (node * bits + b) c =
      (((node : ℕ) * bits + b) * (IB + 1) + c) + blk Q bits IB * h := by
    unfold seedPos blk; ring
  simp only [e1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr, zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.add_comm,
      Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt b.isLt, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]

theorem exists_seed_number (seed : Seed S (Fin Q) bits) :
    ∃ s < 2 ^ (2 * blk Q bits (inputBits S)), seedOf S Q bits s = seed := by
  set IB := inputBits S
  set d := seedDigit Q bits IB seed
  set s := packDigits 2 d (2 * blk Q bits IB)
  refine ⟨s, packDigits_lt (by norm_num) _ _ fun p _ => seedDigit_lt Q bits IB seed p, ?_⟩
  have hbit : ∀ h < 2, ∀ (node : Fin Q) (b : Fin bits) (c : ℕ), c ≤ IB →
      s.testBit (seedPos Q bits IB h (node * bits + b) c) =
        decide (d (seedPos Q bits IB h (node * bits + b) c) = 1) := by
    intro h hh node b c hc
    have hlt : seedPos Q bits IB h (node * bits + b) c < 2 * blk Q bits IB := by
      obtain ⟨d1, -, -, -, -⟩ := seedPos_decode Q bits IB h hh node b c hc
      have hblk : 0 < blk Q bits IB := by
        unfold blk
        have hQ : 0 < Q := lt_of_le_of_lt (Nat.zero_le _) node.isLt
        have hB : 0 < bits := lt_of_le_of_lt (Nat.zero_le _) b.isLt
        exact Nat.mul_pos (Nat.mul_pos hQ hB) (by omega)
      have := Nat.lt_mul_div_succ (seedPos Q bits IB h (node * bits + b) c) hblk
      rw [d1] at this; nlinarith
    rw [Nat.testBit_eq_decide_div_mod_eq, packDigits_div_pow_mod (by norm_num) _ _
      (fun p _ => seedDigit_lt Q bits IB seed p), if_pos hlt]
  have hdig : ∀ h < 2, ∀ (node : Fin Q) (b : Fin bits) (c : ℕ) (hc : c ≤ IB),
      d (seedPos Q bits IB h (node * bits + b) c) =
        if hc' : c < IB then ((if h = 0 then seed.1 else seed.2).1 (node, b) ⟨c, hc'⟩).val
        else ((if h = 0 then seed.1 else seed.2).2 (node, b)).val := by
    intro h hh node b c hc
    obtain ⟨d1, d2, d3, d4, d5⟩ := seedPos_decode Q bits IB h hh node b c hc
    simp only [d, seedDigit, d1, d2, d3, d4, d5]
    rw [dif_pos ⟨node.isLt, b.isLt⟩]
  apply Prod.ext
  · apply Prod.ext
    · funext o c
      change zbit (s.testBit (seedPos Q bits IB 0 (o.1 * bits + o.2) c)) = _
      rw [hbit 0 (by norm_num) o.1 o.2 c (by omega), hdig 0 (by norm_num) o.1 o.2 c (by omega),
        dif_pos c.isLt, if_pos rfl, zbit_val_eq]
    · funext o
      change zbit (s.testBit (seedPos Q bits IB 0 (o.1 * bits + o.2) IB)) = _
      rw [hbit 0 (by norm_num) o.1 o.2 IB le_rfl, hdig 0 (by norm_num) o.1 o.2 IB le_rfl,
        dif_neg (lt_irrefl _), if_pos rfl, zbit_val_eq]
  · apply Prod.ext
    · funext o c
      change zbit (s.testBit (seedPos Q bits IB 1 (o.1 * bits + o.2) c)) = _
      rw [hbit 1 (by norm_num) o.1 o.2 c (by omega), hdig 1 (by norm_num) o.1 o.2 c (by omega),
        dif_pos c.isLt, if_neg one_ne_zero, zbit_val_eq]
    · funext o
      change zbit (s.testBit (seedPos Q bits IB 1 (o.1 * bits + o.2) IB)) = _
      rw [hbit 1 (by norm_num) o.1 o.2 IB le_rfl, hdig 1 (by norm_num) o.1 o.2 IB le_rfl,
        dif_neg (lt_irrefl _), if_neg one_ne_zero, zbit_val_eq]

end NtimeDspace.Placement
