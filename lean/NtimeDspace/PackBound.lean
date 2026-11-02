import NtimeDspace.PackedParser

/-!
# Packed parser states stay below `4·M⁵`

If the bound, the capacity and the zero-run limit are below the radix `M`, the
packed transition maps numbers below `4·M⁵` to numbers below `4·M⁵`, for any
bit and any query. This is the register bound for the parser scan.
-/

namespace NtimeDspace.ParserFold

theorem packFields_lt {M t c r f z a : ℕ} (ht : t < 4) (hc : c < M) (hr : r < M) (hf : f < M)
    (hz : z < M) (ha : a < M) : packFields M t c r f z a < 4 * M ^ 5 := by
  unfold packFields
  have h1 : z + M * a < M ^ 2 := by nlinarith
  have h2 : f + M * (z + M * a) < M ^ 3 := by nlinarith
  have h3 : r + M * (f + M * (z + M * a)) < M ^ 4 := by nlinarith
  have h4 : c + M * (r + M * (f + M * (z + M * a))) < M ^ 5 := by nlinarith
  omega

theorem four_mul_pow_pos {M : ℕ} (hM : 2 ≤ M) : 0 < 4 * M ^ 5 := by
  have : 0 < M ^ 5 := Nat.pow_pos (by omega)
  omega

theorem finishNat_lt {B Cap q M c r f gap : ℕ} (hB : B < M) (hCap : Cap < M) (hM : 2 ≤ M) :
    finishNat B Cap q M c r f gap < 4 * M ^ 5 := by
  unfold finishNat
  by_cases h : 0 < gap ∧ gap ≤ B - c ∧ r < Cap
  · rw [if_pos h]
    exact packFields_lt (by norm_num) (by omega) (by omega) (by split_ifs <;> omega) (by omega)
      (by omega)
  · rw [if_neg h]; exact four_mul_pow_pos hM

theorem prefixNat_lt {B Cap Lb q M c r f z b : ℕ} (hB : B < M) (hCap : Cap < M) (hLb : Lb < M)
    (hM : 2 ≤ M) (hc : c < M) (hr : r < M) (hf : f < M) (hz : z < M) :
    prefixNat B Cap Lb q M c r f z b < 4 * M ^ 5 := by
  have h0 := four_mul_pow_pos hM
  unfold prefixNat
  split_ifs
  · exact packFields_lt (by norm_num) hc hr hf (by omega) (by omega)
  · exact h0
  · exact finishNat_lt hB hCap hM
  · exact packFields_lt (by norm_num) hc hr hf hz (by omega)
  · exact h0

theorem payloadNat_lt {B Cap q M c r f z a b : ℕ} (hB : B < M) (hCap : Cap < M)
    (hM : 2 ≤ M) (hc : c < M) (hr : r < M) (hf : f < M) (hz : z < M) :
    payloadNat B Cap q M c r f z a b < 4 * M ^ 5 := by
  have h0 := four_mul_pow_pos hM
  unfold payloadNat
  split_ifs with h1 h2
  · exact finishNat_lt hB hCap hM
  · exact packFields_lt (by norm_num) hc hr hf (by omega) (by omega)
  · exact h0

theorem stepNat_lt {B Cap Lb q M x b : ℕ} (hB : B < M) (hCap : Cap < M) (hLb : Lb < M)
    (hM : 2 ≤ M) : stepNat B Cap Lb q M x b < 4 * M ^ 5 := by
  have hMpos : 0 < M := by omega
  have hc : x / 4 % M < M := Nat.mod_lt _ hMpos
  have hr : x / 4 / M % M < M := Nat.mod_lt _ hMpos
  have hf : x / 4 / M / M % M < M := Nat.mod_lt _ hMpos
  have hz : x / 4 / M / M / M % M < M := Nat.mod_lt _ hMpos
  have h0 := four_mul_pow_pos hM
  unfold stepNat
  simp only
  split_ifs
  · exact prefixNat_lt hB hCap hLb hM hc hr hf (by omega)
  · exact h0
  · exact prefixNat_lt hB hCap hLb hM hc hr hf hz
  · exact payloadNat_lt hB hCap hM hc hr hf hz
  · exact h0

/-- A packed state below `4·M⁵` whose rank field is at most the capacity. -/
def Good (M Cap x : ℕ) : Prop := x < 4 * M ^ 5 ∧ x / 4 / M % M ≤ Cap

theorem rank_packFields {M t c r f z a : ℕ} (ht : t < 4) (hc : c < M) (hr : r < M) :
    packFields M t c r f z a / 4 / M % M = r := by
  unfold packFields
  have hM : 0 < M := by omega
  rw [show t + 4 * (c + M * (r + M * (f + M * (z + M * a)))) =
      t + 4 * (c + M * (r + M * (f + M * (z + M * a)))) from rfl,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 4), Nat.div_eq_of_lt ht, Nat.zero_add,
    Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hc, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hr]

theorem good_zero {M Cap : ℕ} (hM : 2 ≤ M) : Good M Cap 0 :=
  ⟨four_mul_pow_pos hM, by simp⟩

theorem good_pack {M Cap t c r f z a : ℕ} (hM : 2 ≤ M) (ht : t < 4) (hc : c < M) (hr : r < M)
    (hf : f < M) (hz : z < M) (ha : a < M) (hrc : r ≤ Cap) : Good M Cap (packFields M t c r f z a) :=
  ⟨packFields_lt ht hc hr hf hz ha, by rw [rank_packFields ht hc hr]; exact hrc⟩

theorem finishNat_good {B Cap q M c r f gap : ℕ} (hB : B < M) (hCap : Cap < M) (hM : 2 ≤ M) :
    Good M Cap (finishNat B Cap q M c r f gap) := by
  unfold finishNat
  by_cases h : 0 < gap ∧ gap ≤ B - c ∧ r < Cap
  · rw [if_pos h]
    exact good_pack hM (by norm_num) (by omega) (by omega) (by split_ifs <;> omega) (by omega)
      (by omega) (by omega)
  · rw [if_neg h]; exact good_zero hM

theorem stepNat_good {B Cap Lb q M x b : ℕ} (hB : B < M) (hCap : Cap < M) (hLb : Lb < M)
    (hM : 2 ≤ M) (hx : Good M Cap x) : Good M Cap (stepNat B Cap Lb q M x b) := by
  have hMpos : 0 < M := by omega
  have hc : x / 4 % M < M := Nat.mod_lt _ hMpos
  have hr : x / 4 / M % M < M := Nat.mod_lt _ hMpos
  have hf : x / 4 / M / M % M < M := Nat.mod_lt _ hMpos
  have hz : x / 4 / M / M / M % M < M := Nat.mod_lt _ hMpos
  have hrc := hx.2
  have h0 := good_zero (Cap := Cap) hM
  unfold stepNat
  simp only
  split_ifs
  all_goals first
    | exact h0
    | (unfold prefixNat; split_ifs <;> first
        | exact h0
        | exact finishNat_good hB hCap hM
        | exact good_pack hM (by norm_num) hc hr hf (by omega) (by omega) hrc
        | exact good_pack hM (by norm_num) hc hr hf hz (by omega) hrc)
    | (unfold payloadNat; split_ifs <;> first
        | exact h0
        | exact finishNat_good hB hCap hM
        | exact good_pack hM (by norm_num) hc hr hf (by omega) (by omega) hrc)

end NtimeDspace.ParserFold
