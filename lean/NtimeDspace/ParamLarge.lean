import NtimeDspace.SeedSpec
import NtimeDspace.NetFacts
import NtimeDspace.ParamTerm
import NtimeDspace.Polylog

/-!
# A balanced seed exists for large networks

For an admissible block network with `N` edges and degree at most
`C·log₂ t ≤ C·log₂ N`, the conditions of the balanced-schedule theorem hold
with `a = 2` and `b = maxDegree` once `cost 6 ≤ log₂ N`,
`(2·(log₂ N + 1))³ ≤ N` and `((2 + C)·(log₂ N + 1))⁴ ≤ N` (`exists_balN_network`).
-/

namespace NtimeDspace.ProgTerm

open Parameters WeightedSystem NetworkSystem Placement Cslib.Circuits.Frontier

/-- The group condition: `2·Q·(2^k)² ≤ N`. -/
theorem group_condition (N : ℕ) (hlarge : ParameterChoice.cost 6 ≤ N.log2)
    (hpoly : (2 * (N.log2 + 1)) ^ 3 ≤ N) :
    2 * Q (ParameterChoice.choose N) * (2 ^ ParameterChoice.choose N) ^ 2 ≤ N := by
  set kk := ParameterChoice.choose N
  have hadm := ParameterChoice.admissible N
  have six := ParameterChoice.six_le_selected N hlarge
  unfold ParameterChoice.cost at hadm
  have hs2 : s kk ^ 2 ≤ N.log2 := by
    have : s kk ^ 2 ≤ 16 * s kk ^ 2 * kk ^ 2 := by
      have : 1 ≤ 16 * kk ^ 2 := by nlinarith
      calc s kk ^ 2 = s kk ^ 2 * 1 := by ring
        _ ≤ s kk ^ 2 * (16 * kk ^ 2) := Nat.mul_le_mul_left _ this
        _ = 16 * s kk ^ 2 * kk ^ 2 := by ring
    exact this.trans hadm
  have hk : kk ≤ N.log2 := (ParameterChoice.selected_le_log2 N)
  have e : 2 * Q kk * (2 ^ kk) ^ 2 = 2 * (s kk ^ 2) * (s kk ^ 2) * kk := by
    unfold Q s; ring
  rw [e]
  calc 2 * s kk ^ 2 * s kk ^ 2 * kk ≤ 2 * N.log2 * N.log2 * N.log2 := by gcongr
    _ ≤ (2 * (N.log2 + 1)) ^ 3 := by
        have h1 : N.log2 * N.log2 * N.log2 ≤ (N.log2 + 1) ^ 3 := by
          calc N.log2 * N.log2 * N.log2 = N.log2 ^ 3 := by ring
            _ ≤ (N.log2 + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have h2 : (2 * (N.log2 + 1)) ^ 3 = 8 * (N.log2 + 1) ^ 3 := by ring
        have h3 : 2 * N.log2 * N.log2 * N.log2 = 2 * (N.log2 * N.log2 * N.log2) := by ring
        omega
    _ ≤ N := hpoly

/-- The incidence condition: `(2 + b)·D² ≤ N`. -/
theorem incidence_condition (N b C : ℕ) (hlarge : ParameterChoice.cost 6 ≤ N.log2)
    (hb : b ≤ C * N.log2) (hpoly : ((2 + C) * (N.log2 + 1)) ^ 4 ≤ N) :
    (2 + b) * D (ParameterChoice.choose N) ^ 2 ≤ N := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      simp [ParameterChoice.cost, Parameters.s] at hlarge
    · exact h
  have hD8 := D_pow_eight_le N (ParameterChoice.choose N) hN (ParameterChoice.admissible N)
  have hbC : 2 + b ≤ (2 + C) * (N.log2 + 1) := by nlinarith
  have h4 : ((2 + b) * D (ParameterChoice.choose N) ^ 2) ^ 4 ≤ N ^ 4 := by
    calc ((2 + b) * D (ParameterChoice.choose N) ^ 2) ^ 4
        = (2 + b) ^ 4 * D (ParameterChoice.choose N) ^ 8 := by ring
      _ ≤ N * N := Nat.mul_le_mul ((Nat.pow_le_pow_left hbC 4).trans hpoly) hD8
      _ = N ^ 2 := by ring
      _ ≤ N ^ 4 := Nat.pow_le_pow_right hN (by norm_num)
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h4

/-- **A balanced seed number exists** for a large admissible network. -/
theorem exists_balN_network (d : ExplicitTensorNetwork ℕ) (r C : ℕ) (pos : 0 < d.numEdges)
    (hrows : d.IsRowsFirstBipartite r) (hdeg : d.maxDegree ≤ C * d.numEdges.log2)
    (hlarge : ParameterChoice.cost 6 ≤ d.numEdges.log2)
    (hpoly1 : (2 * (d.numEdges.log2 + 1)) ^ 3 ≤ d.numEdges)
    (hpoly2 : ((2 + C) * (d.numEdges.log2 + 1)) ^ 4 ≤ d.numEdges) :
    ∃ sd < 2 ^ (2 * blk (Q (ParameterChoice.choose d.numEdges)) (ParameterChoice.choose d.numEdges)
        (WSchedulePlacement.inputBits (toSystem d pos))),
      balN (toSystem d pos) (Q (ParameterChoice.choose d.numEdges))
        (ParameterChoice.choose d.numEdges) sd := by
  set N := d.numEdges
  set kk := ParameterChoice.choose N
  have six := ParameterChoice.six_le_selected N hlarge
  have hinc := incidenceCount_eq_two_mul d pos hrows
  refine exists_balN (toSystem d pos) (Q kk) kk (Q_pos kk (by omega)) 2 (d.maxDegree : ℚ)
    (by positivity) (fun v => by rw [bucketCount_variable d pos hrows v])
    (fun e => bucketCount_constraint_le d pos e) pos (by rw [hinc]; omega) ?_ ?_
  · have hic := incidence_condition N d.maxDegree C hlarge hdeg hpoly2
    have e : ((2 ^ kk : ℕ) ^ (2 * Q kk) : ℚ) = (D kk : ℚ) := by
      simp [D, s]
    rw [e, hinc]
    have : ((2 + d.maxDegree) * D kk ^ 2 : ℕ) ≤ N := hic
    have hq : ((2 + d.maxDegree : ℕ) : ℚ) * (D kk : ℚ) ^ 2 ≤ N := by exact_mod_cast this
    push_cast at hq ⊢
    linarith
  · have hg := group_condition N hlarge hpoly1
    exact_mod_cast hg

end NtimeDspace.ProgTerm
