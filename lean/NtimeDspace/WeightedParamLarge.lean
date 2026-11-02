/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.ParamLarge

-- upstream: local-only (parameters and seed selection for the application's counter)

/-!
# Balanced seeds for general sparse weighted systems

The chosen parameters admit balanced seeds for every sufficiently large weighted
system with at least `N` incidences, occurrence at most three, and logarithmic
arity. The threshold depends only on the arity coefficient, not on a machine
network or on the weights. Occurrence at most three also gives at most `3*N`
incidences.

Polynomially many constraints require only logarithmically many identifier bits.
The explicit seed range then uses quadratically many logarithmic bits. These
results supply the existence premise of `ProgTerm.seed_spec` and `seed_lt`;
accessor correctness and the counter's machine resource bounds are separate.
-/

namespace NtimeDspace.WeightedParamLarge

open Filter Parameters WeightedSystem Placement

variable {N : ℕ}

private theorem constraint_bucketCount (S : System N) (e : Fin S.constraints.length) :
    HashVariance.bucketCount (fun inc : Incidence S => inc.1) e =
      (S.constraints[e]).scope.length := by
  unfold HashVariance.bucketCount
  rw [Fintype.sum_sigma,
    Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- Bounded occurrence counts scope positions, including any repeated variable
within one scope; it therefore bounds the total incidence count. -/
theorem incidenceCount_le_three_mul (S : System N)
    (occurrences : ∀ v, HashVariance.bucketCount (incidenceVariable S) v ≤ 3) :
    incidenceCount S ≤ 3 * N := by
  have hsum : (incidenceCount S : ℚ) ≤ 3 * N := by
    rw [← WSchedulePlacement.card_incidence, ← HashVariance.sum_bucketCount (incidenceVariable S)]
    calc
      _ ≤ ∑ _v : Fin N, (3 : ℚ) := Finset.sum_le_sum fun v _ => occurrences v
      _ = 3 * N := by simp [mul_comm]
  exact_mod_cast hsum

/-- The variance bound needed for occurrence three and logarithmic arity. -/
theorem incidence_condition (N b C : ℕ) (positive : 0 < N)
    (arity : b ≤ C * (N.log2 + 1))
    (polylog : ((6 + 2 * C) * (N.log2 + 1)) ^ 4 ≤ N) :
    2 * (3 + b) * D (ParameterChoice.choose N) ^ 2 ≤ N := by
  have hD := D_pow_eight_le N (ParameterChoice.choose N) positive (ParameterChoice.admissible N)
  have hb : 2 * (3 + b) ≤ (6 + 2 * C) * (N.log2 + 1) := by nlinarith
  have hpow : (2 * (3 + b) * D (ParameterChoice.choose N) ^ 2) ^ 4 ≤ N ^ 4 := by
    calc
      _ = (2 * (3 + b)) ^ 4 * D (ParameterChoice.choose N) ^ 8 := by ring
      _ ≤ N * N := Nat.mul_le_mul ((Nat.pow_le_pow_left hb 4).trans polylog) hD
      _ = N ^ 2 := by ring
      _ ≤ N ^ 4 := Nat.pow_le_pow_right positive (by norm_num)
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hpow

/-- Concrete sufficient conditions for a balanced seed, without a network
representation assumption or a constraint-weight bound. -/
theorem exists_balN_system (S : System N) (C : ℕ) (positive : 0 < N)
    (incidences : N ≤ incidenceCount S)
    (occurrences : ∀ v, HashVariance.bucketCount (incidenceVariable S) v ≤ 3)
    (arity : ∀ e : Fin S.constraints.length,
      (S.constraints[e]).scope.length ≤ C * (N.log2 + 1))
    (large : ParameterChoice.cost 6 ≤ N.log2)
    (polylog1 : (2 * (N.log2 + 1)) ^ 3 ≤ N)
    (polylog2 : ((6 + 2 * C) * (N.log2 + 1)) ^ 4 ≤ N) :
    ∃ sd < 2 ^ (2 * blk (Q (ParameterChoice.choose N)) (ParameterChoice.choose N)
        (WSchedulePlacement.inputBits S)),
      balN S (Q (ParameterChoice.choose N)) (ParameterChoice.choose N) sd := by
  let k := ParameterChoice.choose N
  have hk := ParameterChoice.six_le_selected N large
  refine ProgTerm.exists_balN S (Q k) k (Q_pos k (by omega)) 3
    (C * (N.log2 + 1)) (by positivity) occurrences (fun e => ?_)
    positive (positive.trans_le incidences) ?_ ?_
  · rw [constraint_bucketCount]
    exact_mod_cast arity e
  · have hinc := incidence_condition N (C * (N.log2 + 1)) C positive le_rfl polylog2
    have hD : ((2 ^ k : ℕ) ^ (2 * Q k) : ℚ) = (D k : ℚ) := by
      simp [D, s]
    rw [hD]
    have hbound : ((2 * (3 + C * (N.log2 + 1)) * D k ^ 2 : ℕ) : ℚ) ≤
        (incidenceCount S : ℚ) := by exact_mod_cast hinc.trans incidences
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one] using hbound
  · exact_mod_cast ProgTerm.group_condition N large polylog1

/-- One threshold suffices for all weighted systems with the given arity
coefficient. The seed depends on the scope lists, not on the table weights. -/
theorem eventually_exists_balN_system (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ S : System N,
      N ≤ incidenceCount S →
      (∀ v, HashVariance.bucketCount (incidenceVariable S) v ≤ 3) →
      (∀ e : Fin S.constraints.length,
        (S.constraints[e]).scope.length ≤ C * (N.log2 + 1)) →
      ∃ sd < 2 ^ (2 * blk (Q (ParameterChoice.choose N)) (ParameterChoice.choose N)
          (WSchedulePlacement.inputBits S)),
        balN S (Q (ParameterChoice.choose N)) (ParameterChoice.choose N) sd := by
  filter_upwards [eventually_ge_atTop 1,
    Polylog.tendsto_log2.eventually (eventually_ge_atTop (ParameterChoice.cost 6)),
    Polylog.eventually_polylog_le 2 3,
    Polylog.eventually_polylog_le (6 + 2 * C) 4] with N hpos hlarge hp1 hp2
  intro S hinc hocc harity
  exact exists_balN_system S C hpos hinc hocc harity hlarge hp1 hp2

/-- The numeric first-seed search used by `ProgTerm.seedT`, at the selected
parameters. It depends only on scope information, not on the table entries. -/
def selectedSeed (S : System N) : ℕ :=
  LocalSim.optCode ((List.range (2 ^ (2 * blk (Q (ParameterChoice.choose N))
    (ParameterChoice.choose N) (WSchedulePlacement.inputBits S)))).find?
      fun sd => decide (balN S (Q (ParameterChoice.choose N)) (ParameterChoice.choose N) sd)) - 1

/-- The deterministic finite search selects a balanced seed in its stated range. -/
theorem eventually_selectedSeed_spec (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ S : System N,
      N ≤ incidenceCount S →
      (∀ v, HashVariance.bucketCount (incidenceVariable S) v ≤ 3) →
      (∀ e : Fin S.constraints.length,
        (S.constraints[e]).scope.length ≤ C * (N.log2 + 1)) →
      selectedSeed S < 2 ^ (2 * blk (Q (ParameterChoice.choose N)) (ParameterChoice.choose N)
          (WSchedulePlacement.inputBits S)) ∧
        balN S (Q (ParameterChoice.choose N)) (ParameterChoice.choose N) (selectedSeed S) := by
  filter_upwards [eventually_exists_balN_system C] with N hN
  intro S hinc hocc harity
  exact ProgTerm.find_witness (hN S hinc hocc harity)

/-- Polynomially many constraint identifiers need only logarithmically many
bits, even if zero-arity constraints make their count exceed the incidence count. -/
theorem inputBits_le_of_polynomial (S : System N) (d : ℕ) (positive : 0 < d)
    (constraints : S.constraints.length ≤ (N + 1) ^ d) :
    WSchedulePlacement.inputBits S ≤ d * (N.log2 + 1) + 1 := by
  have hN : N ≤ (N + 1) ^ d := by
    calc
      N ≤ N + 1 := Nat.le_succ _
      _ = (N + 1) ^ 1 := (pow_one _).symm
      _ ≤ (N + 1) ^ d := Nat.pow_le_pow_right (by omega) positive
  have hpow : (N + 1) ^ d ≤ 2 ^ (d * (N.log2 + 1)) := by
    calc
      _ ≤ (2 ^ (N.log2 + 1)) ^ d := Nat.pow_le_pow_left (by
        have := Nat.lt_log2_self (n := N)
        omega) d
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  have hmax : max N S.constraints.length ≤ 2 ^ (d * (N.log2 + 1)) :=
    (max_le hN constraints).trans hpow
  have hlog : (max N S.constraints.length).log2 ≤ (2 ^ (d * (N.log2 + 1))).log2 := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hmax
  rw [Nat.log2_two_pow] at hlog
  exact Nat.add_le_add_right hlog 1

/-- A fixed polynomial identifier range leaves only a quadratic logarithmic
seed-bit budget. The exponent bound is independent of all table weights. -/
theorem seedBits_le_of_polynomial (S : System N) (d : ℕ) (positive : 0 < d)
    (constraints : S.constraints.length ≤ (N + 1) ^ d) :
    2 * blk (Q (ParameterChoice.choose N)) (ParameterChoice.choose N)
      (WSchedulePlacement.inputBits S) ≤ 2 * (d + 2) * (N.log2 + 1) ^ 2 := by
  have hib := inputBits_le_of_polynomial S d positive constraints
  have hlog := schedule_bits_log_budget N (ParameterChoice.choose N) (ParameterChoice.admissible N)
  have hQk : Q (ParameterChoice.choose N) * ParameterChoice.choose N ≤ N.log2 + 1 := by omega
  unfold blk
  calc
    _ ≤ 2 * ((N.log2 + 1) * (d * (N.log2 + 1) + 2)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul hQk (by omega))
    _ ≤ 2 * (d + 2) * (N.log2 + 1) ^ 2 := by nlinarith

end NtimeDspace.WeightedParamLarge
