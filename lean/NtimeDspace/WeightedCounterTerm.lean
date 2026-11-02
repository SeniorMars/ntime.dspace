/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.CounterAssemblyEq
import NtimeDspace.SeedSpec
import NtimeDspace.ArithHelpers
import NtimeDspace.IntegerWindow

-- upstream: local-only (selected-parameter terms for the weighted counting application)

/-!
# Selected parameters for an arbitrary weighted system

The counter reads its variable count, constraint count and modulus through
stable terms, and its scopes and weights through the existing accessor
contracts. No machine, clock or network representation is part of this API.
The term uses the existing parameter choice, support parser and balanced-seed
search. Semantic correctness is separate from bounds on its intermediate values.
-/

namespace NtimeDspace.WeightedCounterTerm

open ProgTerm ProgTerm.Term WeightedSystem Placement

/-- The binary logarithm of the declared number of variables. -/
def lgT (nT : Term) : Term := log2T nT nT

def kT (nT : Term) : Term := chooseT (lgT nT)
def sT (nT : Term) : Term := pow2 (kT nT)
def QT (nT : Term) : Term := mul (mul (sT nT) (sT nT)) (kT nT)
def RT (nT : Term) : Term := mul (mul (const 8) (sT nT)) (kT nT)
def qT (nT : Term) : Term := div (mul (mul (const 3) nT) (RT nT)) (QT nT)
def limitT (nT : Term) : Term :=
  div (sub (add (mul (mul (const 24) nT) (add (mul (const 2) (kT nT)) (const 1)))
    (sT nT)) (const 1)) (sT nT)
def startT (nT : Term) : Term :=
  div (add (mul (mul (sT nT) (kT nT)) (sub (sT nT) (const 9))) (const 1)) (const 2)
def radixT (nT : Term) : Term := add (add (add nT (qT nT)) (lgT nT)) (const 3)

/-- The common identifier width covers both variable and constraint indices. -/
def inputBitsT (nT mT : Term) : Term := add (lgT (maxT nT mT)) (const 1)

/-- Count ordered incidences by summing the constraint arities. -/
def incidenceT (mT : Term) (arity : Term → Term) : Term := sumT mT arity

/-- The number of labels, in the same arithmetic form used by the seed search. -/
def DT (nT : Term) : Term := labelSpaceT (QT nT) (kT nT)

def copiesT (nT mT : Term) (arity : Term → Term) : Term :=
  div (mul (const 2) (incidenceT mT arity)) (DT nT)

/-- Search for the first balanced seed for the supplied incidence accessors. -/
def seedT (nT mT : Term) (arity : Term → Term) (varT : Term → Term → Term) : Term :=
  ProgTerm.seedT (QT nT) (kT nT) (inputBitsT nT mT) nT mT arity
    (fun sd e i => labelT (QT nT) (kT nT) (inputBitsT nT mT) sd (varT e i) e)

/-- The selected-parameter modular counter for a weighted system. -/
def counterT (nT mT pT : Term) (arity : Term → Term)
    (varT weight : Term → Term → Term) : Term :=
  systemCounterT pT (QT nT) (add (qT nT) (const 1)) nT (qT nT)
    (lgT nT) (radixT nT) (limitT nT) nT mT (kT nT) (inputBitsT nT mT)
    (seedT nT mT arity varT) (startT nT) (const 0) (RT nT)
    (copiesT nT mT arity) arity varT weight

variable {w : List Bool} {env : List ℕ} {nT mT : Term}

/-- The self-bounded logarithm term also has its intended value at zero. -/
theorem denote_lgT (hn : StableAt w nT env) :
    (lgT nT).denote w env = (nT.denote w env).log2 := by
  rcases Nat.eq_zero_or_pos (nT.denote w env) with h0 | hpos
  · rw [lgT, log2T, denote_sumT _ _ env (fun _ => 0) (fun acc i => by
      simp only [denote_lt, denote_const, divPowT_denote _ _ _ _ (stableAt_const _ _),
        hn.cons₂, h0, Nat.zero_div, lt_irrefl, ite_false])]
    simp [h0]
  · exact log2T_denote _ _ env hn hpos
      (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))

theorem stable_lgT (hn : StableAt w nT env) : StableAt w (lgT nT) env := fun pre => by
  rw [denote_lgT (hn.extend pre), denote_lgT hn, hn pre]

theorem denote_kT (hn : StableAt w nT env) :
    (kT nT).denote w env = ParameterChoice.choose (nT.denote w env) :=
  denote_chooseT (stable_lgT hn) _ (denote_lgT hn)

theorem stable_kT (hn : StableAt w nT env) : StableAt w (kT nT) env :=
  StableAt.chooseT (stable_lgT hn) _ (denote_lgT hn)

theorem denote_sT (hn : StableAt w nT env) :
    (sT nT).denote w env = Parameters.s (ParameterChoice.choose (nT.denote w env)) := by
  simp [sT, denote_kT hn, Parameters.s]

theorem stable_sT (hn : StableAt w nT env) : StableAt w (sT nT) env := (stable_kT hn).pow2

theorem denote_QT (hn : StableAt w nT env) :
    (QT nT).denote w env = Parameters.Q (ParameterChoice.choose (nT.denote w env)) := by
  simp [QT, denote_sT hn, denote_kT hn, Parameters.Q, pow_two]

theorem stable_QT (hn : StableAt w nT env) : StableAt w (QT nT) env :=
  ((stable_sT hn).mul (stable_sT hn)).mul (stable_kT hn)

theorem denote_RT (hn : StableAt w nT env) :
    (RT nT).denote w env = Parameters.R (ParameterChoice.choose (nT.denote w env)) := by
  simp [RT, denote_sT hn, denote_kT hn, Parameters.R]

theorem stable_RT (hn : StableAt w nT env) : StableAt w (RT nT) env :=
  ((stableAt_const _ _).mul (stable_sT hn)).mul (stable_kT hn)

theorem denote_qT (hn : StableAt w nT env) :
    (qT nT).denote w env = Parameters.q (nT.denote w env)
      (ParameterChoice.choose (nT.denote w env)) := by
  simp [qT, denote_RT hn, denote_QT hn, Parameters.q]

theorem stable_qT (hn : StableAt w nT env) : StableAt w (qT nT) env :=
  (((stableAt_const _ _).mul hn).mul (stable_RT hn)).div (stable_QT hn)

theorem denote_limitT (hn : StableAt w nT env) :
    (limitT nT).denote w env = SupportBudget.limit (nT.denote w env)
      (ParameterChoice.choose (nT.denote w env)) := by
  simp [limitT, denote_kT hn, denote_sT hn, SupportBudget.limit]

theorem stable_limitT (hn : StableAt w nT env) : StableAt w (limitT nT) env := fun pre => by
  rw [denote_limitT (hn.extend pre), denote_limitT hn, hn pre]

theorem denote_startT (hn : StableAt w nT env) :
    (startT nT).denote w env =
      (Parameters.s (ParameterChoice.choose (nT.denote w env)) *
        ParameterChoice.choose (nT.denote w env) *
        (Parameters.s (ParameterChoice.choose (nT.denote w env)) - 9) + 1) / 2 := by
  simp [startT, denote_sT hn, denote_kT hn]

theorem stable_startT (hn : StableAt w nT env) : StableAt w (startT nT) env := fun pre => by
  rw [denote_startT (hn.extend pre), denote_startT hn, hn pre]

theorem startT_eq (hn : StableAt w nT env)
    (hs9 : 9 ≤ Parameters.s (ParameterChoice.choose (nT.denote w env))) :
    ((startT nT).denote w env : ℤ) =
      IntegerWindow.start (ParameterChoice.choose (nT.denote w env)) := by
  rw [denote_startT hn, IntegerWindow.start]
  push_cast [Nat.cast_sub hs9]
  rfl

theorem denote_radixT (hn : StableAt w nT env) :
    (radixT nT).denote w env = ParserFold.radix (nT.denote w env)
      (Parameters.q (nT.denote w env) (ParameterChoice.choose (nT.denote w env))) := by
  simp [radixT, denote_qT hn, denote_lgT hn, ParserFold.radix]

theorem stable_radixT (hn : StableAt w nT env) : StableAt w (radixT nT) env := fun pre => by
  rw [denote_radixT (hn.extend pre), denote_radixT hn, hn pre]

theorem denote_inputBitsT (hn : StableAt w nT env) (hm : StableAt w mT env) :
    (inputBitsT nT mT).denote w env = (max (nT.denote w env) (mT.denote w env)).log2 + 1 := by
  have hmax : StableAt w (maxT nT mT) env := fun pre => by
    rw [denote_maxT, denote_maxT, hn pre, hm pre]
  rw [inputBitsT, denote_add, denote_lgT hmax, denote_maxT, denote_const]

theorem stable_inputBitsT (hn : StableAt w nT env) (hm : StableAt w mT env) :
    StableAt w (inputBitsT nT mT) env := fun pre => by
  rw [denote_inputBitsT (hn.extend pre) (hm.extend pre), denote_inputBitsT hn hm, hn pre, hm pre]

theorem denote_DT (hn : StableAt w nT env) :
    (DT nT).denote w env =
      (2 ^ ParameterChoice.choose (nT.denote w env) *
        2 ^ ParameterChoice.choose (nT.denote w env)) ^
        Parameters.Q (ParameterChoice.choose (nT.denote w env)) := by
  rw [DT, labelSpaceT, powT_denote _ _ _ ((stable_kT hn).pow2.mul (stable_kT hn).pow2)]
  simp [denote_kT hn, denote_QT hn]

theorem stable_DT (hn : StableAt w nT env) : StableAt w (DT nT) env :=
  StableAt.powT ((stable_kT hn).pow2.mul (stable_kT hn).pow2) (stable_QT hn)

theorem denote_DT_eq_D (hn : StableAt w nT env) :
    (DT nT).denote w env = Parameters.D (ParameterChoice.choose (nT.denote w env)) := by
  rw [denote_DT hn, Parameters.D, Parameters.s, ← pow_two, ← pow_mul]

variable {n : ℕ} (S : System n) {arity : Term → Term} {AR : ℕ → ℕ}

/-- The incidence term counts each ordered scope position, including repeats. -/
theorem denote_incidenceT (hmv : mT.denote w env = S.constraints.length)
    (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = S.constraints[e].scope.length) :
    (incidenceT mT arity).denote w env = incidenceCount S := by
  rw [incidenceT, denote_sumT_lt _ _ env AR (fun acc e he => ?_), hmv,
    ← Fin.sum_univ_eq_sum_range]
  · unfold incidenceCount
    exact Finset.sum_congr rfl fun e _ => hAR e e.isLt
  · obtain ⟨h, _⟩ := iAR [acc, e] (lvl env.length) (stableAt_lvl (by simp))
    simpa only [List.cons_append, List.nil_append, denote_lvl_index] using h

theorem stable_incidenceT (hm : StableAt w mT env) (hmv : mT.denote w env = S.constraints.length)
    (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = S.constraints[e].scope.length) :
    StableAt w (incidenceT mT arity) env := fun pre => by
  rw [denote_incidenceT S (by rw [hm pre, hmv]) (iAR.extend pre) hAR,
    denote_incidenceT S hmv iAR hAR]

theorem denote_copiesT (hn : StableAt w nT env) (hmv : mT.denote w env = S.constraints.length)
    (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = S.constraints[e].scope.length) :
    (copiesT nT mT arity).denote w env =
      copiesOf S (Parameters.Q (ParameterChoice.choose (nT.denote w env)))
        (ParameterChoice.choose (nT.denote w env)) := by
  simp only [copiesT, denote_div, denote_mul, denote_const,
    denote_incidenceT S hmv iAR hAR, denote_DT hn, copiesOf]

theorem stable_copiesT (hn : StableAt w nT env) (hm : StableAt w mT env)
    (hmv : mT.denote w env = S.constraints.length) (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = S.constraints[e].scope.length) :
    StableAt w (copiesT nT mT arity) env :=
  ((stableAt_const _ _).mul (stable_incidenceT S hm hmv iAR hAR)).div (stable_DT hn)

/-- The support parser uses the same selected cutoff and bit budget. -/
theorem parserParams (hn : StableAt w nT env) :
    ParserParams w env (nT.denote w env)
      (Parameters.q (nT.denote w env) (ParameterChoice.choose (nT.denote w env)))
      (SupportBudget.limit (nT.denote w env) (ParameterChoice.choose (nT.denote w env)))
      nT (qT nT) (lgT nT) (radixT nT) (limitT nT) :=
  ⟨hn, rfl, stable_qT hn, denote_qT hn, stable_lgT hn, denote_lgT hn,
    stable_radixT hn, denote_radixT hn, stable_limitT hn, denote_limitT hn⟩

/-- Seed search is stable and returns a balanced seed whenever one exists in
its finite search range. This statement does not assume a machine representation. -/
theorem seedT_spec {varT : Term → Term → Term} {V : ℕ → ℕ → ℕ}
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    (hm : StableAt w mT env) (hmv : mT.denote w env = S.constraints.length)
    (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = S.constraints[e].scope.length)
    (iV : ImplN2 w env varT V)
    (hV : ∀ inc : Incidence S, V inc.1 inc.2 = (incidenceVariable S inc).val)
    (hex : ∃ sd < 2 ^ (2 * blk (Parameters.Q (ParameterChoice.choose n))
        (ParameterChoice.choose n) (WSchedulePlacement.inputBits S)),
      balN S (Parameters.Q (ParameterChoice.choose n)) (ParameterChoice.choose n) sd) :
    StableAt w (seedT nT mT arity varT) env ∧
      balN S (Parameters.Q (ParameterChoice.choose n)) (ParameterChoice.choose n)
        ((seedT nT mT arity varT).denote w env) := by
  exact ProgTerm.seed_spec S _ _ (stable_QT hn) (by rw [denote_QT hn, hnv])
    (stable_kT hn) (by rw [denote_kT hn, hnv]) (stable_inputBitsT hn hm)
    (by rw [denote_inputBitsT hn hm, hnv, hmv]; rfl) hn hnv hm hmv iAR hAR iV hV hex

/-- A successful seed search returns an index inside its enumerated range. -/
theorem seedT_lt {varT : Term → Term → Term} {V : ℕ → ℕ → ℕ}
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    (hm : StableAt w mT env) (hmv : mT.denote w env = S.constraints.length)
    (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = S.constraints[e].scope.length)
    (iV : ImplN2 w env varT V)
    (hV : ∀ inc : Incidence S, V inc.1 inc.2 = (incidenceVariable S inc).val)
    (hex : ∃ sd < 2 ^ (2 * blk (Parameters.Q (ParameterChoice.choose n))
        (ParameterChoice.choose n) (WSchedulePlacement.inputBits S)),
      balN S (Parameters.Q (ParameterChoice.choose n)) (ParameterChoice.choose n) sd) :
    (seedT nT mT arity varT).denote w env <
      2 ^ (2 * blk (Parameters.Q (ParameterChoice.choose n))
        (ParameterChoice.choose n) (WSchedulePlacement.inputBits S)) := by
  exact ProgTerm.seed_lt S _ _ (stable_QT hn) (by rw [denote_QT hn, hnv])
    (stable_kT hn) (by rw [denote_kT hn, hnv]) (stable_inputBitsT hn hm)
    (by rw [denote_inputBitsT hn hm, hnv, hmv]; rfl) hn hnv hm hmv iAR hAR iV hV hex

/-- The generic selected counter computes the complete weighted count modulo
`P`. The seed, interpolation-capacity and no-alias hypotheses are explicit;
this semantic theorem alone asserts no machine resource bound. -/
theorem counterT_cast {pT : Term} {P : ℕ} [Fact P.Prime]
    {varT weight : Term → Term → Term} {V : ℕ → ℕ → ℕ} {Wt : ℕ → ℕ → ZMod P}
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    (hm : StableAt w mT env) (hmv : mT.denote w env = S.constraints.length)
    (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (npos : 0 < n) (large : 6 ≤ ParameterChoice.choose n)
    (hP3 : 2 < P) (hQP : Parameters.Q (ParameterChoice.choose n) < P)
    (small : Parameters.R (ParameterChoice.choose n) < P)
    (below : Parameters.q n (ParameterChoice.choose n) + 1 < P)
    (capacity : incidenceCount S * (Parameters.R (ParameterChoice.choose n) - 1) <
      Parameters.Q (ParameterChoice.choose n) *
        (Parameters.q n (ParameterChoice.choose n) + 1))
    (no_alias : incidenceCount S * (Parameters.R (ParameterChoice.choose n) - 1) +
      Parameters.Q (ParameterChoice.choose n) * Parameters.q n (ParameterChoice.choose n) ≤ P - 2)
    (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = S.constraints[e].scope.length)
    (iV : ImplN2 w env varT V)
    (hV : ∀ inc : Incidence S, V inc.1 inc.2 = (incidenceVariable S inc).val)
    (iWt : ImplZ2 w env P weight Wt)
    (hWt : ∀ e (h : e < S.constraints.length) A,
      Wt e A = (S.constraints[e].weight (AssignmentLoop.assignment _ A) : ZMod P))
    (hex : ∃ sd < 2 ^ (2 * blk (Parameters.Q (ParameterChoice.choose n))
        (ParameterChoice.choose n) (WSchedulePlacement.inputBits S)),
      balN S (Parameters.Q (ParameterChoice.choose n)) (ParameterChoice.choose n) sd) :
    ((counterT nT mT pT arity varT weight).denote w env : ZMod P) = (S.count : ZMod P) := by
  obtain ⟨hseed, hbal⟩ := seedT_spec S hn hnv hm hmv iAR hAR iV hV hex
  have pp := parserParams hn
  rw [hnv] at pp
  exact systemCounterT_eq S npos hbal hP3 hQP large small below capacity no_alias
    hp hpv (stable_QT hn) (by rw [denote_QT hn, hnv])
    ((stable_qT hn).add (stableAt_const _ _))
    (by rw [denote_add, denote_qT hn, hnv, denote_const]) hn hnv hm hmv
    (stable_kT hn) (by rw [denote_kT hn, hnv])
    (stable_inputBitsT hn hm) (by rw [denote_inputBitsT hn hm, hnv, hmv]; rfl)
    hseed rfl (stable_startT hn) rfl (stableAt_const _ _) rfl
    (stable_RT hn) (by rw [denote_RT hn, hnv])
    (stable_copiesT S hn hm hmv iAR hAR)
    (by rw [denote_copiesT S hn hmv iAR hAR, hnv]) pp iAR hAR iV hV iWt hWt

end NtimeDspace.WeightedCounterTerm
