/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.WeightedNormalization
import NtimeDspace.MeasTerm
import NtimeDspace.TameIte

-- upstream: local-only (input normalization of the weighted counting application)

/-!
# Access the normalized system without constructing it

The added constraint for variable `v` needs only a scan of the original
incidences. The accessors retain the original constraint tables and return
constant weight one for the added constraints. No occurrence bitmap or
serialized normalized system is stored.
-/

namespace NtimeDspace.WeightedNormalization

open WeightedSystem
open scoped BigOperators

/-- The number of original incidence positions carrying the given variable index. -/
def occurrenceN (m : ℕ) (AR : ℕ → ℕ) (V : ℕ → ℕ → ℕ) (v : ℕ) : ℕ :=
  ∑ e ∈ Finset.range m, ∑ i ∈ Finset.range (AR e), if V e i = v then 1 else 0

def normalizedArityN (n m : ℕ) (AR : ℕ → ℕ) (V : ℕ → ℕ → ℕ) (e : ℕ) : ℕ :=
  if e < m then AR e else
    if e < m + n then if occurrenceN m AR V (e - m) = 0 then 1 else 0 else 0

/-- Reduction modulo `n` bounds even queries outside a real scope. -/
def normalizedPortN (n m : ℕ) (V : ℕ → ℕ → ℕ) (e i : ℕ) : ℕ :=
  if e < m then V e i else (e - m) % n

def normalizedWeightN {p : ℕ} (m : ℕ) (Wt : ℕ → ℕ → ZMod p)
    (e a : ℕ) : ZMod p := if e < m then Wt e a else 1

variable {n : ℕ} (S : System n) (AR : ℕ → ℕ) (V : ℕ → ℕ → ℕ)
  (hAR : ∀ e (he : e < S.constraints.length), AR e = S.constraints[e].scope.length)
  (hV : ∀ e (he : e < S.constraints.length) i
    (hi : i < S.constraints[e].scope.length), V e i = (S.constraints[e].scope[i]).val)

include hAR hV in
theorem occurrenceN_eq (v : Fin n) :
    occurrenceN S.constraints.length AR V v = occurrences S v := by
  unfold occurrenceN
  rw [ProgTerm.sum_incidence_eq S AR hAR]
  simp only [Incidence, Fintype.sum_sigma, occurrences]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro i _
  rw [hV e e.isLt i i.isLt]
  simp only [Fin.val_inj]
  rfl

include hAR hV in
theorem normalizedArityN_eq (e : ℕ) (he : e < (normalize S).constraints.length) :
    normalizedArityN n S.constraints.length AR V e =
      (normalize S).constraints[e].scope.length := by
  by_cases he' : e < S.constraints.length
  · simp only [normalizedArityN, he', ite_true, normalize, List.getElem_append_left he']
    exact hAR e he'
  · have hv : e - S.constraints.length < n := by
      rw [constraint_count] at he
      omega
    simp only [normalizedArityN, he', ite_false]
    simp only [show e < S.constraints.length + n by simpa only [constraint_count] using he,
      ite_true]
    rw [occurrenceN_eq S AR V hAR hV ⟨e - S.constraints.length, hv⟩]
    simp only [normalize, List.getElem_append_right (Nat.le_of_not_gt he'), List.getElem_ofFn]
    change (if occurrences S ⟨e - S.constraints.length, hv⟩ = 0 then 1 else 0) =
      (if occurrences S ⟨e - S.constraints.length, hv⟩ = 0 then
        [(⟨e - S.constraints.length, hv⟩ : Fin n)] else []).length
    split_ifs <;> simp_all

include hV in
theorem normalizedPortN_eq (e : ℕ) (he : e < (normalize S).constraints.length)
    (i : ℕ) (hi : i < (normalize S).constraints[e].scope.length) :
    normalizedPortN n S.constraints.length V e i =
      ((normalize S).constraints[e].scope[i]).val := by
  by_cases he' : e < S.constraints.length
  · simp only [normalizedPortN, he', ite_true, normalize, List.getElem_append_left he'] at hi ⊢
    exact hV e he' i hi
  · have hv : e - S.constraints.length < n := by rw [constraint_count] at he; omega
    have scope : (normalize S).constraints[e].scope =
        (addedConstraint S ⟨e - S.constraints.length, hv⟩).scope := by
      simp only [normalize, List.getElem_append_right (Nat.le_of_not_gt he'), List.getElem_ofFn]
    simp only [normalizedPortN, he', ite_false, Nat.mod_eq_of_lt hv]
    simp only [scope, addedConstraint] at hi ⊢
    split_ifs at hi ⊢ with hu
    · have : i = 0 := by simpa using hi
      subst i
      rfl
    · simp at hi

theorem normalizedWeightN_eq {p : ℕ} (Wt : ℕ → ℕ → ZMod p)
    (hWt : ∀ e (he : e < S.constraints.length) a,
      Wt e a = (S.constraints[e].weight (fun i => a.testBit i) : ZMod p))
    (e : ℕ) (he : e < (normalize S).constraints.length) (a : ℕ) :
    normalizedWeightN S.constraints.length Wt e a =
      ((normalize S).constraints[e].weight (fun i => a.testBit i) : ZMod p) := by
  let entry (c : Constraint n) := c.weight (fun i => a.testBit i)
  change normalizedWeightN S.constraints.length Wt e a =
    (entry (normalize S).constraints[e] : ZMod p)
  by_cases he' : e < S.constraints.length
  · have hc : (normalize S).constraints[e] = S.constraints[e] := by
      simp only [normalize, List.getElem_append_left he']
    rw [hc]
    simp only [normalizedWeightN, he', ite_true, entry]
    exact hWt e he' a
  · have hv : e - S.constraints.length < n := by rw [constraint_count] at he; omega
    have hc : (normalize S).constraints[e] =
        addedConstraint S ⟨e - S.constraints.length, hv⟩ := by
      simp only [normalize, List.getElem_append_right (Nat.le_of_not_gt he'), List.getElem_ofFn]
    rw [hc]
    simp only [normalizedWeightN, he', ite_false, entry, addedConstraint, Nat.cast_one]

end NtimeDspace.WeightedNormalization

namespace NtimeDspace.ProgTerm

open Term WeightedNormalization
open scoped BigOperators

variable {w : List Bool} {env : List ℕ}

/-- Count original occurrences using nested constraint/port scans. -/
def occurrenceT (mT : Term) (arity : Term → Term) (varT : Term → Term → Term)
    (v : Term) : Term := incSumT mT arity fun e i => eqT (varT e i) v

def normalizedArityT (nT mT : Term) (arity : Term → Term)
    (varT : Term → Term → Term) (e : Term) : Term :=
  ite (lt e mT) (arity e)
    (ite (lt e (add mT nT)) (eqT (occurrenceT mT arity varT (sub e mT)) (const 0))
      (const 0))

def normalizedPortT (nT mT : Term) (varT : Term → Term → Term)
    (e i : Term) : Term := ite (lt e mT) (varT e i) (mod (sub e mT) nT)

def normalizedWeightT (mT : Term) (weight : Term → Term → Term)
    (e a : Term) : Term := ite (lt e mT) (weight e a) (const 1)

theorem denote_occurrenceT {mT v : Term} {arity : Term → Term}
    {varT : Term → Term → Term} {AR : ℕ → ℕ} {V : ℕ → ℕ → ℕ}
    (hv : StableAt w v env) (iAR : ImplN w env arity AR) (iV : ImplN2 w env varT V) :
    (occurrenceT mT arity varT v).denote w env =
      occurrenceN (mT.denote w env) AR V (v.denote w env) := by
  unfold occurrenceT incSumT occurrenceN
  rw [denote_sumT _ _ env
    (fun e => ∑ i ∈ Finset.range (AR e), if V e i = v.denote w env then 1 else 0)]
  intro acc e
  have hes : StableAt w (lvl env.length) ([acc, e] ++ env) := stableAt_index env acc e
  have har := (iAR [acc, e] _ hes).1
  simp only [List.cons_append, List.nil_append, denote_lvl_index] at har
  rw [denote_sumT _ _ (acc :: e :: env)
    (fun i => if V e i = v.denote w env then 1 else 0), har]
  intro acc' i
  have hes' := hes.extend [acc', i]
  have his : StableAt w (lvl (env.length + 2)) ([acc', i, acc, e] ++ env) :=
    stableAt_lvl (by simp)
  have hvar := (iV [acc', i, acc, e] (lvl env.length) (lvl (env.length + 2)) hes' his).1
  simp only [List.cons_append, List.nil_append] at hvar
  have hev : (lvl env.length).denote w (acc' :: i :: acc :: e :: env) = e := by term_simp
  have hiv : (lvl (env.length + 2)).denote w (acc' :: i :: acc :: e :: env) = i := by term_simp
  have hlen : (acc :: e :: env).length = env.length + 2 := by simp
  have hv' := hv [acc', i, acc, e]
  simp only [List.cons_append, List.nil_append] at hv'
  simp only [hlen, denote_eqT, hvar, hev, hiv, hv']

theorem implN_occurrenceT {mT : Term} {arity : Term → Term}
    {varT : Term → Term → Term} {AR : ℕ → ℕ} {V : ℕ → ℕ → ℕ}
    (hm : StableAt w mT env) (iAR : ImplN w env arity AR) (iV : ImplN2 w env varT V) :
    ImplN w env (occurrenceT mT arity varT) (occurrenceN (mT.denote w env) AR V) := by
  intro pre v hv
  refine ⟨?_, ?_⟩
  · rw [denote_occurrenceT hv (iAR.extend pre) (iV.extend pre), hm pre]
  · intro extra
    rw [denote_occurrenceT (hv.extend extra) ((iAR.extend pre).extend extra)
      ((iV.extend pre).extend extra), denote_occurrenceT hv (iAR.extend pre) (iV.extend pre),
      (hm.extend pre) extra, hv extra]

theorem implN_normalizedArityT {nT mT : Term} {arity : Term → Term}
    {varT : Term → Term → Term} {AR : ℕ → ℕ} {V : ℕ → ℕ → ℕ}
    (hn : StableAt w nT env) (hm : StableAt w mT env)
    (iAR : ImplN w env arity AR) (iV : ImplN2 w env varT V) :
    ImplN w env (normalizedArityT nT mT arity varT)
      (normalizedArityN (nT.denote w env) (mT.denote w env) AR V) := by
  intro pre e he
  have har := iAR pre e he
  have hs := implN_occurrenceT hm iAR iV pre (sub e mT) (he.sub (hm.extend pre))
  refine ⟨?_, ?_⟩
  · simp only [normalizedArityT, normalizedArityN, denote_ite, denote_lt, har.1,
      denote_eqT, hs.1, denote_sub, denote_const, denote_add, hn pre, hm pre]
    split_ifs <;> simp_all
  · exact (he.lt (hm.extend pre)).ite har.2
      ((he.lt ((hm.extend pre).add (hn.extend pre))).ite
        (hs.2.eqT (stableAt_const _ _)) (stableAt_const _ _))

theorem implN2_normalizedPortT {nT mT : Term} {varT : Term → Term → Term}
    {V : ℕ → ℕ → ℕ} (hn : StableAt w nT env) (hm : StableAt w mT env)
    (iV : ImplN2 w env varT V) :
    ImplN2 w env (normalizedPortT nT mT varT)
      (normalizedPortN (nT.denote w env) (mT.denote w env) V) := by
  intro pre e i he hi
  have hvar := iV pre e i he hi
  refine ⟨?_, ?_⟩
  · simp only [normalizedPortT, normalizedPortN, denote_ite, denote_lt, hvar.1,
      denote_mod, denote_sub, hn pre, hm pre]
    split_ifs <;> simp_all
  · exact (he.lt (hm.extend pre)).ite hvar.2 ((he.sub (hm.extend pre)).mod (hn.extend pre))

theorem implZ2_normalizedWeightT {p : ℕ} {mT : Term} {weight : Term → Term → Term}
    {Wt : ℕ → ℕ → ZMod p} (hm : StableAt w mT env)
    (iWt : ImplZ2 w env p weight Wt) :
    ImplZ2 w env p (normalizedWeightT mT weight)
      (normalizedWeightN (mT.denote w env) Wt) := by
  intro pre e a he ha
  have hweight := iWt pre e a he ha
  simp only [normalizedWeightT, normalizedWeightN, denote_ite, denote_lt, denote_const, hm pre]
  split_ifs <;> simp_all

section Tame

variable {L : ℕ} {nT mT : Term} {arity : Term → Term}
  {varT weight : Term → Term → Term}

/-- Equality testing returns one bit regardless of its input tiers. -/
theorem tm_eqT {a b : Term} {da db : ℕ} (hL : 2 ≤ L)
    (ha : Tm w L da a env) (hb : Tm w L db b env) : Tm w L 1 (eqT a b) env := by
  unfold eqT
  exact t_sub (t_const (lit_lt_two_pow (by omega) hL))
    (t_add (t_lt ha hb (by omega)) (t_lt hb ha (by omega)) (by omega) (by omega))

/-- The two incidence loops have tier three, independently of their scan length. -/
theorem tm_occurrenceT (hL : 2 ≤ L) (hm : Tm w L 1 mT env)
    (hAR : TmF w L arity 4 1 env) (hV : TmF2 w L varT 4 4 1 env) :
    TmF w L (occurrenceT mT arity varT) 4 3 env := by
  intro env' he v hv
  unfold occurrenceT incSumT
  refine t_sumT (hm.ext he) (db := 2) ?_ (by omega) (by omega)
  intro env'' he' e hE
  have htot := Ext.trans he' he
  refine t_sumT (hAR.app htot (hE.mono (by omega))) (db := 1) ?_
    (by omega) (by omega)
  intro env''' he'' i hI
  exact tm_eqT hL
    (hV.app (Ext.trans he'' htot) ((hE.ext he'').mono (by omega)) (hI.mono (by omega)))
    ((hv.ext he').ext he'')

/-- The normalized accessors preserve the input/output tiers used by the counter. -/
theorem tm_normalized_accessors (hL : 2 ≤ L)
    (hn : Tm w L 1 nT env) (hm : Tm w L 1 mT env) (hnpos : Pos w L nT env)
    (hAR : TmF w L arity 4 1 env) (hV : TmF2 w L varT 4 4 1 env)
    (hWt : TmF2 w L weight 4 4 1 env) :
    TmF w L (normalizedArityT nT mT arity varT) 4 1 env ∧
    TmF2 w L (normalizedPortT nT mT varT) 4 4 1 env ∧
    TmF2 w L (normalizedWeightT mT weight) 4 4 1 env := by
  have hzero : Tm w L 1 (const 0) env := t_const (by positivity)
  have hone : Tm w L 1 (const 1) env := t_const (lit_lt_two_pow (by omega) hL)
  have hocc := tm_occurrenceT hL hm hAR hV
  refine ⟨?_, ?_, ?_⟩
  · intro env' he e hE
    unfold normalizedArityT
    refine tm_ite (t_lt hE (hm.ext he) (by omega)) (hAR.app he hE) ?_
    refine tm_ite (t_lt hE (t_add (hm.ext he) (hn.ext he) (by omega) (by omega))
      (by omega)) ?_ (hzero.ext he)
    exact tm_eqT hL (hocc.app he (t_sub hE (hm.ext he))) (hzero.ext he)
  · intro env' he e i hE hI
    unfold normalizedPortT
    exact tm_ite (t_lt hE (hm.ext he) (by omega)) (hV.app he hE hI)
      (tm_mod (t_sub hE (hm.ext he)) (hn.ext he) (hnpos.ext he))
  · intro env' he e a hE hA
    unfold normalizedWeightT
    exact tm_ite (t_lt hE (hm.ext he) (by omega)) (hWt.app he hE hA) (hone.ext he)

end Tame

end NtimeDspace.ProgTerm
