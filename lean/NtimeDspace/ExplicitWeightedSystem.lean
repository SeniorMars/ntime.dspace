/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

import NtimeDspace.ExplicitWeightedAccess

-- upstream: local-only (semantic input layout of the weighted counting application)

/-!
# Explicit residue tables for weighted systems

`ofSystem` constructs a fixed-width record for every weighted Boolean system.
Only residues of the weights are stored, so the construction requires no bound
on the weights themselves. `Represents` records the correspondence between each
input field and the system's ordered scopes and tables. Unused variables and
empty scopes are retained.

Different integer weights can have the same residue record. The record is an
input encoding for modular counting, not an injective encoding of unrestricted
natural-valued systems.
-/

namespace NtimeDspace.ExplicitWeightedEncoding

open WeightedSystem

variable {n : ℕ}

/-- A padded port is zero after the end of the actual ordered scope. -/
def portValue (c : Constraint n) (i : ℕ) : ℕ := (c.scope.map Fin.val).getD i 0

/-- Truth-table entries are numbered by little-endian Boolean assignments.
Extra high bits are ignored, so padding repeats the table on unused coordinates. -/
def residueValue (c : Constraint n) (p assignment : ℕ) : ℕ :=
  c.weight (fun i => assignment.testBit i) % p

def rowValue (c : Constraint n) (p maxArity offset : ℕ) : ℕ :=
  if offset = 0 then c.scope.length else
    if offset ≤ maxArity then portValue c (offset - 1)
    else residueValue c p (offset - (1 + maxArity))

def fieldValue (S : System n) (p maxArity index : ℕ) : ℕ :=
  if index < 4 then [n, S.constraints.length, p, maxArity].getD index 0 else
    if h : (index - 4) / rowWidth maxArity < S.constraints.length then
      rowValue S.constraints[(index - 4) / rowWidth maxArity] p maxArity
        ((index - 4) % rowWidth maxArity) else 0

theorem portValue_lt (c : Constraint n) {bound : ℕ} (hn : n ≤ bound) (hpos : 0 < bound)
    (i : ℕ) : portValue c i < bound := by
  unfold portValue
  by_cases hi : i < c.scope.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map]
    exact (c.scope[i]).isLt.trans_le hn
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using (Nat.le_of_not_gt hi))]
    exact hpos

theorem residueValue_lt (c : Constraint n) {p bound : ℕ}
    (hp : 0 < p) (hbound : p ≤ bound) (assignment : ℕ) :
    residueValue c p assignment < bound := (Nat.mod_lt _ hp).trans_le hbound

theorem rowValue_lt (c : Constraint n) {p maxArity width : ℕ}
    (hn : n < 2 ^ width) (hp : 0 < p) (hP : p < 2 ^ width)
    (ha : c.scope.length ≤ maxArity) (hA : maxArity < 2 ^ width) (offset : ℕ) :
    rowValue c p maxArity offset < 2 ^ width := by
  unfold rowValue
  split_ifs
  · exact ha.trans_lt hA
  · exact portValue_lt c hn.le (by positivity) _
  · exact residueValue_lt c hp hP.le _

theorem fieldValue_lt (S : System n) {p maxArity width : ℕ}
    (hn : n < 2 ^ width) (hm : S.constraints.length < 2 ^ width)
    (hp : 0 < p) (hP : p < 2 ^ width) (hA : maxArity < 2 ^ width)
    (ha : ∀ c ∈ S.constraints, c.scope.length ≤ maxArity) (index : ℕ) :
    fieldValue S p maxArity index < 2 ^ width := by
  unfold fieldValue
  split_ifs with hi he
  · interval_cases index <;> simp_all
  · exact rowValue_lt _ hn hp hP (ha _ (List.getElem_mem he)) hA _
  · positivity

/-- The explicit table record. The hypotheses bound indices and residues,
never the unreduced natural weights. -/
def ofSystem (S : System n) (p maxArity width : ℕ)
    (hw : 0 < width) (hn : n < 2 ^ width) (hm : S.constraints.length < 2 ^ width)
    (hp : 0 < p) (hP : p < 2 ^ width) (hA : maxArity < 2 ^ width)
    (ha : ∀ c ∈ S.constraints, c.scope.length ≤ maxArity) : Record where
  width := width
  fields := List.ofFn fun i : Fin (4 + S.constraints.length * rowWidth maxArity) =>
    fieldValue S p maxArity i
  positive_width := hw
  fields_lt := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact fieldValue_lt S hn hm hp hP hA ha i

theorem fieldValue_row (S : System n) (p maxArity e offset : ℕ)
    (he : e < S.constraints.length) (ho : offset < rowWidth maxArity) :
    fieldValue S p maxArity (rowStart maxArity e + offset) =
      rowValue S.constraints[e] p maxArity offset := by
  have hrow : 0 < rowWidth maxArity := by unfold rowWidth; positivity
  have hd : (e * rowWidth maxArity + offset) / rowWidth maxArity = e := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hrow, Nat.div_eq_of_lt ho, Nat.zero_add]
  have hm : (e * rowWidth maxArity + offset) % rowWidth maxArity = offset := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt ho]
  simp only [fieldValue, rowStart, show ¬4 + e * rowWidth maxArity + offset < 4 by omega,
    ite_false, show 4 + e * rowWidth maxArity + offset - 4 = e * rowWidth maxArity + offset by omega,
    hd, hm]
  simp [he]

theorem rowValue_arity (c : Constraint n) (p maxArity : ℕ) :
    rowValue c p maxArity 0 = c.scope.length := by simp [rowValue]

theorem rowValue_port (c : Constraint n) (p maxArity i : ℕ) (hi : i < maxArity) :
    rowValue c p maxArity (1 + i) = portValue c i := by
  simp [rowValue, show 1 + i ≤ maxArity by omega]

theorem rowValue_weight (c : Constraint n) (p maxArity a : ℕ) :
    rowValue c p maxArity (1 + maxArity + a) = residueValue c p a := by
  simp [rowValue, show ¬1 + maxArity + a ≤ maxArity by omega,
    show 1 + maxArity + a - (1 + maxArity) = a by omega]

/-- The four headers and every padded constraint field have their intended
meaning. It is a representation contract, independent of incidence bounds. -/
structure Represents (r : Record) (S : System n) (p maxArity : ℕ) : Prop where
  length : r.fields.length = 4 + S.constraints.length * rowWidth maxArity
  header : ∀ i < 4, r.fields.getD i 0 = [n, S.constraints.length, p, maxArity].getD i 0
  arity : ∀ e (he : e < S.constraints.length),
    r.fields.getD (arityIndex maxArity e) 0 = S.constraints[e].scope.length
  port : ∀ e (he : e < S.constraints.length) i, i < maxArity →
    r.fields.getD (portIndex maxArity e i) 0 = portValue S.constraints[e] i
  weight : ∀ e (he : e < S.constraints.length) a, a < 2 ^ maxArity →
    r.fields.getD (weightIndex maxArity e a) 0 = residueValue S.constraints[e] p a

theorem ofSystem_represents (S : System n) (p maxArity width : ℕ)
    (hw : 0 < width) (hn : n < 2 ^ width) (hm : S.constraints.length < 2 ^ width)
    (hp : 0 < p) (hP : p < 2 ^ width) (hA : maxArity < 2 ^ width)
    (ha : ∀ c ∈ S.constraints, c.scope.length ≤ maxArity) :
    Represents (ofSystem S p maxArity width hw hn hm hp hP hA ha) S p maxArity := by
  let r := ofSystem S p maxArity width hw hn hm hp hP hA ha
  have hl : r.fields.length = 4 + S.constraints.length * rowWidth maxArity := by
    simp [r, ofSystem]
  have field (i : ℕ) (hi : i < 4 + S.constraints.length * rowWidth maxArity) :
      r.fields.getD i 0 = fieldValue S p maxArity i := by
    simp [r, ofSystem, List.getD_eq_getElem?_getD, hi]
  have hrow : 0 < rowWidth maxArity := by unfold rowWidth; positivity
  have inside (e offset : ℕ) (he : e < S.constraints.length) (ho : offset < rowWidth maxArity) :
      rowStart maxArity e + offset < 4 + S.constraints.length * rowWidth maxArity := by
    unfold rowStart
    have hmul := Nat.mul_le_mul_right (rowWidth maxArity) (show e + 1 ≤ S.constraints.length by omega)
    nlinarith
  refine ⟨hl, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [field i (by omega)]
    simp [fieldValue, hi]
  · intro e he
    rw [field _ (by simpa [arityIndex] using inside e 0 he hrow)]
    change fieldValue S p maxArity (rowStart maxArity e + 0) = _
    rw [fieldValue_row S p maxArity e 0 he hrow, rowValue_arity]
  · intro e he i hi
    have ho : 1 + i < rowWidth maxArity := by
      unfold rowWidth
      have : 0 < 2 ^ maxArity := by positivity
      omega
    rw [field _ (by simpa [portIndex, Nat.add_assoc] using inside e (1 + i) he ho)]
    simp only [portIndex, Nat.add_assoc]
    rw [fieldValue_row S p maxArity e (1 + i) he ho, rowValue_port _ _ _ _ hi]
  · intro e he a ha
    have ho : 1 + maxArity + a < rowWidth maxArity := by unfold rowWidth; omega
    rw [field _ (by simpa [weightIndex, Nat.add_assoc] using inside e (1 + maxArity + a) he ho)]
    rw [show weightIndex maxArity e a = rowStart maxArity e + (1 + maxArity + a) by
      simp [weightIndex, Nat.add_assoc]]
    rw [fieldValue_row S p maxArity e (1 + maxArity + a) he ho, rowValue_weight]

/-- A canonical logarithmic width large enough for all four header fields. -/
def systemWidth (S : System n) (p maxArity : ℕ) : ℕ :=
  (n + S.constraints.length + p + maxArity).log2 + 1

theorem header_lt_systemWidth (S : System n) (p maxArity : ℕ) :
    n < 2 ^ systemWidth S p maxArity ∧
    S.constraints.length < 2 ^ systemWidth S p maxArity ∧
    p < 2 ^ systemWidth S p maxArity ∧ maxArity < 2 ^ systemWidth S p maxArity := by
  have h : n + S.constraints.length + p + maxArity < 2 ^ systemWidth S p maxArity := by
    simpa only [systemWidth, Nat.log2_eq_log_two] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n + S.constraints.length + p + maxArity)
  omega

/-- Every bounded-arity system has a concrete record, including systems with
unused variables or no constraints. -/
def systemRecord (S : System n) (p maxArity : ℕ) (hp : 0 < p)
    (ha : ∀ c ∈ S.constraints, c.scope.length ≤ maxArity) : Record :=
  ofSystem S p maxArity (systemWidth S p maxArity) (by unfold systemWidth; omega)
    (header_lt_systemWidth S p maxArity).1 (header_lt_systemWidth S p maxArity).2.1 hp
    (header_lt_systemWidth S p maxArity).2.2.1 (header_lt_systemWidth S p maxArity).2.2.2 ha

theorem systemRecord_represents (S : System n) (p maxArity : ℕ) (hp : 0 < p)
    (ha : ∀ c ∈ S.constraints, c.scope.length ≤ maxArity) :
    Represents (systemRecord S p maxArity hp ha) S p maxArity :=
  ofSystem_represents S p maxArity _ _ _ _ _ _ _ _

theorem Represents.variableCount {r : Record} {S : System n} {p maxArity : ℕ}
    (h : Represents r S p maxArity) : r.fields.getD 0 0 = n := by
  simpa using h.header 0 (by omega)

theorem Represents.constraintCount {r : Record} {S : System n} {p maxArity : ℕ}
    (h : Represents r S p maxArity) : r.fields.getD 1 0 = S.constraints.length := by
  simpa using h.header 1 (by omega)

theorem Represents.modulus {r : Record} {S : System n} {p maxArity : ℕ}
    (h : Represents r S p maxArity) : r.fields.getD 2 0 = p := by
  simpa using h.header 2 (by omega)

theorem Represents.maxArity {r : Record} {S : System n} {p maxArity : ℕ}
    (h : Represents r S p maxArity) : r.fields.getD 3 0 = maxArity := by
  simpa using h.header 3 (by omega)

/-- Reducing a stored table entry does not change its interpretation modulo p. -/
theorem residueValue_cast (c : Constraint n) (p a : ℕ) :
    (residueValue c p a : ZMod p) = (c.weight (fun i => a.testBit i) : ZMod p) := by
  simp [residueValue]

theorem residueValue_mod (c : Constraint n) (p maxArity a : ℕ)
    (ha : c.scope.length ≤ maxArity) :
    residueValue c p (a % 2 ^ maxArity) = residueValue c p a := by
  unfold residueValue
  congr 2
  funext i
  simp [Nat.testBit_mod_two_pow, show i.val < maxArity from i.isLt.trans_le ha]

def systemArity (S : System n) (e : ℕ) : ℕ :=
  if h : e < S.constraints.length then S.constraints[e].scope.length else 0

def systemPort (S : System n) (e i : ℕ) : ℕ :=
  if h : e < S.constraints.length then portValue S.constraints[e] i else 0

def systemWeight (S : System n) (p e a : ℕ) : ZMod p :=
  if h : e < S.constraints.length then
    (S.constraints[e].weight (AssignmentLoop.assignment _ a) : ZMod p) else 0

theorem systemArity_eq (S : System n) (e : ℕ) (he : e < S.constraints.length) :
    systemArity S e = S.constraints[e].scope.length := by simp [systemArity, he]

theorem systemPort_eq (S : System n) (inc : Incidence S) :
    systemPort S inc.1 inc.2 = (incidenceVariable S inc).val := by
  simp only [systemPort, inc.1.isLt, dite_true, portValue, incidenceVariable]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
  simp only [Fin.getElem_fin]

theorem systemWeight_eq (S : System n) (p e a : ℕ) (he : e < S.constraints.length) :
    systemWeight S p e a = (S.constraints[e].weight (AssignmentLoop.assignment _ a) : ZMod p) := by
  simp [systemWeight, he]

open ProgTerm ProgTerm.Term in
/-- Exact callback contracts for the generic counter. In particular, the
weight contract holds for every natural assignment index, not only those
below the truth-table size. -/
theorem Represents.accessor_contracts {r : Record} {S : System n} {p maxArity : ℕ}
    (h : Represents r S p maxArity)
    (arity_bound : ∀ c ∈ S.constraints, c.scope.length ≤ maxArity)
    {env : List ℕ} {widthT countT maxArityT : Term}
    (hw : StableAt (encode r) widthT env) (hwv : widthT.denote (encode r) env = r.width)
    (hm : StableAt (encode r) countT env)
    (hmv : countT.denote (encode r) env = S.constraints.length)
    (ha : StableAt (encode r) maxArityT env)
    (hav : maxArityT.denote (encode r) env = maxArity) :
    ImplN (encode r) env (explicitArityT widthT countT maxArityT) (systemArity S) ∧
    ImplN2 (encode r) env (explicitPortT widthT countT maxArityT) (systemPort S) ∧
    ImplZ2 (encode r) env p (explicitWeightT widthT countT maxArityT) (systemWeight S p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro pre e he
    obtain ⟨hv, hs⟩ := implN_explicitArityT r hw hwv hm ha pre e he
    refine ⟨?_, hs⟩
    rw [hmv, hav] at hv
    rw [hv]
    dsimp only
    unfold systemArity
    split_ifs with he'
    · exact h.arity _ he'
    · rfl
  · intro pre e i he hi
    obtain ⟨hv, hs⟩ := implN2_explicitPortT r hw hwv hm ha pre e i he hi
    refine ⟨?_, hs⟩
    rw [hmv, hav] at hv
    rw [hv]
    dsimp only
    unfold systemPort
    by_cases he' : e.denote (encode r) (pre ++ env) < S.constraints.length
    · by_cases hi' : i.denote (encode r) (pre ++ env) < maxArity
      · simpa only [he', hi', and_self, ite_true, dite_true] using h.port _ he' _ hi'
      · have hs : S.constraints[e.denote (encode r) (pre ++ env)].scope.length ≤ maxArity :=
          arity_bound _ (List.getElem_mem he')
        have ho : (S.constraints[e.denote (encode r) (pre ++ env)].scope.map Fin.val).length ≤
            i.denote (encode r) (pre ++ env) := by simp only [List.length_map]; omega
        simp [he', hi', portValue, List.getD_eq_getElem?_getD, List.getElem?_eq_none ho]
    · simp [he']
  · intro pre e a he hx
    have hv := implZ2_explicitWeightT r p hw hwv hm ha pre e a he hx
    rw [hmv, hav] at hv
    rw [hv]
    dsimp only
    unfold systemWeight
    split_ifs with he'
    · rw [h.weight _ he' _ (Nat.mod_lt _ (by positivity)),
        residueValue_mod _ p maxArity _ (arity_bound _ (List.getElem_mem he')),
        residueValue_cast]
      rfl
    · rfl

/-- A nonempty declared variable set with no constraints is representable. -/
example : Represents
    (systemRecord (⟨[]⟩ : System 1) 3 0 (by decide) (by simp)) (⟨[]⟩ : System 1) 3 0 :=
  systemRecord_represents _ _ _ _ _

/-- An empty scope still has a table entry; it is reduced modulo the modulus. -/
example : (systemRecord (⟨[⟨[], fun _ => 11⟩]⟩ : System 0) 3 0
    (by decide) (by simp)).fields.getD (weightIndex 0 0 0) 0 = 2 := by decide

end NtimeDspace.ExplicitWeightedEncoding
