import NtimeDspace.MachineContract
import NtimeDspace.SupportEncoding
import NtimeDspace.FormulaIncidences

/-!
# Canonical explicit binary inputs

The format is gamma(n+1), followed by a length-prefixed ordered clause list,
then gamma(modulus+1). Each clause is a length-prefixed ordered literal list;
a literal consists of gamma(index+1) and one polarity bit. Here gamma is the
executable Elias codec from SupportEncoding. No satisfying count is encoded.

The parser rejects truncated inputs, out-of-range indices, clauses wider than
three, and trailing junk at the complete-record interface. List parsing uses
structural recursion on the explicitly decoded count. Empty clauses, zero
variables, and unused declared variables are represented without normalization.

These are executable data codecs and length bounds, not a Turing-machine
implementation or a bound on the parser's work tapes.
-/

namespace NtimeDspace.InputEncoding

open SupportEncoding

/-- Shift by one so gamma also represents zero. -/
def encodeNat (n : ℕ) : List Bool := gammaEncode (n + 1)

def decodeNat (bits : List Bool) : Option (ℕ × List Bool) :=
  (gammaDecode bits).map fun (n, rest) => (n - 1, rest)

theorem decodeNat_encode_append (n : ℕ) (rest : List Bool) :
    decodeNat (encodeNat n ++ rest) = some (n, rest) := by
  simp [decodeNat, encodeNat, gammaDecode_encode_append]

theorem encodeNat_length (n : ℕ) :
    (encodeNat n).length = 2 * (n + 1).log2 + 1 := gammaEncode_length _

def decodeBool : List Bool → Option (Bool × List Bool)
  | [] => none
  | bit :: rest => some (bit, rest)

/-- Concatenate element encodings in their given order. -/
def encodeMany {α : Type} (encode : α → List Bool) : List α → List Bool
  | [] => []
  | x :: xs => encode x ++ encodeMany encode xs

/-- An explicit finite parser. The decoded length is a recursion bound. -/
def decodeMany {α : Type} (decode : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
    let (value, rest) ← decode bits
    let (values, suffix) ← decodeMany decode count rest
    return (value :: values, suffix)

def encodeList {α : Type} (encode : α → List Bool) (xs : List α) : List Bool :=
  encodeNat xs.length ++ encodeMany encode xs

def decodeList {α : Type} (decode : List Bool → Option (α × List Bool))
    (bits : List Bool) : Option (List α × List Bool) := do
  let (count, rest) ← decodeNat bits
  decodeMany decode count rest

theorem decodeMany_encode_append {α : Type}
    (encode : α → List Bool) (decode : List Bool → Option (α × List Bool))
    (roundtrip : ∀ x rest, decode (encode x ++ rest) = some (x, rest))
    (xs : List α) (rest : List Bool) :
    decodeMany decode xs.length (encodeMany encode xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [encodeMany, List.append_assoc, decodeMany, roundtrip, ih]

theorem decodeList_encode_append {α : Type}
    (encode : α → List Bool) (decode : List Bool → Option (α × List Bool))
    (roundtrip : ∀ x rest, decode (encode x ++ rest) = some (x, rest))
    (xs : List α) (rest : List Bool) :
    decodeList decode (encodeList encode xs ++ rest) = some (xs, rest) := by
  simp [encodeList, decodeList, List.append_assoc, decodeNat_encode_append,
    decodeMany_encode_append encode decode roundtrip]

def encodeLiteral {n : ℕ} (literal : Literal n) : List Bool :=
  encodeNat literal.index.val ++ [literal.positive]

def decodeLiteral (n : ℕ) (bits : List Bool) : Option (Literal n × List Bool) := do
  let (index, rest) ← decodeNat bits
  let (positive, suffix) ← decodeBool rest
  if valid : index < n then return (⟨⟨index, valid⟩, positive⟩, suffix) else none

theorem decodeLiteral_encode_append {n : ℕ} (literal : Literal n) (rest : List Bool) :
    decodeLiteral n (encodeLiteral literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk index positive =>
    simp [encodeLiteral, decodeLiteral, List.append_assoc, decodeNat_encode_append,
      decodeBool, index.isLt]

def encodeClause {n : ℕ} (clause : Clause n) : List Bool :=
  encodeList encodeLiteral clause.literals

def decodeClause (n : ℕ) (bits : List Bool) : Option (Clause n × List Bool) := do
  let (literals, rest) ← decodeList (decodeLiteral n) bits
  if valid : literals.length ≤ 3 then return (⟨literals, valid⟩, rest) else none

theorem decodeClause_encode_append {n : ℕ} (clause : Clause n) (rest : List Bool) :
    decodeClause n (encodeClause clause ++ rest) = some (clause, rest) := by
  cases clause with
  | mk literals width =>
    simp [encodeClause, decodeClause,
      decodeList_encode_append encodeLiteral (decodeLiteral n) decodeLiteral_encode_append,
      width]

def encodeFormula {n : ℕ} (formula : Formula n) : List Bool :=
  encodeList encodeClause formula.clauses

def decodeFormula (n : ℕ) (bits : List Bool) : Option (Formula n × List Bool) := do
  let (clauses, rest) ← decodeList (decodeClause n) bits
  return (⟨clauses⟩, rest)

theorem decodeFormula_encode_append {n : ℕ} (formula : Formula n) (rest : List Bool) :
    decodeFormula n (encodeFormula formula ++ rest) = some (formula, rest) := by
  cases formula with
  | mk clauses =>
    simp [encodeFormula, decodeFormula,
      decodeList_encode_append encodeClause (decodeClause n) decodeClause_encode_append]

/-- Only actual input data, without prime or occurrence proof fields. -/
structure RawInput where
  variableCount : ℕ
  formula : Formula variableCount
  modulus : ℕ

def encodeRaw (input : RawInput) : List Bool :=
  encodeNat input.variableCount ++ encodeFormula input.formula ++ encodeNat input.modulus

def decodeRawPrefix (bits : List Bool) : Option (RawInput × List Bool) := do
  let (n, rest) ← decodeNat bits
  let (formula, rest) ← decodeFormula n rest
  let (modulus, rest) ← decodeNat rest
  return (⟨n, formula, modulus⟩, rest)

def decodeRaw (bits : List Bool) : Option RawInput := do
  let (input, rest) ← decodeRawPrefix bits
  if rest.isEmpty then return input else none

theorem decodeRawPrefix_encode_append (input : RawInput) (rest : List Bool) :
    decodeRawPrefix (encodeRaw input ++ rest) = some (input, rest) := by
  cases input with
  | mk n formula modulus =>
    simp [encodeRaw, decodeRawPrefix, List.append_assoc, decodeNat_encode_append,
      decodeFormula_encode_append]

theorem decodeRaw_encode (input : RawInput) : decodeRaw (encodeRaw input) = some input := by
  have h := decodeRawPrefix_encode_append input []
  simp only [List.append_nil] at h
  simp [decodeRaw, h]

theorem decodeRaw_encode_append (input : RawInput) (rest : List Bool) :
    decodeRaw (encodeRaw input ++ rest) = if rest.isEmpty then some input else none := by
  simp [decodeRaw, decodeRawPrefix_encode_append]

theorem encodeRaw_injective : Function.Injective encodeRaw := by
  intro left right h
  have hd := congrArg decodeRaw h
  simpa only [decodeRaw_encode, Option.some.injEq] using hd

theorem encodeRaw_unique_prefix (left right : RawInput) (xs ys : List Bool)
    (h : encodeRaw left ++ xs = encodeRaw right ++ ys) : left = right ∧ xs = ys := by
  have hd := congrArg decodeRawPrefix h
  simpa only [decodeRawPrefix_encode_append, Option.some.injEq, Prod.mk.injEq] using hd

/-- Forget only proposition-valued certificates, retaining every input datum. -/
def rawInput {c₀ : ℕ} (input : ModularInput c₀) : RawInput :=
  ⟨input.variableCount, input.formula, input.modulus⟩

theorem rawInput_injective (c₀ : ℕ) : Function.Injective (@rawInput c₀) := by
  intro left right h
  cases left with
  | mk n formula bounded modulus prime lower upper =>
    cases right with
    | mk n' formula' bounded' modulus' prime' lower' upper' =>
      simp only [rawInput, RawInput.mk.injEq] at h
      obtain ⟨hn, hf, hp⟩ := h
      subst n'
      cases eq_of_heq hf
      subst modulus'
      rfl

/-- Canonical input embedding for ModularCounterResourceClaim. -/
def inputEmbedding (c₀ : ℕ) : ModularInput c₀ ↪ List Bool where
  toFun input := encodeRaw (rawInput input)
  inj' := encodeRaw_injective.comp (rawInput_injective c₀)

theorem decode_inputEmbedding {c₀ : ℕ} (input : ModularInput c₀) :
    decodeRaw (inputEmbedding c₀ input) = some (rawInput input) := decodeRaw_encode _

/-- The same explicit natural-number code supplies an output representation. -/
def naturalEmbedding : ℕ ↪ List Bool where
  toFun := encodeNat
  inj' := by
    intro m n h
    have hd := congrArg decodeNat h
    have hm := decodeNat_encode_append m []
    have hn := decodeNat_encode_append n []
    simp only [List.append_nil] at hm hn
    rw [hm, hn] at hd
    exact congrArg Prod.fst (Option.some.inj hd)

theorem encodeMany_length_le {α : Type} (encode : α → List Bool)
    (xs : List α) (budget : ℕ) (bound : ∀ x ∈ xs, (encode x).length ≤ budget) :
    (encodeMany encode xs).length ≤ xs.length * budget := by
  induction xs with
  | nil => simp [encodeMany]
  | cons x xs ih =>
    have hx := bound x (by simp)
    have hxs := ih (fun y hy => bound y (by simp [hy]))
    simp only [encodeMany, List.length_append, List.length_cons]
    nlinarith

theorem encodeLiteral_length_le {n : ℕ} (literal : Literal n) :
    (encodeLiteral literal).length ≤ 2 * (n + 1).log2 + 2 := by
  have hlog : (literal.index.val + 1).log2 ≤ (n + 1).log2 := by
    simpa only [Nat.log2_eq_log_two] using
      Nat.log_mono_right (b := 2) (by have := literal.index.isLt; omega : literal.index.val + 1 ≤ n + 1)
  simp only [encodeLiteral, List.length_append, encodeNat_length, List.length_singleton]
  omega

theorem encodeClause_length_le {n : ℕ} (clause : Clause n) :
    (encodeClause clause).length ≤ 6 * (n + 1).log2 + 11 := by
  have hwidth := clause.width_le_three
  have hprefix : (clause.literals.length + 1).log2 ≤ 2 := by
    have hlog : (clause.literals.length + 1).log2 ≤ (4 : ℕ).log2 := by
      simpa only [Nat.log2_eq_log_two] using
        Nat.log_mono_right (b := 2) (by omega : clause.literals.length + 1 ≤ 4)
    exact hlog
  have hmany := encodeMany_length_le encodeLiteral clause.literals
    (2 * (n + 1).log2 + 2) (fun literal _ => encodeLiteral_length_le literal)
  have hscale := Nat.mul_le_mul_right (2 * (n + 1).log2 + 2) hwidth
  simp only [encodeClause, encodeList, List.length_append, encodeNat_length]
  nlinarith

theorem encodeFormula_length_le {n : ℕ} (formula : Formula n) :
    (encodeFormula formula).length ≤
      2 * (formula.clauses.length + 1).log2 + 1 +
        formula.clauses.length * (6 * (n + 1).log2 + 11) := by
  have hmany := encodeMany_length_le encodeClause formula.clauses
    (6 * (n + 1).log2 + 11) (fun clause _ => encodeClause_length_le clause)
  simp only [encodeFormula, encodeList, List.length_append, encodeNat_length]
  omega

/-- Linear in the number of clauses times the variable-index bit width,
plus explicit variable-count, clause-count, and modulus headers. -/
theorem encodeRaw_length_le (input : RawInput) :
    (encodeRaw input).length ≤
      2 * (input.variableCount + 1).log2 +
      2 * (input.formula.clauses.length + 1).log2 +
      2 * (input.modulus + 1).log2 + 3 +
      input.formula.clauses.length * (6 * (input.variableCount + 1).log2 + 11) := by
  have hformula := encodeFormula_length_le input.formula
  simp only [encodeRaw, List.length_append, encodeNat_length]
  omega

theorem inputEmbedding_length_le {c₀ : ℕ} (input : ModularInput c₀) :
    (inputEmbedding c₀ input).length ≤
      2 * (input.variableCount + 1).log2 +
      2 * (input.formula.clauses.length + 1).log2 +
      2 * (input.modulus + 1).log2 + 3 +
      input.formula.clauses.length * (6 * (input.variableCount + 1).log2 + 11) :=
  encodeRaw_length_le (rawInput input)

/-- A coarse polynomial bound, useful without any logarithm conventions.
The preceding theorem records the substantially smaller binary bound. -/
theorem encodeRaw_length_le_polynomial (input : RawInput) :
    (encodeRaw input).length ≤
      2 * (input.variableCount + 1) +
      2 * (input.formula.clauses.length + 1) +
      2 * (input.modulus + 1) + 3 +
      input.formula.clauses.length * (6 * (input.variableCount + 1) + 11) := by
  have hmain := encodeRaw_length_le input
  have hn := Nat.log2_le_self (input.variableCount + 1)
  have hm := Nat.log2_le_self (input.formula.clauses.length + 1)
  have hp := Nat.log2_le_self (input.modulus + 1)
  have hprod := Nat.mul_le_mul_left input.formula.clauses.length
    (show 6 * (input.variableCount + 1).log2 + 11 ≤ 6 * (input.variableCount + 1) + 11 by omega)
  omega

/-- Counting empty clauses separately accounts for the declared canonical
convention permitting at most one empty clause. -/
theorem clauses_le_literals_add_empty {n : ℕ} (clauses : List (Clause n)) :
    clauses.length ≤ (clauses.map fun c => c.literals.length).sum +
      (clauses.filter fun c => c.literals.isEmpty).length := by
  induction clauses with
  | nil => simp
  | cons clause clauses ih =>
    cases hliterals : clause.literals with
    | nil => simp [hliterals] at *; omega
    | cons literal literals => simp [hliterals] at *; omega

theorem bounded_clause_count {n : ℕ} (formula : Formula n)
    (bounded : formula.BoundedOccurrence) : formula.clauses.length ≤ 3 * n + 1 := by
  have hcount := clauses_le_literals_add_empty formula.clauses
  have hinc := (FormulaIncidences.literalCount_le_population formula).trans
    (FormulaIncidences.population_le_three_variables formula bounded)
  unfold FormulaCounter.incidenceCount at hinc
  rw [FormulaIncidences.sum_positions_eq_list formula.clauses (fun c => c.literals.length)] at hinc
  have hempty := bounded.2.1
  omega

/-- With the actual bounded-occurrence and modulus hypotheses, input length is
polynomial in declared variable count for every fixed exponent c₀. -/
theorem inputEmbedding_length_le_polynomial {c₀ : ℕ} (input : ModularInput c₀) :
    (inputEmbedding c₀ input).length ≤
      18 * input.variableCount ^ 2 + 65 * input.variableCount +
        2 * input.variableCount ^ c₀ + 28 := by
  have hmain := encodeRaw_length_le_polynomial (rawInput input)
  have hm := bounded_clause_count input.formula input.bounded
  have hp := input.upper
  have hprod := Nat.mul_le_mul_right (6 * (input.variableCount + 1) + 11) hm
  simp only [rawInput] at hmain
  change (encodeRaw (rawInput input)).length ≤ _
  dsimp only [rawInput]
  nlinarith

end NtimeDspace.InputEncoding
