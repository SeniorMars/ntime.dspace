import NtimeDspace.SupportAssignment
import Mathlib.Data.Fintype.OfMap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import NtimeDspace.SupportBounds

/-!
# Scalar enumeration of canonical support candidates

A positive integer supplies a sentinel leading bit; its remaining binary bits
enumerate every word of length at most `budget` exactly once. The executing
loop keeps a scalar cursor, remaining count, accumulator, and one current word.
It never constructs a list of all words or decodes a support list. Finite word
and support types below are specifications used to prove the exact sum.

This is an arithmetic algorithm and its finite-sum correctness proof. Allocation,
integer representation, and a tape-machine space refinement remain separate.
Parser capacity bounds support size; it does not specify assignment-mask width.
-/

namespace NtimeDspace.SupportEnumeration

open SupportEncoding
open scoped BigOperators

/-- Positive sentinels are precisely `1, …, 2^(budget+1)-1`. -/
def candidateCount (budget : ℕ) : ℕ := 2 ^ (budget + 1) - 1

abbrev Candidate (budget : ℕ) := Fin (candidateCount budget)

def candidate {budget : ℕ} (index : Candidate budget) : List Bool :=
  binaryTail (index.val + 1)

theorem candidate_length {budget : ℕ} (index : Candidate budget) :
    (candidate index).length ≤ budget := by
  have bound := index.isLt
  dsimp [candidateCount] at bound
  rw [candidate, binaryTail_length]
  have below : index.val + 1 < 2 ^ (budget + 1) := by omega
  have logarithm := (Nat.log2_lt (by omega : index.val + 1 ≠ 0)).mpr below
  omega

abbrev BoundedWord (budget : ℕ) := {word : List Bool // word.length ≤ budget}

theorem binaryValue_lt {budget : ℕ} (word : BoundedWord budget) :
    binaryValue word.val < 2 ^ (budget + 1) := by
  have length : (binaryValue word.val).log2 = word.val.length := by
    rw [← binaryTail_length, BoundedSupportParser.binaryTail_binaryValue]
  apply (Nat.log2_lt (Nat.ne_of_gt (BoundedSupportParser.binaryValue_positive word.val))).mp
  rw [length]
  exact Nat.lt_succ_of_le word.property

/-- A bijection proves both completeness and absence of duplicate candidates. -/
def candidateEquiv (budget : ℕ) : Candidate budget ≃ BoundedWord budget where
  toFun index := ⟨candidate index, candidate_length index⟩
  invFun word := ⟨binaryValue word.val - 1, by
    have positive := BoundedSupportParser.binaryValue_positive word.val
    have below := binaryValue_lt word
    dsimp [candidateCount]
    omega⟩
  left_inv index := by
    apply Fin.ext
    change binaryValue (binaryTail (index.val + 1)) - 1 = index.val
    rw [binaryValue_binaryTail _ (by omega)]
    omega
  right_inv word := by
    apply Subtype.ext
    change binaryTail (binaryValue word.val - 1 + 1) = word.val
    have positive := BoundedSupportParser.binaryValue_positive word.val
    rw [Nat.sub_add_cancel (by omega), BoundedSupportParser.binaryTail_binaryValue]

instance boundedWordFintype (budget : ℕ) : Fintype (BoundedWord budget) :=
  Fintype.ofEquiv (Candidate budget) (candidateEquiv budget)

section Accumulator

variable {R : Type*} [AddCommMonoid R]

/-- Scalar tail recursion. The callback sees one current index at a time. -/
def foldFrom (limit : ℕ) (callback : Fin limit → R) :
    (remaining cursor : ℕ) → cursor + remaining ≤ limit → R → R
  | 0, _, _, accumulator => accumulator
  | remaining + 1, cursor, fits, accumulator =>
    foldFrom limit callback remaining (cursor + 1) (by omega)
      (accumulator + callback ⟨cursor, by omega⟩)

theorem foldFrom_eq_sum (limit : ℕ) (callback : Fin limit → R)
    (remaining cursor : ℕ) (fits : cursor + remaining ≤ limit) (accumulator : R) :
    foldFrom limit callback remaining cursor fits accumulator =
      accumulator + ∑ index : Fin remaining,
        callback ⟨cursor + index.val, by have := index.isLt; omega⟩ := by
  induction remaining generalizing cursor accumulator with
  | zero => simp [foldFrom]
  | succ remaining ih =>
    rw [foldFrom, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    rw [add_assoc]
    congr 2
    apply Finset.sum_congr rfl
    intro index _
    congr 1
    apply Fin.ext
    dsimp
    omega

/-- Execute every candidate callback without building a candidate collection. -/
def enumerate (budget : ℕ) (callback : List Bool → R) (initial : R) : R :=
  foldFrom (candidateCount budget) (fun index => callback (candidate index))
    (candidateCount budget) 0 (Nat.zero_add _ ▸ le_refl _) initial

theorem enumerate_eq_sum (budget : ℕ) (callback : List Bool → R) (initial : R) :
    enumerate budget callback initial =
      initial + ∑ word : BoundedWord budget, callback word.val := by
  unfold enumerate
  rw [foldFrom_eq_sum]
  have same : (∑ index : Candidate budget, callback (candidate index)) =
      ∑ word : BoundedWord budget, callback word.val :=
    (candidateEquiv budget).sum_comp (fun word => callback word.val)
  simpa only [Nat.zero_add] using congrArg (initial + ·) same

end Accumulator

section Supports

variable {n capacity budget : ℕ}

/-- Specification-side sorted supports subject to both cardinality and code
length bounds. This type is not enumerated by the executing algorithm. -/
abbrev BoundedSupport (n capacity budget : ℕ) :=
  {support : List (Fin n) // SupportAssignment.Valid capacity support ∧
    (SupportAssignment.encode support).length ≤ budget}

def supportWord (support : BoundedSupport n capacity budget) : BoundedWord budget :=
  ⟨SupportAssignment.encode support.val, support.property.2⟩

theorem supportWord_injective :
    Function.Injective (supportWord (n := n) (capacity := capacity) (budget := budget)) := by
  intro first second same
  apply Subtype.ext
  exact SupportAssignment.encode_injective first.property.1 second.property.1
    (congrArg Subtype.val same)

noncomputable instance boundedSupportFintype (n capacity budget : ℕ) :
    Fintype (BoundedSupport n capacity budget) :=
  Fintype.ofInjective supportWord supportWord_injective

/-- A zero query exists even for zero formula variables. Validation never
needs a decoded support or a variable query in `Fin n`. -/
def validate (n capacity : ℕ) (word : List Bool) : Option Bool :=
  BoundedSupportParser.lookup n capacity ⟨0, by omega⟩ word

theorem validate_encode (support : List (Fin n))
    (valid : SupportAssignment.Valid capacity support) :
    validate n capacity (SupportAssignment.encode support) ≠ none := by
  have positive := (SupportAssignment.positiveSupport_valid_iff support).mpr valid
  unfold validate SupportAssignment.encode
  rw [BoundedSupportParser.lookup_encodeSupport n capacity ⟨0, by omega⟩
    (SupportAssignment.positiveSupport support) positive.1 positive.2.1
    positive.2.2.1 positive.2.2.2]
  exact Option.some_ne_none _

/-- Acceptance is exactly canonical support encoding, including empty input. -/
theorem validate_ne_none_iff (word : List Bool) :
    validate n capacity word ≠ none ↔
      ∃ support : List (Fin n), SupportAssignment.Valid capacity support ∧
        word = SupportAssignment.encode support := by
  constructor
  · intro accepted
    cases parsed : validate n capacity word with
    | none => exact False.elim (accepted parsed)
    | some found =>
      obtain ⟨indices, valid, encoded, _⟩ :=
        BoundedSupportParser.lookup_sound n capacity ⟨0, by omega⟩ word found parsed
      obtain ⟨support, support_valid, support_code⟩ :=
        SupportAssignment.exists_variableSupport indices valid
      refine ⟨support, support_valid, ?_⟩
      rw [SupportAssignment.encode, support_code]
      exact encoded
  · rintro ⟨support, valid, rfl⟩
    exact validate_encode support valid

theorem validate_ne_none_iff_mem_image (word : BoundedWord budget) :
    validate n capacity word.val ≠ none ↔
      word ∈ Finset.univ.image (supportWord (n := n) (capacity := capacity)) := by
  classical
  rw [validate_ne_none_iff]
  constructor
  · rintro ⟨support, valid, code⟩
    let bounded : BoundedSupport n capacity budget :=
      ⟨support, valid, by rw [← code]; exact word.property⟩
    exact Finset.mem_image.mpr ⟨bounded, Finset.mem_univ _, Subtype.ext code.symm⟩
  · intro member
    obtain ⟨support, _, same⟩ := Finset.mem_image.mp member
    exact ⟨support.val, support.property.1, (congrArg Subtype.val same).symm⟩

variable {R : Type*} [AddCommMonoid R]

/-- Any word callback agreeing on valid codes and zero on parser rejection
gives precisely the support sum, with no multiplicities from noncanonical codes. -/
theorem enumerate_support_sum (callback : List Bool → R)
    (weight : List (Fin n) → R) (initial : R)
    (agrees : ∀ support : BoundedSupport n capacity budget,
      callback (SupportAssignment.encode support.val) = weight support.val)
    (invalid_zero : ∀ word : BoundedWord budget,
      validate n capacity word.val = none → callback word.val = 0) :
    enumerate budget callback initial =
      initial + ∑ support : BoundedSupport n capacity budget, weight support.val := by
  classical
  rw [enumerate_eq_sum]
  apply congrArg (initial + ·)
  have restrict :
      (∑ word ∈ Finset.univ.image (supportWord (n := n) (capacity := capacity) (budget := budget)),
        callback word.val) = ∑ word : BoundedWord budget, callback word.val := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro word _ outside
    apply invalid_zero word
    by_contra accepted
    exact outside ((validate_ne_none_iff_mem_image word).mp accepted)
  rw [← restrict, Finset.sum_image supportWord_injective.injOn]
  exact Finset.sum_congr rfl (fun support _ => agrees support)

/-- Executing guard: the bounded streaming parser rejects before the callback
is used. It constructs no decoded support list. -/
def guarded (n capacity : ℕ) (callback : List Bool → R) (word : List Bool) : R :=
  match validate n capacity word with
  | none => 0
  | some _ => callback word

def enumerateValid (n capacity budget : ℕ) (callback : List Bool → R) (initial : R) : R :=
  enumerate budget (guarded n capacity callback) initial

/-- Exact outer support enumeration. The callback may perform its own
exact-width mask loop; no capacity-sized mask enumeration is inserted here. -/
theorem enumerateValid_correct (callback : List Bool → R)
    (weight : List (Fin n) → R) (initial : R)
    (agrees : ∀ support : BoundedSupport n capacity budget,
      callback (SupportAssignment.encode support.val) = weight support.val) :
    enumerateValid n capacity budget callback initial =
      initial + ∑ support : BoundedSupport n capacity budget, weight support.val := by
  apply enumerate_support_sum (guarded n capacity callback) weight initial
  · intro support
    have accepted := validate_encode support.val support.property.1
    unfold guarded
    cases parsed : validate n capacity (SupportAssignment.encode support.val) with
    | none => exact False.elim (accepted parsed)
    | some found => exact agrees support
  · intro word rejected
    simp only [guarded, rejected]

end Supports

section FiniteSubsets

variable {n capacity budget : ℕ}

theorem sort_toFinset_of_valid (support : List (Fin n))
    (valid : SupportAssignment.Valid capacity support) :
    support.toFinset.sort = support := by
  exact (List.toFinset_sort (· ≤ ·) valid.1.nodup).mpr
    (valid.1.imp (fun lt => le_of_lt lt))

/-- The usual finite-subset version of the specification, with a code-length
cutoff in addition to the parser's support-size cutoff. -/
def eligibleSupports (n capacity budget : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun support => support.card ≤ capacity ∧
    (SupportAssignment.encode support.sort).length ≤ budget

theorem boundedSupport_mem_eligible (support : BoundedSupport n capacity budget) :
    support.val.toFinset ∈ eligibleSupports n capacity budget := by
  simp only [eligibleSupports, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.toFinset_card_of_nodup support.property.1.1.nodup,
    sort_toFinset_of_valid support.val support.property.1]
  exact ⟨support.property.1.2, support.property.2⟩

variable {R : Type*} [AddCommMonoid R]

theorem support_sum_eq_finset_sum (weight : Finset (Fin n) → R) :
    (∑ support : BoundedSupport n capacity budget, weight support.val.toFinset) =
      ∑ support ∈ eligibleSupports n capacity budget, weight support := by
  classical
  apply Finset.sum_bij (fun support _ => support.val.toFinset)
  · intro support _
    exact boundedSupport_mem_eligible support
  · intro first _ second _ same
    apply Subtype.ext
    rw [← sort_toFinset_of_valid first.val first.property.1,
      ← sort_toFinset_of_valid second.val second.property.1, same]
  · intro support member
    have bounds := (Finset.mem_filter.mp member).2
    let bounded : BoundedSupport n capacity budget :=
      ⟨support.sort, ⟨support.sortedLT_sort.pairwise, by simpa using bounds.1⟩, bounds.2⟩
    exact ⟨bounded, Finset.mem_univ _, support.sort_toFinset _⟩
  · intro support _
    rfl

/-- Direct finite-subset form for an outer counting expression. Both the
canonical encoding and rejection are discharged by the enumeration module. -/
theorem enumerateValid_finset_sum (callback : List Bool → R)
    (weight : Finset (Fin n) → R) (initial : R)
    (agrees : ∀ support ∈ eligibleSupports n capacity budget,
      callback (SupportAssignment.encode support.sort) = weight support) :
    enumerateValid n capacity budget callback initial =
      initial + ∑ support ∈ eligibleSupports n capacity budget, weight support := by
  rw [← support_sum_eq_finset_sum]
  apply enumerateValid_correct callback (fun support => weight support.toFinset) initial
  intro support
  have agreement := agrees support.val.toFinset (boundedSupport_mem_eligible support)
  rwa [sort_toFinset_of_valid support.val support.property.1] at agreement

end FiniteSubsets

section ParameterBudget

variable {n k : ℕ}

/-- The existing aggregate gamma bound covers every admissible support. -/
theorem encode_length_le_supportLimit (support : List (Fin n))
    (valid : SupportAssignment.Valid (Parameters.q n k) support) (large : 6 ≤ k) :
    (SupportAssignment.encode support).length ≤ SupportBounds.supportLimit n k := by
  have positive := (SupportAssignment.positiveSupport_valid_iff support).mpr valid
  unfold SupportAssignment.encode SupportEncoding.encodeSupport
  apply SupportBounds.encodeGaps_length_le_supportLimit _
    (gapsFromSupport_pos _ positive.1 0 positive.2.1) n k large
  · simpa only [BoundedSupportParser.gapsFromSupport_length] using positive.2.2.2
  · simpa only [Nat.zero_add] using
      BoundedSupportParser.gapsFromSupport_sum_le n _ positive.1 0 (Nat.zero_le _)
        positive.2.1 positive.2.2.1

theorem eligibleSupports_parameter (n k : ℕ) (large : 6 ≤ k) :
    eligibleSupports n (Parameters.q n k) (SupportBounds.supportLimit n k) =
      Finset.univ.filter (fun support : Finset (Fin n) => support.card ≤ Parameters.q n k) := by
  ext support
  simp only [eligibleSupports, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.left
  · intro count
    exact ⟨count, encode_length_le_supportLimit support.sort
      ⟨support.sortedLT_sort.pairwise, by simpa using count⟩ large⟩

variable {R : Type*} [AddCommMonoid R]

/-- With the manuscript's gamma-code budget, the executing guarded loop is
the entire support sum of cardinality at most `q n k`. Its remaining premise
is the callback's mathematical value on a valid canonical code. -/
theorem enumerateValid_parameter_sum (n k : ℕ) (large : 6 ≤ k)
    (callback : List Bool → R) (weight : Finset (Fin n) → R) (initial : R)
    (agrees : ∀ support : Finset (Fin n), support.card ≤ Parameters.q n k →
      callback (SupportAssignment.encode support.sort) = weight support) :
    enumerateValid n (Parameters.q n k) (SupportBounds.supportLimit n k) callback initial =
      initial + ∑ support ∈ Finset.univ.filter
        (fun support : Finset (Fin n) => support.card ≤ Parameters.q n k), weight support := by
  rw [← eligibleSupports_parameter n k large]
  apply enumerateValid_finset_sum callback weight initial
  intro support member
  exact agrees support (Finset.mem_filter.mp member).2.1

end ParameterBudget

end NtimeDspace.SupportEnumeration
