import NtimeDspace.ParserTerm
import NtimeDspace.SupportEnumeration
import NtimeDspace.SupportCardinality

/-!
# Queries on a candidate support code

For the candidate number `c` (the code word `binaryTail c`), terms for its
validity, the membership of a variable, and its number of entries, each one
run of the verified parser term `scanT`. On a valid candidate, which is the
code of a valid support (`SupportEnumeration.validate_ne_none_iff`), the
membership and size terms read that support.
-/

namespace NtimeDspace.ProgTerm

open Term ParserFold

variable {w : List Bool}

section Terms

variable (B Cap Lb M K : Term)

/-- The packed parser state on candidate `c` with query `q`. -/
def parseT (c q : Term) : Term := scanT B Cap Lb q M K c

/-- Whether candidate `c` is a valid code. -/
def codeValidT (c : Term) : Term := validT (parseT B Cap Lb M K c (const 0))

/-- Whether variable `v` lies in the support coded by `c` (query `v + 1`). -/
def codeMemT (c v : Term) : Term := foundT M (parseT B Cap Lb M K c (add v (const 1)))

/-- The number of entries of the support coded by `c`. -/
def codeSizeT (c : Term) : Term := rankT M (parseT B Cap Lb M K c (const 0))

end Terms

/-- The parameter terms of the parser for supports of `Fin n` with capacity `cap` and code
budget `budget`. -/
structure ParserParams (w : List Bool) (env : List ℕ) (n cap budget : ℕ)
    (B Cap Lb M K : Term) : Prop where
  hB : StableAt w B env
  hBv : B.denote w env = n
  hCap : StableAt w Cap env
  hCapv : Cap.denote w env = cap
  hLb : StableAt w Lb env
  hLbv : Lb.denote w env = n.log2
  hM : StableAt w M env
  hMv : M.denote w env = radix n cap
  hK : StableAt w K env
  hKv : K.denote w env = budget

variable {env : List ℕ} {n cap budget : ℕ} {B Cap Lb M K : Term}

theorem ParserParams.extend (h : ParserParams w env n cap budget B Cap Lb M K) (pre : List ℕ) :
    ParserParams w (pre ++ env) n cap budget B Cap Lb M K :=
  ⟨h.hB.extend pre, by rw [h.hB pre, h.hBv], h.hCap.extend pre, by rw [h.hCap pre, h.hCapv],
    h.hLb.extend pre, by rw [h.hLb pre, h.hLbv], h.hM.extend pre, by rw [h.hM pre, h.hMv],
    h.hK.extend pre, by rw [h.hK pre, h.hKv]⟩

/-- The scan of candidate `c` with query `q`. -/
def scanCand (n cap : ℕ) (q : Fin (n + 1)) (c : ℕ) :
    Option (BoundedSupportParser.Registers n cap) :=
  BoundedSupportParser.scan n cap q (initRegs n cap) (SupportEncoding.binaryTail c)

theorem parseT_readout (hp : ParserParams w env n cap budget B Cap Lb M K) {c q : Term}
    (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env)
    (hlt : c.denote w env < 2 ^ (budget + 1)) (hq : StableAt w q env) (query : Fin (n + 1))
    (hqv : q.denote w env = query) :
    (((parseT B Cap Lb M K c q).denote w env % 4 = 1) ↔
      (scanCand n cap query (c.denote w env)).isSome) ∧
    ∀ regs, scanCand n cap query (c.denote w env) = some regs →
      (parseT B Cap Lb M K c q).denote w env / 4 / radix n cap / radix n cap % radix n cap =
          regs.found.toNat ∧
        (parseT B Cap Lb M K c q).denote w env / 4 / radix n cap % radix n cap = regs.rank :=
  readout query _ _ (scanT_denote query B Cap Lb q M K c env hp.hB hp.hBv hp.hCap hp.hCapv
    hp.hLb hp.hLbv hq hqv hp.hM hp.hMv hc hpos (by rw [hp.hKv]; exact hlt))

theorem stableAt_parseT (hp : ParserParams w env n cap budget B Cap Lb M K) {c q : Term}
    (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env)
    (hlt : c.denote w env < 2 ^ (budget + 1)) (hq : StableAt w q env) (hqb : q.denote w env < n + 1) :
    StableAt w (parseT B Cap Lb M K c q) env := fun extra => by
  have h1 := scanT_denote ⟨q.denote w env, hqb⟩ B Cap Lb q M K c (extra ++ env)
    (hp.extend extra).hB (hp.extend extra).hBv (hp.extend extra).hCap (hp.extend extra).hCapv
    (hp.extend extra).hLb (hp.extend extra).hLbv (hq.extend extra) (by rw [hq extra])
    (hp.extend extra).hM (hp.extend extra).hMv (hc.extend extra) (by rw [hc extra]; exact hpos)
    (by rw [hc extra, (hp.extend extra).hKv]; exact hlt)
  have h2 := scanT_denote ⟨q.denote w env, hqb⟩ B Cap Lb q M K c env hp.hB hp.hBv hp.hCap hp.hCapv
    hp.hLb hp.hLbv hq rfl hp.hM hp.hMv hc hpos (by rw [hp.hKv]; exact hlt)
  unfold parseT
  rw [h1, h2, hc extra]

/-- **Validity.** -/
theorem denote_codeValidT (hp : ParserParams w env n cap budget B Cap Lb M K) {c : Term}
    (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env)
    (hlt : c.denote w env < 2 ^ (budget + 1)) :
    (codeValidT B Cap Lb M K c).denote w env =
      if SupportEnumeration.validate n cap (SupportEncoding.binaryTail (c.denote w env)) ≠ none
      then 1 else 0 := by
  have h := (parseT_readout hp hc hpos hlt (stableAt_const 0 env) ⟨0, by omega⟩ rfl).1
  unfold codeValidT validT
  rw [denote_eqT, denote_mod, denote_const, denote_const]
  have hv : SupportEnumeration.validate n cap (SupportEncoding.binaryTail (c.denote w env)) ≠ none ↔
      (scanCand n cap ⟨0, by omega⟩ (c.denote w env)).isSome := by
    unfold SupportEnumeration.validate BoundedSupportParser.lookup scanCand initRegs
    cases BoundedSupportParser.scan n cap ⟨0, by omega⟩ _ _ <;> simp
  by_cases h1 : (parseT B Cap Lb M K c (const 0)).denote w env % 4 = 1
  · rw [if_pos h1, if_pos (hv.mpr (h.mp h1))]
  · rw [if_neg h1, if_neg (fun h' => h1 (h.mpr (hv.mp h')))]

theorem stableAt_codeValidT (hp : ParserParams w env n cap budget B Cap Lb M K) {c : Term}
    (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env)
    (hlt : c.denote w env < 2 ^ (budget + 1)) : StableAt w (codeValidT B Cap Lb M K c) env :=
  StableAt.eqT ((stableAt_parseT hp hc hpos hlt (stableAt_const 0 env) (by simp)).mod
    (stableAt_const _ _)) (stableAt_const _ _)

/-- A valid candidate codes a valid support. -/
theorem exists_support_of_valid {c : ℕ}
    (h : SupportEnumeration.validate n cap (SupportEncoding.binaryTail c) ≠ none) :
    ∃ support : List (Fin n), SupportAssignment.Valid cap support ∧
      SupportEncoding.binaryTail c = SupportAssignment.encode support :=
  (SupportEnumeration.validate_ne_none_iff _).mp h

theorem scanCand_encode {c : ℕ} {support : List (Fin n)} (valid : SupportAssignment.Valid cap support)
    (code : SupportEncoding.binaryTail c = SupportAssignment.encode support) (q : Fin (n + 1)) :
    ∃ regs, scanCand n cap q c = some regs ∧ regs.rank = support.length ∧
      regs.found = decide (q.val ∈ SupportAssignment.positiveSupport support) := by
  have positive := (SupportAssignment.positiveSupport_valid_iff support).mpr valid
  have := SupportCardinality.count_encode (n := n) support valid
  unfold scanCand
  rw [code]
  unfold SupportAssignment.encode SupportEncoding.encodeSupport
  rw [BoundedSupportParser.scan_encode n cap q _
    (SupportEncoding.gapsFromSupport_pos _ positive.1 0 positive.2.1) (initRegs n cap)
    (by simpa only [initRegs] using (BoundedSupportParser.gapsFromSupport_sum_le n _ positive.1 0
      (Nat.zero_le _) positive.2.1 positive.2.2.1))
    (by simpa only [initRegs, Nat.zero_add, BoundedSupportParser.gapsFromSupport_length,
      SupportAssignment.positiveSupport, List.length_map] using positive.2.2.2)]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [initRegs, BoundedSupportParser.gapsFromSupport_length, SupportAssignment.positiveSupport]
  · simp only [initRegs, Bool.false_or]
    congr 1
    rw [SupportEncoding.supportFromGaps_gapsFromSupport]
    · exact positive.1
    · exact positive.2.1

theorem positiveIndex_mem_iff (support : List (Fin n)) (v : Fin n) :
    v.val + 1 ∈ SupportAssignment.positiveSupport support ↔ v ∈ support := by
  unfold SupportAssignment.positiveSupport SupportAssignment.positiveIndex
  constructor
  · intro h
    obtain ⟨u, hu, huv⟩ := List.mem_map.mp h
    have : u = v := Fin.ext (by omega)
    rwa [← this]
  · intro h; exact List.mem_map.mpr ⟨v, h, rfl⟩

/-- **Membership** in the support coded by a valid candidate. -/
theorem denote_codeMemT (hp : ParserParams w env n cap budget B Cap Lb M K) {c v : Term}
    (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env)
    (hlt : c.denote w env < 2 ^ (budget + 1)) (hv : StableAt w v env) (hvn : v.denote w env < n)
    {support : List (Fin n)} (valid : SupportAssignment.Valid cap support)
    (code : SupportEncoding.binaryTail (c.denote w env) = SupportAssignment.encode support) :
    (codeMemT B Cap Lb M K c v).denote w env = (decide (⟨v.denote w env, hvn⟩ ∈ support)).toNat := by
  have hq : StableAt w (add v (const 1)) env := hv.add (stableAt_const _ _)
  obtain ⟨regs, hs, -, hf⟩ := scanCand_encode valid code ⟨v.denote w env + 1, by omega⟩
  have h := (parseT_readout hp hc hpos hlt hq ⟨v.denote w env + 1, by omega⟩ (by simp)).2 regs hs
  unfold codeMemT foundT
  rw [denote_mod, denote_div, denote_div, denote_div, denote_const, hp.hMv, h.1, hf]
  simp only [positiveIndex_mem_iff support ⟨v.denote w env, hvn⟩]

/-- **Size** of the support coded by a valid candidate. -/
theorem denote_codeSizeT (hp : ParserParams w env n cap budget B Cap Lb M K) {c : Term}
    (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env)
    (hlt : c.denote w env < 2 ^ (budget + 1))
    {support : List (Fin n)} (valid : SupportAssignment.Valid cap support)
    (code : SupportEncoding.binaryTail (c.denote w env) = SupportAssignment.encode support) :
    (codeSizeT B Cap Lb M K c).denote w env = support.length := by
  obtain ⟨regs, hs, hr, -⟩ := scanCand_encode valid code ⟨0, by omega⟩
  have h := (parseT_readout hp hc hpos hlt (stableAt_const 0 env) ⟨0, by omega⟩ rfl).2 regs hs
  unfold codeSizeT rankT
  rw [denote_mod, denote_div, denote_div, denote_const, hp.hMv, h.2, hr]

end NtimeDspace.ProgTerm
