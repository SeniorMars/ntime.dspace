import NtimeDspace.SupportQueryTerm
import NtimeDspace.FormulaLoopTerm
import NtimeDspace.WCompressedTaylorLoop

/-!
# The compressed Taylor loop as a term: support bits and corrections

Inside the Taylor loop, the support is a valid candidate code `c` and the
subset is a mask over the support's entries. The support bit of a variable is
one parser query (`sBitT`), and the mask bit of an entry is read at its rank,
the number of support entries below it (`selT`). The correction of an
incidence is the scalar sum over selected variables (`corrT`).
`implN_sBitT` and `implZ2_corrT` give the contracts the formula loop term
needs.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-! ### Ranks in sorted supports -/

/-- The number of entries of `E` below `v`, as a sum over `u < v`. -/
def countBelow {n : ℕ} (E : List (Fin n)) (v : ℕ) : ℕ :=
  ∑ u ∈ Finset.range v, if h : u < n then (if (⟨u, h⟩ : Fin n) ∈ E then 1 else 0) else 0

theorem idxOf_eq_countBelow {n : ℕ} :
    ∀ (E : List (Fin n)), E.Pairwise (· < ·) → ∀ v : Fin n, v ∈ E → E.idxOf v = countBelow E v
  | [], _, v, hv => absurd hv (by simp)
  | a :: E, hs, v, hv => by
    have hs' := List.pairwise_cons.mp hs
    have ha : a ∉ E := fun h => lt_irrefl a (hs'.1 a h)
    have hcount : ∀ m, countBelow (a :: E) m = (if a.val < m then 1 else 0) + countBelow E m := by
      intro m
      unfold countBelow
      rw [show (if a.val < m then 1 else 0) = ∑ u ∈ Finset.range m,
          (if h : u < n then (if (⟨u, h⟩ : Fin n) = a then 1 else 0) else 0) by
        by_cases hm : a.val < m
        · rw [if_pos hm, Finset.sum_eq_single a.val]
          · simp only [dif_pos a.isLt, Fin.eta, if_true]
          · intro u _ hu
            split_ifs with h1 h2
            · exact absurd (congrArg Fin.val h2) hu
            · rfl
            · rfl
          · intro h; exact absurd (Finset.mem_range.mpr hm) h
        · rw [if_neg hm]
          refine (Finset.sum_eq_zero fun u hu => ?_).symm
          simp only [Finset.mem_range] at hu
          split_ifs with h1 h2
          · exact absurd (congrArg Fin.val h2) (by simp only; omega)
          · rfl
          · rfl]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h : u < n
      · simp only [dif_pos h, List.mem_cons]
        by_cases h1 : (⟨u, h⟩ : Fin n) = a
        · subst h1; simp [ha]
        · simp [h1]
      · simp [h]
    rcases List.mem_cons.mp hv with rfl | hv'
    · rw [List.idxOf_cons_self, hcount, if_neg (lt_irrefl _), zero_add]
      unfold countBelow
      refine (Finset.sum_eq_zero fun u hu => ?_).symm
      split_ifs with h1 h2
      · have := hs'.1 _ h2
        simp only [Finset.mem_range] at hu
        exact absurd this (by rw [Fin.lt_def]; simp only; omega)
      · rfl
      · rfl
    · have hne : a ≠ v := fun h => ha (h ▸ hv')
      rw [List.idxOf_cons_ne _ hne, hcount, if_pos (Fin.lt_def.mp (hs'.1 v hv')),
        idxOf_eq_countBelow E hs'.2 v hv']
      omega

/-! ### Support bits, mask bits and corrections -/

section Terms

variable (B Cap Lb M K : Term)

/-- The support bit of variable `v` (zero from `n` on). -/
def sBitT (nT c v : Term) : Term := ite (lt v nT) (codeMemT B Cap Lb M K c v) (const 0)

/-- Whether variable `v` is selected by the mask: a support entry whose rank bit is set. -/
def selT (c mask v : Term) : Term :=
  mul (codeMemT B Cap Lb M K c v) (bit mask (sumT v fun u => codeMemT B Cap Lb M K c u))

/-- The correction of incidence `(e, i)`: the sum over selected variables of the change of the
coefficient evaluation from `node` to `node + point`, modulo `p`. -/
def corrT (p nT : Term) (evalC : Term → Term → Term → Term → Term) (node point c mask : Term)
    (e i : Term) : Term :=
  Term.sumMod p nT fun v => ite (selT B Cap Lb M K c mask v)
    (mod (add (evalC e i v (add node point)) (sub p (mod (evalC e i v node) p))) p) (const 0)

end Terms

variable {env : List ℕ} {n cap budget : ℕ} {B Cap Lb M K : Term}

/-- `sumT` with body facts needed only below the bound. -/
theorem denote_sumT_lt (n : Term) (body : Term → Term) (env : List ℕ) (c : ℕ → ℕ)
    (hb : ∀ acc k, k < n.denote w env → (body (lvl env.length)).denote w (acc :: k :: env) = c k) :
    (sumT n body).denote w env = ∑ k ∈ Finset.range (n.denote w env), c k := by
  simp only [sumT, denote_foldT, denote_const]
  have key : ∀ m, m ≤ n.denote w env →
      foldAcc w (fun acc i => add acc (body i)) env 0 m = ∑ k ∈ Finset.range m, c k := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [foldAcc_succ, Finset.sum_range_succ, ← ih (by omega)]
      simp only [denote_add, denote_lvl_acc]
      rw [hb _ m (by omega)]
  exact key _ le_rfl

/-- The support bit function of `E`. -/
def sBitN {n : ℕ} (E : List (Fin n)) (v : ℕ) : ℕ :=
  if h : v < n then (decide ((⟨v, h⟩ : Fin n) ∈ E)).toNat else 0

theorem implN_sBitT (hp : ParserParams w env n cap budget B Cap Lb M K) {nT c : Term}
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env) (hlt : c.denote w env < 2 ^ (budget + 1))
    {E : List (Fin n)} (valid : SupportAssignment.Valid cap E)
    (code : SupportEncoding.binaryTail (c.denote w env) = SupportAssignment.encode E) :
    ImplN w env (sBitT B Cap Lb M K nT c) (sBitN E) := by
  have key : ∀ (pre : List ℕ) (a : Term), StableAt w a (pre ++ env) →
      (sBitT B Cap Lb M K nT c a).denote w (pre ++ env) = sBitN E (a.denote w (pre ++ env)) := by
    intro pre a ha
    unfold sBitT sBitN
    rw [denote_ite, denote_lt, hn pre, hnv]
    by_cases h : a.denote w (pre ++ env) < n
    · rw [if_pos (by simp [h]), dif_pos h,
        denote_codeMemT (hp.extend pre) (hc.extend pre) (by rw [hc pre]; exact hpos)
          (by rw [hc pre]; exact hlt) ha h valid (by rw [hc pre]; exact code)]
    · rw [if_neg (by simp [h]), dif_neg h]; rfl
  intro pre a ha
  refine ⟨key pre a ha, fun extra => ?_⟩
  rw [← List.append_assoc, key _ a (by rw [List.append_assoc]; exact ha.extend extra),
    List.append_assoc, ha extra, key pre a ha]

theorem sBitN_le {n : ℕ} (E : List (Fin n)) (v : ℕ) : sBitN E v ≤ 1 := by
  unfold sBitN; split_ifs <;> simp [Bool.toNat_le]

/-- The selected variables: support entries whose rank bit in `mask` is set. -/
def selN {n : ℕ} (E : List (Fin n)) (mask v : ℕ) : Bool :=
  if h : v < n then decide ((⟨v, h⟩ : Fin n) ∈ E) && mask.testBit (countBelow E v) else false

theorem denote_selT (hp : ParserParams w env n cap budget B Cap Lb M K) {c mask : Term}
    (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env) (hlt : c.denote w env < 2 ^ (budget + 1))
    {E : List (Fin n)} (valid : SupportAssignment.Valid cap E)
    (code : SupportEncoding.binaryTail (c.denote w env) = SupportAssignment.encode E)
    {v : Term} (hv : StableAt w v env) (hvn : v.denote w env < n) :
    (selT B Cap Lb M K c mask v).denote w env = (selN E (mask.denote w env) (v.denote w env)).toNat := by
  unfold selT selN
  rw [denote_mul, denote_codeMemT hp hc hpos hlt hv hvn valid code, denote_bit, dif_pos hvn,
    denote_sumT_lt _ _ env (fun u => if h : u < n then (if (⟨u, h⟩ : Fin n) ∈ E then 1 else 0) else 0)]
  · unfold countBelow
    cases decide ((⟨v.denote w env, hvn⟩ : Fin n) ∈ E) <;> simp
  · intro acc u huv
    have hun : u < n := by omega
    have hu : StableAt w (lvl env.length) ([acc, u] ++ env) := stableAt_lvl (by simp)
    have hu' : (lvl env.length).denote w (acc :: u :: env) = u := denote_lvl_index env acc u
    have h := denote_codeMemT (hp.extend [acc, u]) (hc.extend [acc, u])
      (by rw [hc [acc, u]]; exact hpos) (by rw [hc [acc, u]]; exact hlt) hu
      (by simpa using hun) valid (by rw [hc [acc, u]]; exact code)
    simp only [List.cons_append, List.nil_append] at h
    rw [h, dif_pos hun]
    by_cases hm : (⟨u, hun⟩ : Fin n) ∈ E <;> simp [hu', hm]

theorem cast_mod_add_sub_mod (P a b : ℕ) (hP : 0 < P) :
    (((a + (P - b % P)) % P : ℕ) : ZMod P) = (a : ZMod P) - b := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ hP).le, ZMod.natCast_self,
    ZMod.natCast_mod]
  ring

/-- **The correction contract.** -/
theorem implZ2_corrT (hp : ParserParams w env n cap budget B Cap Lb M K) {pT nT : Term} {P : ℕ}
    (hP : 0 < P) (hpT : StableAt w pT env) (hpv : pT.denote w env = P)
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    {c mask node point : Term} (hc : StableAt w c env) (hpos : 1 ≤ c.denote w env)
    (hlt : c.denote w env < 2 ^ (budget + 1)) (hmask : StableAt w mask env)
    (hnode : StableAt w node env) (hpoint : StableAt w point env)
    {E : List (Fin n)} (valid : SupportAssignment.Valid cap E)
    (code : SupportEncoding.binaryTail (c.denote w env) = SupportAssignment.encode E)
    {evalC : Term → Term → Term → Term → Term} {EC : ℕ → ℕ → ℕ → ℕ → ZMod P}
    (iEC : ImplZ4 w env P evalC EC) :
    ImplZ2 w env P (corrT B Cap Lb M K pT nT evalC node point c mask) (fun e i =>
      ∑ v ∈ Finset.range n, if selN E (mask.denote w env) v then
        EC e i v (node.denote w env + point.denote w env) - EC e i v (node.denote w env) else 0) := by
  intro pre a b ha hb
  unfold corrT
  rw [denote_sumModZ pT nT _ (pre ++ env) P (fun v => if selN E (mask.denote w env) v then
      EC (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) v
        (node.denote w env + point.denote w env) -
      EC (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) v (node.denote w env) else 0)
    (hpT.extend pre) (by rw [hpT pre, hpv]), hn pre, hnv]
  intro acc v hv
  rw [hn pre, hnv] at hv
  set env' := acc :: v :: (pre ++ env)
  have e' : env' = ([acc, v] ++ pre) ++ env := rfl
  have hp' := hp.extend ([acc, v] ++ pre)
  rw [← e'] at hp'
  have hc' : StableAt w c env' := by rw [e']; exact hc.extend _
  have hcv : c.denote w env' = c.denote w env := by rw [e']; exact hc _
  have hvs : StableAt w (lvl (pre ++ env).length) env' := stableAt_lvl (by simp [env'])
  have hvv : (lvl (pre ++ env).length).denote w env' = v := denote_lvl_index _ acc v
  have hmv : mask.denote w env' = mask.denote w env := by rw [e']; exact hmask _
  have hsel := denote_selT (mask := mask) hp' hc' (by rw [hcv]; exact hpos) (by rw [hcv]; exact hlt)
    valid (by rw [hcv]; exact code) hvs (by rw [hvv]; exact hv)
  have ha' : StableAt w a ([acc, v] ++ (pre ++ env)) := ha.extend _
  have hb' : StableAt w b ([acc, v] ++ (pre ++ env)) := hb.extend _
  have hnp : StableAt w (add node point) ([acc, v] ++ pre ++ env) :=
    (hnode.add hpoint).extend _
  have hnd : StableAt w node ([acc, v] ++ pre ++ env) := hnode.extend _
  have e1 := iEC ([acc, v] ++ pre) a b (lvl (pre ++ env).length) (add node point)
    (by rw [List.append_assoc]; exact ha') (by rw [List.append_assoc]; exact hb')
    (by rw [← e']; exact hvs) hnp
  have e2 := iEC ([acc, v] ++ pre) a b (lvl (pre ++ env).length) node
    (by rw [List.append_assoc]; exact ha') (by rw [List.append_assoc]; exact hb')
    (by rw [← e']; exact hvs) hnd
  rw [← e'] at e1 e2
  rw [denote_ite, hsel, hvv, hmv]
  have hpv' : pT.denote w env' = P := by rw [e']; rw [hpT _, hpv]
  have hav : a.denote w env' = a.denote w (pre ++ env) := ha [acc, v]
  have hbv : b.denote w env' = b.denote w (pre ++ env) := hb [acc, v]
  have hnodev : node.denote w env' = node.denote w env := by rw [e']; exact hnode _
  have hpointv : point.denote w env' = point.denote w env := by rw [e']; exact hpoint _
  cases hs : selN E (mask.denote w env) v
  · simp
  · simp only [Bool.toNat_true, Nat.lt_one_iff, zero_lt_one, if_true, denote_mod, denote_add,
      denote_sub, hpv', if_true]
    rw [cast_mod_add_sub_mod P _ _ hP]
    have c1 : ((evalC a b (lvl (pre ++ env).length) (add node point)).denote w env' : ZMod P) =
        EC (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) v
          (node.denote w env + point.denote w env) := by
      rw [e1, hav, hbv, hvv, denote_add, hnodev, hpointv]
    have c2 : ((evalC a b (lvl (pre ++ env).length) node).denote w env' : ZMod P) =
        EC (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) v (node.denote w env) := by
      rw [e2, hav, hbv, hvv, hnodev]
    rw [c1, c2]

end NtimeDspace.ProgTerm
