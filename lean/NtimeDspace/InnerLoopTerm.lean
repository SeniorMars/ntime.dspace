import NtimeDspace.ParserTerm
import NtimeDspace.RecoverTerm
import NtimeDspace.WGroupedInnerLoop

/-!
# The grouped inner loop as terms

Terms for the value of one constraint's multilinear extension at incidence
values, and for the product over the constraints of one group. Accessors are
term functions with residue-level contracts in every extension of the
environment.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- A term function implements `F` at the residue level in every extension of `env`. -/
def ImplZ (w : List Bool) (env : List ℕ) (P : ℕ) (f : Term → Term) (F : ℕ → ZMod P) : Prop :=
  ∀ (pre : List ℕ) (a : Term), StableAt w a (pre ++ env) →
    ((f a).denote w (pre ++ env) : ZMod P) = F (a.denote w (pre ++ env))

theorem ImplZ.extend {env : List ℕ} {P : ℕ} {f : Term → Term} {F : ℕ → ZMod P}
    (h : ImplZ w env P f F) (pre : List ℕ) : ImplZ w (pre ++ env) P f F :=
  fun pre' a ha => by rw [← List.append_assoc] at ha ⊢; exact h (pre' ++ pre) a ha

/-- `1 - v` modulo `p`, for any natural `v`. -/
def oneSubT (p v : Term) : Term := sub (add p (const 1)) (mod v p)

theorem oneSubT_cast (p v : Term) (env : List ℕ) (P : ℕ) (hP0 : 0 < P)
    (hpv : p.denote w env = P) :
    ((oneSubT p v).denote w env : ZMod P) = 1 - (v.denote w env : ZMod P) := by
  have hP : v.denote w env % P ≤ P + 1 := (Nat.mod_lt _ hP0).le.trans (Nat.le_succ P)
  simp only [oneSubT, denote_sub, denote_add, denote_mod, denote_const, hpv]
  rw [Nat.cast_sub hP, ZMod.natCast_mod]
  push_cast
  simp

/-- The value of a constraint's extension: `∑_{A < 2^ar} W(A) ∏_{i<ar} (A_i ? V_i : 1 - V_i)`. -/
def clauseValueT (p ar : Term) (weight value : Term → Term) : Term :=
  Term.sumMod p (pow2 ar) fun A => mod (mul (weight A) (Term.prodMod p ar fun i =>
    ite (bit A i) (value i) (oneSubT p (value i)))) p

theorem clauseValueT_denote (p ar : Term) (weight value : Term → Term) (env : List ℕ) (P : ℕ)
    (hP0 : 0 < P) (hp : StableAt w p env) (hpv : p.denote w env = P) (har : StableAt w ar env)
    (Wt : ℕ → ZMod P) (V : ℕ → ZMod P) (hw : ImplZ w env P weight Wt)
    (hv : ImplZ w env P value V) :
    ((clauseValueT p ar weight value).denote w env : ZMod P) =
      ∑ A ∈ Finset.range (2 ^ ar.denote w env), Wt A *
        ∏ i ∈ Finset.range (ar.denote w env),
          (if (A.testBit i) then V i else 1 - V i) := by
  rw [clauseValueT, denote_sumModZ p _ _ env P _ hp hpv (fun acc A _ => ?_), denote_pow2]
  have hp1 := hp.extend₂ acc A
  have hpv1 : p.denote w (acc :: A :: env) = P := by rw [hp.cons₂]; exact hpv
  simp only [denote_mod, denote_mul, ZMod.natCast_mod, Nat.cast_mul, hpv1]
  have hwA := hw [acc, A] (lvl env.length) (stableAt_index env acc A)
  simp only [List.cons_append, List.nil_append, denote_lvl_index] at hwA
  rw [hwA, denote_prodModZ p ar _ (acc :: A :: env) P _ hp1 hpv1 (fun acc' i _ => ?_),
    har.cons₂]
  have hidx : StableAt w (lvl (acc :: A :: env).length) ([acc', i, acc, A] ++ env) :=
    stableAt_index (acc :: A :: env) acc' i
  have hvi := hv [acc', i, acc, A] _ hidx
  simp only [List.cons_append, List.nil_append] at hvi
  have hpv2 : p.denote w (acc' :: i :: acc :: A :: env) = P := by
    show p.denote w ([acc', i, acc, A] ++ env) = P; rw [hp, hpv]
  have hAv : (lvl env.length).denote w (acc' :: i :: acc :: A :: env) = A := by
    simp [Term.denote_lvl, Nat.add_assoc]
  simp only [denote_ite, denote_bit, hAv, denote_lvl_index]
  by_cases hb : A.testBit i
  · simp only [hb, Bool.toNat_true, zero_lt_one, ite_true]
    rw [hvi, denote_lvl_index]
  · simp only [hb, Bool.toNat_false, lt_irrefl, ite_false, Bool.false_eq_true]
    rw [oneSubT_cast p _ _ P hP0 hpv2, hvi, denote_lvl_index]

/-- A two-argument term function implements `F` at the residue level. -/
def ImplZ2 (w : List Bool) (env : List ℕ) (P : ℕ) (f : Term → Term → Term)
    (F : ℕ → ℕ → ZMod P) : Prop :=
  ∀ (pre : List ℕ) (a b : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
    ((f a b).denote w (pre ++ env) : ZMod P) = F (a.denote w (pre ++ env)) (b.denote w (pre ++ env))

/-- A three-argument term function implements `F` at the residue level. -/
def ImplZ3 (w : List Bool) (env : List ℕ) (P : ℕ) (f : Term → Term → Term → Term)
    (F : ℕ → ℕ → ℕ → ZMod P) : Prop :=
  ∀ (pre : List ℕ) (a b c : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
    StableAt w c (pre ++ env) →
    ((f a b c).denote w (pre ++ env) : ZMod P) =
      F (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) (c.denote w (pre ++ env))

/-- A term function implements `F` exactly (with stable results) in every extension. -/
def ImplN (w : List Bool) (env : List ℕ) (f : Term → Term) (F : ℕ → ℕ) : Prop :=
  ∀ (pre : List ℕ) (a : Term), StableAt w a (pre ++ env) →
    (f a).denote w (pre ++ env) = F (a.denote w (pre ++ env)) ∧ StableAt w (f a) (pre ++ env)

/-- The product over the constraints of `group` of their extension values. -/
def groupValueT (p m : Term) (cGroup arity : Term → Term) (group : Term)
    (weight value : Term → Term → Term) : Term :=
  Term.prodMod p m fun e => ite (eqT (cGroup e) group)
    (clauseValueT p (arity e) (weight e) (value e)) (const 1)

theorem groupValueT_denote (p m : Term) (cGroup arity : Term → Term) (group : Term)
    (weight value : Term → Term → Term) (env : List ℕ) (P : ℕ) (hP0 : 0 < P)
    (hp : StableAt w p env) (hpv : p.denote w env = P) (hgroup : StableAt w group env)
    (CG AR : ℕ → ℕ) (hCG : ImplN w env cGroup CG) (hAR : ImplN w env arity AR)
    (Wt V : ℕ → ℕ → ZMod P) (hW : ImplZ2 w env P weight Wt) (hV : ImplZ2 w env P value V) :
    ((groupValueT p m cGroup arity group weight value).denote w env : ZMod P) =
      ∏ e ∈ Finset.range (m.denote w env),
        (if CG e = group.denote w env then
          ∑ A ∈ Finset.range (2 ^ AR e), Wt e A *
            ∏ i ∈ Finset.range (AR e), (if A.testBit i then V e i else 1 - V e i)
        else 1) := by
  rw [groupValueT, denote_prodModZ p m _ env P _ hp hpv (fun acc e _ => ?_)]
  have he : StableAt w (lvl env.length) ([acc, e] ++ env) := stableAt_index env acc e
  obtain ⟨hcg, -⟩ := hCG [acc, e] _ he
  obtain ⟨har, hars⟩ := hAR [acc, e] _ he
  simp only [List.cons_append, List.nil_append, denote_lvl_index] at hcg har hars
  simp only [denote_ite, denote_eqT, hcg, hgroup.cons₂, denote_const]
  by_cases hc : CG e = group.denote w env
  · rw [if_pos hc, if_pos one_pos, if_pos hc]
    rw [clauseValueT_denote p (arity (lvl env.length)) _ _ (acc :: e :: env) P hP0 (hp.extend₂ acc e)
      (by rw [hp.cons₂]; exact hpv) hars (Wt e) (V e) (fun pre a ha => ?_) (fun pre a ha => ?_),
      har]
    · have := hW (pre ++ [acc, e]) (lvl env.length) a (by
        rw [List.append_assoc]; exact (stableAt_index env acc e).extend pre) (by
        rw [List.append_assoc]; exact ha)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at this
      rw [this]
      congr 1
      exact ((stableAt_index (w := w) env acc e) pre).trans (denote_lvl_index env acc e)
    · have := hV (pre ++ [acc, e]) (lvl env.length) a (by
        rw [List.append_assoc]; exact (stableAt_index env acc e).extend pre) (by
        rw [List.append_assoc]; exact ha)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at this
      rw [this]
      congr 1
      exact ((stableAt_index (w := w) env acc e) pre).trans (denote_lvl_index env acc e)
  · rw [if_neg hc, if_neg (lt_irrefl 0), if_neg hc]
    simp

/-- `1` if every test `i < n` gives `1`, for `0/1`-valued tests. -/
def allT (n : Term) (test : Term → Term) : Term :=
  eqT (sumT n fun i => sub (const 1) (test i)) (const 0)

theorem allT_denote (n : Term) (test : Term → Term) (env : List ℕ) (Pr : ℕ → Prop)
    [DecidablePred Pr]
    (ht : ∀ acc i, (test (lvl env.length)).denote w (acc :: i :: env) = if Pr i then 1 else 0) :
    (allT n test).denote w env = if ∀ i < n.denote w env, Pr i then 1 else 0 := by
  rw [allT, denote_eqT, denote_sumT _ _ env (fun i => if Pr i then 0 else 1) (fun acc i => by
    simp only [denote_sub, denote_const, ht]; split_ifs <;> rfl), denote_const]
  by_cases hall : ∀ i < n.denote w env, Pr i
  · rw [if_pos hall, if_pos (Finset.sum_eq_zero fun i hi => if_pos (hall i (Finset.mem_range.mp hi)))]
  · rw [if_neg hall, if_neg]
    push_neg at hall
    obtain ⟨i, hi, hni⟩ := hall
    intro hzero
    have := (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_range.mpr hi)
    simp [hni] at this

/-- A two-argument term function implements `F` exactly, with stable results. -/
def ImplN2 (w : List Bool) (env : List ℕ) (f : Term → Term → Term) (F : ℕ → ℕ → ℕ) : Prop :=
  ∀ (pre : List ℕ) (a b : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
    (f a b).denote w (pre ++ env) = F (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) ∧
      StableAt w (f a b) (pre ++ env)

theorem ImplN.extend {env : List ℕ} {f : Term → Term} {F : ℕ → ℕ} (h : ImplN w env f F)
    (pre : List ℕ) : ImplN w (pre ++ env) f F :=
  fun pre' a ha => by rw [← List.append_assoc] at ha ⊢; exact h (pre' ++ pre) a ha

theorem ImplN2.extend {env : List ℕ} {f : Term → Term → Term} {F : ℕ → ℕ → ℕ}
    (h : ImplN2 w env f F) (pre : List ℕ) : ImplN2 w (pre ++ env) f F :=
  fun pre' a b ha hb => by
    rw [← List.append_assoc] at ha hb ⊢; exact h (pre' ++ pre) a b ha hb

theorem ImplN2.fix {env : List ℕ} {f : Term → Term → Term} {F : ℕ → ℕ → ℕ}
    (h : ImplN2 w env f F) (a : Term) (ha : StableAt w a env) :
    ImplN w env (f a) (F (a.denote w env)) :=
  fun pre b hb => by
    have := h pre a b (ha.extend pre) hb
    rw [ha pre] at this
    exact this

theorem ImplZ3.fix2 {env : List ℕ} {P : ℕ} {f : Term → Term → Term → Term}
    {F : ℕ → ℕ → ℕ → ZMod P} (h : ImplZ3 w env P f F) (a b : Term) (ha : StableAt w a env)
    (hb : StableAt w b env) : ImplZ w env P (f a b) (F (a.denote w env) (b.denote w env)) :=
  fun pre c hc => by
    have := h pre a b c (ha.extend pre) (hb.extend pre) hc
    rw [ha pre, hb pre] at this
    exact this

theorem ImplZ3.extend {env : List ℕ} {P : ℕ} {f : Term → Term → Term → Term}
    {F : ℕ → ℕ → ℕ → ZMod P} (h : ImplZ3 w env P f F) (pre : List ℕ) :
    ImplZ3 w (pre ++ env) P f F :=
  fun pre' a b c ha hb hc => by
    rw [← List.append_assoc] at ha hb hc ⊢; exact h (pre' ++ pre) a b c ha hb hc

theorem ImplZ2.extend {env : List ℕ} {P : ℕ} {f : Term → Term → Term} {F : ℕ → ℕ → ZMod P}
    (h : ImplZ2 w env P f F) (pre : List ℕ) : ImplZ2 w (pre ++ env) P f F :=
  fun pre' a b ha hb => by
    rw [← List.append_assoc] at ha hb ⊢; exact h (pre' ++ pre) a b ha hb

/-- The bit of the local assignment `mask` at variable `v`: bit `rank v` of `mask`. -/
def assignBitT (n : Term) (gOf : Term → Term) (group mask v : Term) : Term :=
  bit mask (countBeforeT n gOf group v)

/-- The support test: every support variable of `group` is set by `mask`. -/
def supportTestT (n : Term) (gOf : Term → Term) (group : Term) (sBit : Term → Term)
    (mask : Term) : Term :=
  allT n fun v => sub (const 1) (mul (eqT (gOf v) group)
    (mul (sBit v) (sub (const 1) (assignBitT n gOf group mask v))))

section Support

variable {base : List ℕ} {n : ℕ} {Group : Type*} [DecidableEq Group]
  (groupOf : Fin n → Group) (code : Group → ℕ) (code_injective : Function.Injective code)
  (gOf : Term → Term) (G : ℕ → ℕ) (hG : ImplN w base gOf G)
  (hGcode : ∀ i (h : i < n), G i = code (groupOf ⟨i, h⟩))

include code_injective hG hGcode in
theorem assignBitT_denote (nT group mask v : Term) (pre : List ℕ)
    (hn : StableAt w nT (pre ++ base)) (hnv : nT.denote w (pre ++ base) = n)
    (hgroup : StableAt w group (pre ++ base)) (target : Group)
    (hgv : group.denote w (pre ++ base) = code target)
    (hv : StableAt w v (pre ++ base)) :
    (assignBitT nT gOf group mask v).denote w (pre ++ base) =
      ((mask.denote w (pre ++ base)).testBit
        (LocalAssignmentLoop.countBefore groupOf target (v.denote w (pre ++ base)))).toNat := by
  rw [assignBitT, denote_bit, countBeforeT_denote groupOf code code_injective gOf G hG hGcode nT
    group v pre hn hgroup hv hnv target hgv]

include code_injective hG hGcode in
theorem supportTestT_denote (nT group mask : Term) (sBit : Term → Term) (SB : ℕ → ℕ)
    (hSB : ImplN w base sBit SB) (hSB01 : ∀ v, SB v ≤ 1) (pre : List ℕ)
    (hn : StableAt w nT (pre ++ base)) (hnv : nT.denote w (pre ++ base) = n)
    (hgroup : StableAt w group (pre ++ base)) (target : Group)
    (hgv : group.denote w (pre ++ base) = code target)
    (hmask : StableAt w mask (pre ++ base)) :
    (supportTestT nT gOf group sBit mask).denote w (pre ++ base) =
      if ∀ v < n, G v = code target → SB v = 1 →
          (mask.denote w (pre ++ base)).testBit
            (LocalAssignmentLoop.countBefore groupOf target v) = true then 1 else 0 := by
  rw [supportTestT, allT_denote _ _ (pre ++ base) (fun v => G v = code target → SB v = 1 →
      (mask.denote w (pre ++ base)).testBit
        (LocalAssignmentLoop.countBefore groupOf target v) = true) (fun acc v => ?_), hnv]
  have hidx : StableAt w (lvl (pre ++ base).length) ((acc :: v :: pre) ++ base) :=
    stableAt_index (pre ++ base) acc v
  obtain ⟨hg1, -⟩ := hG (acc :: v :: pre) _ hidx
  obtain ⟨hs1, -⟩ := hSB (acc :: v :: pre) _ hidx
  have hab := assignBitT_denote groupOf code code_injective gOf G hG hGcode nT group mask
    (lvl (pre ++ base).length) (acc :: v :: pre) (hn.extend [acc, v])
    (by show nT.denote w ([acc, v] ++ (pre ++ base)) = n; rw [hn, hnv])
    (hgroup.extend [acc, v]) target
    (by show group.denote w ([acc, v] ++ (pre ++ base)) = code target; rw [hgroup, hgv]) hidx
  simp only [List.cons_append] at hg1 hs1 hab
  have hv : (lvl (pre ++ base).length).denote w (acc :: v :: (pre ++ base)) = v :=
    denote_lvl_index _ _ _
  rw [hv] at hg1 hs1 hab
  rw [hmask.cons₂] at hab
  simp only [denote_sub, denote_const, denote_mul, denote_eqT, hg1, hs1, hab, hgroup.cons₂, hgv]
  have h01 := hSB01 v
  rcases (show SB v = 0 ∨ SB v = 1 by omega) with h0 | h1s
  · simp [h0]
  · by_cases h1 : G v = code target <;>
      by_cases h3 : (mask.denote w (pre ++ base)).testBit
        (LocalAssignmentLoop.countBefore groupOf target v) = true <;>
      simp [h1s, h1, h3]

/-- `∑_{v<n, v ∈ group} coef(v) · bit(v)`. -/
def measSumT (nT : Term) (gOf : Term → Term) (group : Term) (coef : Term → Term) (mask : Term) :
    Term :=
  sumT nT fun v => mul (eqT (gOf v) group) (mul (coef v) (assignBitT nT gOf group mask v))

include code_injective hG hGcode in
theorem measSumT_denote (nT group mask : Term) (coef : Term → Term) (C : ℕ → ℕ)
    (hC : ImplN w base coef C) (pre : List ℕ)
    (hn : StableAt w nT (pre ++ base)) (hnv : nT.denote w (pre ++ base) = n)
    (hgroup : StableAt w group (pre ++ base)) (target : Group)
    (hgv : group.denote w (pre ++ base) = code target)
    (hmask : StableAt w mask (pre ++ base)) :
    (measSumT nT gOf group coef mask).denote w (pre ++ base) =
      ∑ v ∈ Finset.range n, (if G v = code target then 1 else 0) * (C v *
        ((mask.denote w (pre ++ base)).testBit
          (LocalAssignmentLoop.countBefore groupOf target v)).toNat) := by
  rw [measSumT, denote_sumT _ _ (pre ++ base) _ (fun acc v => ?_), hnv]
  have hidx : StableAt w (lvl (pre ++ base).length) ((acc :: v :: pre) ++ base) :=
    stableAt_index (pre ++ base) acc v
  obtain ⟨hg1, -⟩ := hG (acc :: v :: pre) _ hidx
  obtain ⟨hc1, -⟩ := hC (acc :: v :: pre) _ hidx
  have hab := assignBitT_denote groupOf code code_injective gOf G hG hGcode nT group mask
    (lvl (pre ++ base).length) (acc :: v :: pre) (hn.extend [acc, v])
    (by show nT.denote w ([acc, v] ++ (pre ++ base)) = n; rw [hn, hnv])
    (hgroup.extend [acc, v]) target
    (by show group.denote w ([acc, v] ++ (pre ++ base)) = code target; rw [hgroup, hgv]) hidx
  simp only [List.cons_append] at hg1 hc1 hab
  have hv : (lvl (pre ++ base).length).denote w (acc :: v :: (pre ++ base)) = v :=
    denote_lvl_index _ _ _
  rw [hv] at hg1 hc1 hab
  rw [hmask.cons₂] at hab
  simp only [denote_mul, denote_eqT, hg1, hc1, hab, hgroup.cons₂, hgv]

/-- The measurement test: for every row `ρ`, `pos(ρ) + D = digit(ρ) + neg(ρ)`. -/
def measTestT (rows nT : Term) (gOf : Term → Term) (group : Term) (posC negC : Term → Term → Term)
    (tdig : Term → Term) (D mask : Term) : Term :=
  allT rows fun ρ => eqT (add (measSumT nT gOf group (posC ρ) mask) D)
    (add (tdig ρ) (measSumT nT gOf group (negC ρ) mask))

include code_injective hG hGcode in
theorem measTestT_denote (rows nT group mask D : Term) (posC negC : Term → Term → Term)
    (tdig : Term → Term) (Cp Cn : ℕ → ℕ → ℕ) (Td : ℕ → ℕ)
    (hp : ImplN2 w base posC Cp) (hneg : ImplN2 w base negC Cn) (ht : ImplN w base tdig Td)
    (pre : List ℕ) (hrows : StableAt w rows (pre ++ base))
    (hn : StableAt w nT (pre ++ base)) (hnv : nT.denote w (pre ++ base) = n)
    (hgroup : StableAt w group (pre ++ base)) (target : Group)
    (hgv : group.denote w (pre ++ base) = code target)
    (hmask : StableAt w mask (pre ++ base)) (hD : StableAt w D (pre ++ base)) :
    (measTestT rows nT gOf group posC negC tdig D mask).denote w (pre ++ base) =
      if ∀ ρ < rows.denote w (pre ++ base),
        ∑ v ∈ Finset.range n, (if G v = code target then 1 else 0) * (Cp ρ v *
            ((mask.denote w (pre ++ base)).testBit
              (LocalAssignmentLoop.countBefore groupOf target v)).toNat) + D.denote w (pre ++ base) =
          Td ρ + ∑ v ∈ Finset.range n, (if G v = code target then 1 else 0) * (Cn ρ v *
            ((mask.denote w (pre ++ base)).testBit
              (LocalAssignmentLoop.countBefore groupOf target v)).toNat)
      then 1 else 0 := by
  rw [measTestT, allT_denote _ _ (pre ++ base) (fun ρ =>
      ∑ v ∈ Finset.range n, (if G v = code target then 1 else 0) * (Cp ρ v *
          ((mask.denote w (pre ++ base)).testBit
            (LocalAssignmentLoop.countBefore groupOf target v)).toNat) + D.denote w (pre ++ base) =
        Td ρ + ∑ v ∈ Finset.range n, (if G v = code target then 1 else 0) * (Cn ρ v *
          ((mask.denote w (pre ++ base)).testBit
            (LocalAssignmentLoop.countBefore groupOf target v)).toNat)) (fun acc ρ => ?_)]
  have hρ : StableAt w (lvl (pre ++ base).length) ((acc :: ρ :: pre) ++ base) :=
    stableAt_index (pre ++ base) acc ρ
  have hρv : (lvl (pre ++ base).length).denote w ((acc :: ρ :: pre) ++ base) = ρ :=
    denote_lvl_index _ _ _
  have hpC := (hp.extend (acc :: ρ :: pre)).fix _ hρ
  have hnC := (hneg.extend (acc :: ρ :: pre)).fix _ hρ
  rw [hρv] at hpC hnC
  have hG' := hG.extend (acc :: ρ :: pre)
  have e1 := measSumT_denote (base := (acc :: ρ :: pre) ++ base) groupOf code code_injective gOf G
    hG' hGcode nT group mask (posC (lvl (pre ++ base).length)) (Cp ρ) hpC []
    (hn.extend [acc, ρ]) (by show nT.denote w ([acc, ρ] ++ (pre ++ base)) = n; rw [hn, hnv])
    (hgroup.extend [acc, ρ]) target
    (by show group.denote w ([acc, ρ] ++ (pre ++ base)) = code target; rw [hgroup, hgv])
    (hmask.extend [acc, ρ])
  have e2 := measSumT_denote (base := (acc :: ρ :: pre) ++ base) groupOf code code_injective gOf G
    hG' hGcode nT group mask (negC (lvl (pre ++ base).length)) (Cn ρ) hnC []
    (hn.extend [acc, ρ]) (by show nT.denote w ([acc, ρ] ++ (pre ++ base)) = n; rw [hn, hnv])
    (hgroup.extend [acc, ρ]) target
    (by show group.denote w ([acc, ρ] ++ (pre ++ base)) = code target; rw [hgroup, hgv])
    (hmask.extend [acc, ρ])
  obtain ⟨et, -⟩ := ht (acc :: ρ :: pre) _ hρ
  rw [hρv] at et
  simp only [List.nil_append, List.cons_append] at e1 e2 et
  simp only [denote_eqT, denote_add, e1, e2, et, hD.cons₂, hmask.cons₂]

/-- The linear value: `∑_{v ∈ group} localC(v) · bit(v) + measTerm`, modulo `p`. -/
def linearValueT (p nT : Term) (gOf : Term → Term) (group : Term) (localC : Term → Term)
    (mask measTerm : Term) : Term :=
  mod (add (Term.sumMod p nT fun v => mul (eqT (gOf v) group)
    (mul (localC v) (assignBitT nT gOf group mask v))) measTerm) p

include code_injective hG hGcode in
theorem linearValueT_denote (p nT group mask measTerm : Term) (localC : Term → Term) (P : ℕ)
    (LC : ℕ → ZMod P) (hLC : ImplZ w base P localC LC) (pre : List ℕ)
    (hp : StableAt w p (pre ++ base)) (hpv : p.denote w (pre ++ base) = P)
    (hn : StableAt w nT (pre ++ base)) (hnv : nT.denote w (pre ++ base) = n)
    (hgroup : StableAt w group (pre ++ base)) (target : Group)
    (hgv : group.denote w (pre ++ base) = code target)
    (hmask : StableAt w mask (pre ++ base)) :
    ((linearValueT p nT gOf group localC mask measTerm).denote w (pre ++ base) : ZMod P) =
      (∑ v ∈ Finset.range n, (if G v = code target then (1 : ZMod P) else 0) * (LC v *
        (((mask.denote w (pre ++ base)).testBit
          (LocalAssignmentLoop.countBefore groupOf target v)).toNat : ZMod P))) +
        (measTerm.denote w (pre ++ base) : ZMod P) := by
  simp only [linearValueT, denote_mod, denote_add, ZMod.natCast_mod, Nat.cast_add, hpv]
  rw [denote_sumModZ p nT _ (pre ++ base) P _ hp hpv (fun acc v _ => ?_), hnv]
  have hidx : StableAt w (lvl (pre ++ base).length) ((acc :: v :: pre) ++ base) :=
    stableAt_index (pre ++ base) acc v
  obtain ⟨hg1, -⟩ := hG (acc :: v :: pre) _ hidx
  have hl1 := hLC (acc :: v :: pre) _ hidx
  have hab := assignBitT_denote groupOf code code_injective gOf G hG hGcode nT group mask
    (lvl (pre ++ base).length) (acc :: v :: pre) (hn.extend [acc, v])
    (by show nT.denote w ([acc, v] ++ (pre ++ base)) = n; rw [hn, hnv])
    (hgroup.extend [acc, v]) target
    (by show group.denote w ([acc, v] ++ (pre ++ base)) = code target; rw [hgroup, hgv]) hidx
  simp only [List.cons_append] at hg1 hl1 hab
  have hv : (lvl (pre ++ base).length).denote w (acc :: v :: (pre ++ base)) = v :=
    denote_lvl_index _ _ _
  rw [hv] at hg1 hl1 hab
  rw [hmask.cons₂] at hab
  simp only [denote_mul, denote_eqT, hg1, hab, hgroup.cons₂, hgv, Nat.cast_mul, hl1]
  split_ifs <;> simp

/-- The value of incidence `(e, i)` under the local assignment `mask`. -/
def incValueT (p nT : Term) (gOf : Term → Term) (group : Term)
    (localC : Term → Term → Term → Term) (measTerm corr : Term → Term → Term) (mask e i : Term) :
    Term :=
  mod (add (linearValueT p nT gOf group (localC e i) mask (measTerm e i)) (corr e i)) p

/-- The sum over local assignments of one group. -/
def sumGroupT (p nT : Term) (gOf : Term → Term) (group : Term) (sBit : Term → Term)
    (rows : Term) (posC negC : Term → Term → Term) (tdig : Term → Term) (D m : Term)
    (cGroup arity : Term → Term) (weight : Term → Term → Term)
    (localC : Term → Term → Term → Term) (measTerm corr : Term → Term → Term) : Term :=
  Term.sumMod p (pow2 (countBeforeT nT gOf group nT)) fun mask =>
    ite (mul (measTestT rows nT gOf group posC negC tdig D mask)
        (supportTestT nT gOf group sBit mask))
      (groupValueT p m cGroup arity group weight
        (incValueT p nT gOf group localC measTerm corr mask)) (const 0)

include code_injective hG hGcode in
/-- The incidence value implements its formula in the extensions of an environment where
`mask` is stable. -/
theorem incValueT_implZ2 (p nT mask : Term) (group : Term) (localC : Term → Term → Term → Term)
    (measTerm corr : Term → Term → Term) (P : ℕ) (LC : ℕ → ℕ → ℕ → ZMod P)
    (MT CR : ℕ → ℕ → ZMod P) (hLC : ImplZ3 w base P localC LC) (hMT : ImplZ2 w base P measTerm MT)
    (hCR : ImplZ2 w base P corr CR) (env : List ℕ) (henv : ∃ pre, env = pre ++ base)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    (hgroup : StableAt w group env) (target : Group) (hgv : group.denote w env = code target)
    (hmask : StableAt w mask env) :
    ImplZ2 w env P (incValueT p nT gOf group localC measTerm corr mask) (fun e i =>
      (∑ v ∈ Finset.range n, (if G v = code target then (1 : ZMod P) else 0) * (LC e i v *
        (((mask.denote w env).testBit
          (LocalAssignmentLoop.countBefore groupOf target v)).toNat : ZMod P))) +
        MT e i + CR e i) := by
  obtain ⟨pre0, rfl⟩ := henv
  intro pre e i he hi
  have hLCei := (hLC.extend (pre ++ pre0)).fix2 e i
    (by rw [List.append_assoc]; exact he) (by rw [List.append_assoc]; exact hi)
  have hG' := hG.extend (pre ++ pre0)
  have hlin := linearValueT_denote (base := (pre ++ pre0) ++ base) groupOf code code_injective gOf G
    hG' hGcode p nT group mask (measTerm e i) (localC e i) P _ hLCei []
    (by rw [List.nil_append, List.append_assoc]; exact hp.extend pre)
    (by rw [List.nil_append, List.append_assoc, hp pre]; exact hpv)
    (by rw [List.nil_append, List.append_assoc]; exact hn.extend pre)
    (by rw [List.nil_append, List.append_assoc, hn pre]; exact hnv)
    (by rw [List.nil_append, List.append_assoc]; exact hgroup.extend pre) target
    (by rw [List.nil_append, List.append_assoc, hgroup pre]; exact hgv)
    (by rw [List.nil_append, List.append_assoc]; exact hmask.extend pre)
  simp only [List.nil_append, List.append_assoc] at hlin
  have hmt := hMT (pre ++ pre0) e i (by rw [List.append_assoc]; exact he)
    (by rw [List.append_assoc]; exact hi)
  have hcr := hCR (pre ++ pre0) e i (by rw [List.append_assoc]; exact he)
    (by rw [List.append_assoc]; exact hi)
  simp only [List.append_assoc] at hmt hcr
  have hpv' : p.denote w (pre ++ (pre0 ++ base)) = P := by rw [hp pre]; exact hpv
  simp only [incValueT, denote_mod, denote_add, ZMod.natCast_mod, Nat.cast_add, hpv', hlin, hmt,
    hcr, hmask pre]

include code_injective hG hGcode in
/-- **The group sum, as a formula over ranges.** -/
theorem sumGroupT_denote (p nT group rows D m : Term) (sBit tdig cGroup arity : Term → Term)
    (posC negC : Term → Term → Term) (weight : Term → Term → Term)
    (localC : Term → Term → Term → Term) (measTerm corr : Term → Term → Term) (P : ℕ)
    (hP0 : 0 < P) (SB Td CG AR : ℕ → ℕ) (Cp Cn : ℕ → ℕ → ℕ) (Wt : ℕ → ℕ → ZMod P)
    (LC : ℕ → ℕ → ℕ → ZMod P) (MT CR : ℕ → ℕ → ZMod P)
    (hSB : ImplN w base sBit SB) (hSB01 : ∀ v, SB v ≤ 1) (hTd : ImplN w base tdig Td)
    (hCG : ImplN w base cGroup CG) (hAR : ImplN w base arity AR)
    (hCp : ImplN2 w base posC Cp) (hCn : ImplN2 w base negC Cn) (hWt : ImplZ2 w base P weight Wt)
    (hLC : ImplZ3 w base P localC LC) (hMT : ImplZ2 w base P measTerm MT)
    (hCR : ImplZ2 w base P corr CR) (pre : List ℕ)
    (hp : StableAt w p (pre ++ base)) (hpv : p.denote w (pre ++ base) = P)
    (hn : StableAt w nT (pre ++ base)) (hnv : nT.denote w (pre ++ base) = n)
    (hgroup : StableAt w group (pre ++ base)) (target : Group)
    (hgv : group.denote w (pre ++ base) = code target)
    (hrows : StableAt w rows (pre ++ base)) (hD : StableAt w D (pre ++ base))
    (hmT : StableAt w m (pre ++ base)) :
    ((sumGroupT p nT gOf group sBit rows posC negC tdig D m cGroup arity weight localC measTerm
        corr).denote w (pre ++ base) : ZMod P) =
      ∑ mask ∈ Finset.range (2 ^ LocalAssignmentLoop.countBefore groupOf target n),
        if (∀ ρ < rows.denote w (pre ++ base),
            ∑ v ∈ Finset.range n, (if G v = code target then 1 else 0) * (Cp ρ v *
                (mask.testBit (LocalAssignmentLoop.countBefore groupOf target v)).toNat) +
              D.denote w (pre ++ base) =
            Td ρ + ∑ v ∈ Finset.range n, (if G v = code target then 1 else 0) * (Cn ρ v *
                (mask.testBit (LocalAssignmentLoop.countBefore groupOf target v)).toNat)) ∧
          (∀ v < n, G v = code target → SB v = 1 →
            mask.testBit (LocalAssignmentLoop.countBefore groupOf target v) = true) then
          ∏ e ∈ Finset.range (m.denote w (pre ++ base)),
            (if CG e = code target then
              ∑ A ∈ Finset.range (2 ^ AR e), Wt e A *
                ∏ i ∈ Finset.range (AR e),
                  (if A.testBit i then
                    (∑ v ∈ Finset.range n, (if G v = code target then (1 : ZMod P) else 0) *
                      (LC e i v * ((mask.testBit
                        (LocalAssignmentLoop.countBefore groupOf target v)).toNat : ZMod P))) +
                      MT e i + CR e i
                  else 1 - ((∑ v ∈ Finset.range n, (if G v = code target then (1 : ZMod P) else 0) *
                      (LC e i v * ((mask.testBit
                        (LocalAssignmentLoop.countBefore groupOf target v)).toNat : ZMod P))) +
                      MT e i + CR e i))
            else 1)
        else 0 := by
  rw [sumGroupT, denote_sumModZ p _ _ (pre ++ base) P _ hp hpv (fun acc mask _ => ?_), denote_pow2,
    countBeforeT_denote groupOf code code_injective gOf G hG hGcode nT group nT pre hn hgroup hn
      hnv target hgv, hnv]
  have hm : StableAt w (lvl (pre ++ base).length) ((acc :: mask :: pre) ++ base) :=
    stableAt_index (pre ++ base) acc mask
  have hmv : (lvl (pre ++ base).length).denote w ((acc :: mask :: pre) ++ base) = mask :=
    denote_lvl_index _ _ _
  have hn1 : StableAt w nT ((acc :: mask :: pre) ++ base) := hn.extend [acc, mask]
  have hnv1 : nT.denote w ((acc :: mask :: pre) ++ base) = n := by
    show nT.denote w ([acc, mask] ++ (pre ++ base)) = n; rw [hn, hnv]
  have hg1 : StableAt w group ((acc :: mask :: pre) ++ base) := hgroup.extend [acc, mask]
  have hgv1 : group.denote w ((acc :: mask :: pre) ++ base) = code target := by
    show group.denote w ([acc, mask] ++ (pre ++ base)) = code target; rw [hgroup, hgv]
  have hmt := measTestT_denote groupOf code code_injective gOf G hG hGcode rows nT group
    (lvl (pre ++ base).length) D posC negC tdig Cp Cn Td hCp hCn hTd (acc :: mask :: pre)
    (hrows.extend [acc, mask]) hn1 hnv1 hg1 target hgv1 hm (hD.extend [acc, mask])
  have hst := supportTestT_denote groupOf code code_injective gOf G hG hGcode nT group
    (lvl (pre ++ base).length) sBit SB hSB hSB01 (acc :: mask :: pre) hn1 hnv1 hg1 target hgv1 hm
  rw [hmv] at hmt hst
  simp only [List.cons_append] at hmt hst
  simp only [hrows.cons₂, hD.cons₂] at hmt
  simp only [denote_ite, denote_mul, hmt, hst, denote_const]
  by_cases h1 : ∀ ρ < rows.denote w (pre ++ base),
      ∑ v ∈ Finset.range n, (if G v = code target then 1 else 0) * (Cp ρ v *
          (mask.testBit (LocalAssignmentLoop.countBefore groupOf target v)).toNat) +
        D.denote w (pre ++ base) =
      Td ρ + ∑ v ∈ Finset.range n, (if G v = code target then 1 else 0) * (Cn ρ v *
          (mask.testBit (LocalAssignmentLoop.countBefore groupOf target v)).toNat)
  · by_cases h2 : ∀ v < n, G v = code target → SB v = 1 →
        mask.testBit (LocalAssignmentLoop.countBefore groupOf target v) = true
    · rw [if_pos h1, if_pos h2, if_pos (And.intro h1 h2), if_pos (by norm_num : 0 < 1 * 1)]
      have hval := incValueT_implZ2 groupOf code code_injective gOf G hG hGcode p nT
        (lvl (pre ++ base).length) group localC measTerm corr P LC MT CR hLC hMT hCR
        ((acc :: mask :: pre) ++ base) ⟨acc :: mask :: pre, rfl⟩ (hp.extend [acc, mask])
        (by show p.denote w ([acc, mask] ++ (pre ++ base)) = P; rw [hp, hpv]) hn1 hnv1 hg1
        target hgv1 hm
      rw [hmv] at hval
      rw [groupValueT_denote p m cGroup arity group weight _ (acc :: mask :: (pre ++ base)) P hP0
        (hp.extend [acc, mask])
        (by show p.denote w ([acc, mask] ++ (pre ++ base)) = P; rw [hp, hpv]) hg1 CG AR
        (hCG.extend (acc :: mask :: pre)) (hAR.extend (acc :: mask :: pre)) Wt _
        (hWt.extend (acc :: mask :: pre)) hval,
        show group.denote w (acc :: mask :: (pre ++ base)) = code target from hgv1]
      rw [hmT.cons₂]
    · rw [if_pos h1, if_neg h2, if_neg (fun h : _ ∧ _ => h2 h.2), mul_zero, if_neg (lt_irrefl 0)]
      simp
  · rw [if_neg h1, if_neg (fun h : _ ∧ _ => h1 h.1), zero_mul, if_neg (lt_irrefl 0)]
    simp

end Support

end NtimeDspace.ProgTerm
