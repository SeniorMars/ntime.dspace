import NtimeDspace.PlacementBalance
import NtimeDspace.NetGraphTerm

/-!
# Copy ranks, the balance check, and the seed search as terms

`copyRankT` computes copy ranks, `balT` checks `balN` for a seed number, and
`seedT` finds the first balanced seed number below `2^(2 Q bits (IB + 1))`.
Labels are read through a seed-dependent term `lbOf s e i`.
-/

namespace NtimeDspace.ProgTerm

open Term Placement WeightedSystem

variable {w : List Bool}

section Def

variable (mT : Term) (arity : Term → Term)

/-- Lexicographic comparison of incidences `(e', i') < (e, i)`. -/
def lexT (e' i' e i : Term) : Term := lt (const 0) (add (lt e' e) (mul (eqT e' e) (lt i' i)))

/-- The rank of `(e, i)` among earlier incidences with the same label. -/
def copyRankT (lbT : Term → Term → Term) (e i : Term) : Term :=
  incSumT mT arity fun e' i' => mul (lexT e' i' e i) (eqT (lbT e' i') (lbT e i))

end Def

theorem denote_lexT (e' i' e i : Term) (env : List ℕ) :
    (lexT e' i' e i).denote w env =
      if e'.denote w env < e.denote w env ∨
        (e'.denote w env = e.denote w env ∧ i'.denote w env < i.denote w env) then 1 else 0 := by
  unfold lexT
  simp only [denote_lt, denote_add, denote_mul, denote_eqT, denote_const]
  by_cases h1 : e'.denote w env < e.denote w env <;>
    by_cases h2 : e'.denote w env = e.denote w env <;>
    by_cases h3 : i'.denote w env < i.denote w env <;> simp [h1, h2, h3]

variable {n : ℕ}

/-- Ranks on numbers. -/
noncomputable def rankNum (formula : System n) (LB : ℕ → ℕ → ℕ) (e i : ℕ) : ℕ :=
  ∑ inc : Incidence formula,
    if ((inc.1 : ℕ) < e ∨ ((inc.1 : ℕ) = e ∧ (inc.2 : ℕ) < i)) ∧ LB inc.1 inc.2 = LB e i then 1 else 0

theorem rankNum_eq_rankN (formula : System n) (LB : ℕ → ℕ → ℕ) (inc : Incidence formula) :
    rankNum formula LB inc.1 inc.2 = rankN formula (fun b => LB b.1 b.2) inc := by
  unfold rankNum rankN lexLt
  rfl

theorem implN2_copyRankT (formula : System n) {mT : Term} {arity : Term → Term}
    {lbT : Term → Term → Term} {env : List ℕ} (hm : StableAt w mT env)
    (hmv : mT.denote w env = formula.constraints.length)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    {LB : ℕ → ℕ → ℕ} (iLB : ImplN2 w env lbT LB) :
    ImplN2 w env (copyRankT mT arity lbT) (rankNum formula LB) := by
  have key : ∀ (pre : List ℕ) (a b : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
      (copyRankT mT arity lbT a b).denote w (pre ++ env) =
        rankNum formula LB (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) := by
    intro pre a b ha hb
    unfold copyRankT rankNum
    refine denote_incSumT formula (by rw [hm pre, hmv]) (iAR.extend pre) hAR (fun e' i' =>
      if (e' < a.denote w (pre ++ env) ∨ (e' = a.denote w (pre ++ env) ∧ i' < b.denote w (pre ++ env)))
        ∧ LB e' i' = LB (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) then 1 else 0) ?_
    intro pre2 e' i' he hi _ _
    obtain ⟨l1, -⟩ := (iLB.extend pre) pre2 e' i' he hi
    obtain ⟨l2, -⟩ := (iLB.extend pre) pre2 a b (ha.extend pre2) (hb.extend pre2)
    rw [denote_mul, denote_lexT, denote_eqT, l1, l2, ha pre2, hb pre2]
    split_ifs <;> simp_all
  intro pre a b ha hb
  refine ⟨key pre a b ha hb, fun extra => ?_⟩
  rw [← List.append_assoc, key _ a b (by rw [List.append_assoc]; exact ha.extend extra)
    (by rw [List.append_assoc]; exact hb.extend extra), List.append_assoc, ha extra, hb extra,
    key pre a b ha hb]

/-! ### The balance check -/

section Bal

variable (QT bitsT IBT nT mT : Term) (arity : Term → Term) (lbOf : Term → Term → Term → Term)

def labelSpaceT : Term := powT (mul (pow2 bitsT) (pow2 bitsT)) QT

/-- The balance check of seed number `s`. -/
def balT (s : Term) : Term :=
  mul (allT (labelSpaceT QT bitsT) fun m =>
      LocalSim.leT' (mul (incSumT mT arity fun e' i' => eqT (lbOf s e' i') m) (labelSpaceT QT bitsT))
        (mul (const 2) (incSumT mT arity fun _ _ => const 1)))
    (allT QT fun node => allT (pow2 bitsT) fun g =>
      LocalSim.leT' (mul (sumT nT fun v => eqT (grpT QT bitsT IBT s (const 0) node v) g) (pow2 bitsT))
        (mul (const 2) nT))

end Bal

theorem incidenceCount_eq_card (formula : System n) :
    incidenceCount formula = ∑ _inc : Incidence formula, 1 := by
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, WSchedulePlacement.card_incidence]

open Classical in
theorem denote_balT (S : System n) (Q bits : ℕ) {QT bitsT IBT nT mT s : Term}
    {arity : Term → Term} {lbOf : Term → Term → Term → Term} {env : List ℕ}
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hb : StableAt w bitsT env)
    (hbv : bitsT.denote w env = bits) (hIB : StableAt w IBT env)
    (hIBv : IBT.denote w env = WSchedulePlacement.inputBits S) (hn : StableAt w nT env)
    (hnv : nT.denote w env = n) (hm : StableAt w mT env)
    (hmv : mT.denote w env = S.constraints.length) (hs : StableAt w s env)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = (S.constraints[e]).scope.length)
    {LBs : ℕ → ℕ → ℕ} (iLB : ImplN2 w env (lbOf s) LBs)
    (hLB : ∀ inc : Incidence S, LBs inc.1 inc.2 = incLabelN S Q bits (s.denote w env) inc) :
    (balT QT bitsT IBT nT mT arity lbOf s).denote w env =
      if balN S Q bits (s.denote w env) then 1 else 0 := by
  have hLS : (labelSpaceT QT bitsT).denote w env = (2 ^ bits * 2 ^ bits) ^ Q := by
    unfold labelSpaceT
    rw [powT_denote _ _ _ (hb.pow2.mul hb.pow2)]; simp [hbv, hQv]
  have hLSs : StableAt w (labelSpaceT QT bitsT) env := StableAt.powT (hb.pow2.mul hb.pow2) hQ
  -- the label-bucket test
  have h1 : (allT (labelSpaceT QT bitsT) fun m =>
      LocalSim.leT' (mul (incSumT mT arity fun e' i' => eqT (lbOf s e' i') m) (labelSpaceT QT bitsT))
        (mul (const 2) (incSumT mT arity fun _ _ => const 1))).denote w env =
      if ∀ m < (2 ^ bits * 2 ^ bits) ^ Q,
        (∑ inc : Incidence S, if incLabelN S Q bits (s.denote w env) inc = m then 1 else 0) *
          (2 ^ bits * 2 ^ bits) ^ Q ≤ 2 * incidenceCount S then 1 else 0 := by
    rw [allT_denote_lt _ _ env (fun m =>
      (∑ inc : Incidence S, if incLabelN S Q bits (s.denote w env) inc = m then 1 else 0) *
        (2 ^ bits * 2 ^ bits) ^ Q ≤ 2 * incidenceCount S) (fun acc m _ => ?_), hLS]
    have e' : acc :: m :: env = [acc, m] ++ env := rfl
    have hcount : (incSumT mT arity fun e' i' => eqT (lbOf s e' i') (lvl env.length)).denote w
        (acc :: m :: env) = ∑ inc : Incidence S, if incLabelN S Q bits (s.denote w env) inc = m
          then 1 else 0 := by
      rw [e', denote_incSumT S (by rw [hm _, hmv]) (iAR.extend _) hAR
        (fun e i => if LBs e i = m then 1 else 0)]
      · exact Finset.sum_congr rfl fun inc _ => by rw [hLB]
      intro pre2 e2 i2 he hi _ _
      obtain ⟨l1, -⟩ := (iLB.extend [acc, m]) pre2 e2 i2 he hi
      have hmv' : (lvl env.length).denote w (pre2 ++ ([acc, m] ++ env)) = m := by
        rw [((stableAt_lvl (by simp) : StableAt w (lvl env.length) ([acc, m] ++ env))) pre2]
        exact denote_lvl_index env acc m
      rw [denote_eqT, l1, hmv']
    have hinc : (incSumT mT arity fun _ _ => const 1).denote w (acc :: m :: env) = incidenceCount S := by
      rw [e', denote_incSumT S (by rw [hm _, hmv]) (iAR.extend _) hAR (fun _ _ => 1),
        incidenceCount_eq_card]
      intro pre2 e2 i2 _ _ _ _
      rfl
    have hLS' : (labelSpaceT QT bitsT).denote w (acc :: m :: env) = (2 ^ bits * 2 ^ bits) ^ Q := by
      rw [hLSs.cons₂, hLS]
    rw [LocalSim.denote_leT', denote_mul, denote_mul, hcount, hLS', denote_const, hinc]
  -- the group test
  have h2 : (allT QT fun node => allT (pow2 bitsT) fun g =>
      LocalSim.leT' (mul (sumT nT fun v => eqT (grpT QT bitsT IBT s (const 0) node v) g)
        (pow2 bitsT)) (mul (const 2) nT)).denote w env =
      if ∀ node < Q, ∀ g < 2 ^ bits,
        (∑ v ∈ Finset.range n, if grpN Q bits (WSchedulePlacement.inputBits S) (s.denote w env) 0
          node v = g then 1 else 0) * 2 ^ bits ≤ 2 * n then 1 else 0 := by
    rw [allT_denote_lt _ _ env (fun node => ∀ g < 2 ^ bits,
      (∑ v ∈ Finset.range n, if grpN Q bits (WSchedulePlacement.inputBits S) (s.denote w env) 0
          node v = g then 1 else 0) * 2 ^ bits ≤ 2 * n) (fun acc node _ => ?_), hQv]
    set E1 := acc :: node :: env
    have hE1 : E1 = [acc, node] ++ env := rfl
    have hbv1 : bitsT.denote w E1 = bits := by rw [hb.cons₂, hbv]
    rw [allT_denote_lt _ _ E1 (fun g =>
      (∑ v ∈ Finset.range n, if grpN Q bits (WSchedulePlacement.inputBits S) (s.denote w env) 0
          node v = g then 1 else 0) * 2 ^ bits ≤ 2 * n) (fun acc' g _ => ?_), denote_pow2, hbv1]
    set E2 := acc' :: g :: E1
    have hE2 : E2 = [acc', g, acc, node] ++ env := rfl
    have hnodev : (lvl env.length).denote w E2 = node := by
      rw [denote_lvl]; simp only [E2, E1, List.length_cons]
      rw [show env.length + 1 + 1 + 1 + 1 - env.length - 1 = 3 by omega]; rfl
    have hgv : (lvl E1.length).denote w E2 = g := denote_lvl_index E1 acc' g
    have hsum : (sumT nT fun v => eqT (grpT QT bitsT IBT s (const 0) (lvl env.length) v)
        (lvl E1.length)).denote w E2 = ∑ v ∈ Finset.range n,
          if grpN Q bits (WSchedulePlacement.inputBits S) (s.denote w env) 0 node v = g then 1 else 0 := by
      have hnE2 : nT.denote w E2 = n := by rw [hE2, hn _, hnv]
      rw [denote_sumT_lt _ _ E2 (fun v => if grpN Q bits (WSchedulePlacement.inputBits S)
        (s.denote w env) 0 node v = g then 1 else 0), hnE2]
      intro acc'' v _
      set E3 := acc'' :: v :: E2
      have hE3 : E3 = [acc'', v, acc', g, acc, node] ++ env := rfl
      have hnode3 : (lvl env.length).denote w E3 = node := by
        rw [denote_lvl]; simp only [E3, E2, E1, List.length_cons]
        rw [show env.length + 1 + 1 + 1 + 1 + 1 + 1 - env.length - 1 = 5 by omega]; rfl
      have hg3 : (lvl E1.length).denote w E3 = g := by
        rw [denote_lvl]; simp only [E3, E2, E1, List.length_cons]
        rw [show env.length + 1 + 1 + 1 + 1 + 1 + 1 - (env.length + 1 + 1) - 1 = 3 by omega]; rfl
      have hv3 : (lvl E2.length).denote w E3 = v := denote_lvl_index E2 acc'' v
      have hl1 : env.length < ([acc'', v, acc', g, acc, node] ++ env).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hl2 : E2.length < ([acc'', v, acc', g, acc, node] ++ env).length := by
        simp only [E2, E1, List.length_append, List.length_cons, List.length_nil]; omega
      rw [denote_eqT, hE3, denote_grpT (hIB.extend _) (hQ.extend _) (hb.extend _) (hs.extend _)
        (stableAt_const _ _) (stableAt_lvl hl1) (stableAt_lvl hl2), ← hE3]
      rw [hnode3, hg3, hv3]
      simp only [hE3, hIB _, hQ _, hb _, hs _, hIBv, hQv, hbv, denote_const]
    have hnE2 : nT.denote w E2 = n := by rw [hE2, hn _, hnv]
    have hbE2 : bitsT.denote w E2 = bits := by rw [hE2, hb _, hbv]
    rw [LocalSim.denote_leT', denote_mul, denote_mul, hsum, denote_pow2, hbE2, denote_const, hnE2]
  unfold balT balN
  rw [denote_mul, h1, h2, LocalSim.ind_mul]

/-! ### The seed search -/

section Search

variable (QT bitsT IBT nT mT : Term) (arity : Term → Term) (lbOf : Term → Term → Term → Term)

def blkT : Term := mul (mul QT bitsT) (add IBT (const 1))

/-- One more than the first balanced seed number (zero when there is none). -/
def firstSeedT : Term :=
  foldT (pow2 (mul (const 2) (blkT QT bitsT IBT))) (const 0) fun acc s =>
    ite (mul (eqT acc (const 0)) (balT QT bitsT IBT nT mT arity lbOf s)) (add s (const 1)) acc

/-- The first balanced seed number. -/
def seedT : Term := sub (firstSeedT QT bitsT IBT nT mT arity lbOf) (const 1)

end Search

open Classical in
theorem denote_firstSeedT (S : System n) (Q bits : ℕ) {QT bitsT IBT nT mT : Term}
    {arity : Term → Term} {lbOf : Term → Term → Term → Term} {env : List ℕ}
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hb : StableAt w bitsT env)
    (hbv : bitsT.denote w env = bits) (hIB : StableAt w IBT env)
    (hIBv : IBT.denote w env = WSchedulePlacement.inputBits S) (hn : StableAt w nT env)
    (hnv : nT.denote w env = n) (hm : StableAt w mT env)
    (hmv : mT.denote w env = S.constraints.length)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = (S.constraints[e]).scope.length)
    {LBf : ℕ → ℕ → ℕ → ℕ}
    (iLB : ∀ (pre : List ℕ) (sT : Term), StableAt w sT (pre ++ env) →
      ImplN2 w (pre ++ env) (lbOf sT) (LBf (sT.denote w (pre ++ env))))
    (hLB : ∀ sv (inc : Incidence S), LBf sv inc.1 inc.2 = incLabelN S Q bits sv inc) :
    (firstSeedT QT bitsT IBT nT mT arity lbOf).denote w env =
      LocalSim.optCode ((List.range (2 ^ (2 * blk Q bits (WSchedulePlacement.inputBits S)))).find?
        fun s => decide (balN S Q bits s)) := by
  unfold firstSeedT
  rw [denote_foldT, denote_const, foldAcc_eq _ env (fun acc s =>
    if acc = 0 ∧ decide (balN S Q bits s) = true then s + 1 else acc)]
  · rw [show (List.range ((pow2 (mul (const 2) (blkT QT bitsT IBT))).denote w env)).foldl _ 0 =
      LocalSim.firstNum _ _ from rfl, LocalSim.firstNum_eq]
    congr 3
    simp [blkT, hQv, hbv, hIBv, blk]
  · intro acc sv
    have e' : acc :: sv :: env = [acc, sv] ++ env := rfl
    have hsv : StableAt w (lvl env.length) ([acc, sv] ++ env) := stableAt_lvl (by simp)
    have hsvv : (lvl env.length).denote w ([acc, sv] ++ env) = sv := denote_lvl_index env acc sv
    rw [denote_ite, denote_mul, denote_eqT, denote_lvl_acc, denote_const, e',
      denote_balT S Q bits (hQ.extend _) (by rw [hQ _, hQv]) (hb.extend _) (by rw [hb _, hbv])
        (hIB.extend _) (by rw [hIB _, hIBv]) (hn.extend _) (by rw [hn _, hnv]) (hm.extend _)
        (by rw [hm _, hmv]) hsv (iAR.extend _) hAR (iLB _ _ hsv) (by intro inc; rw [hLB, hsvv]),
      hsvv, ← e']
    simp only [denote_add, denote_const, denote_lvl_index, denote_lvl_acc]
    by_cases h1 : acc = 0 <;> by_cases h2 : balN S Q bits sv <;> simp [h1, h2]

/-- The search result is a witness when one exists. -/
theorem find_witness {p : ℕ → Prop} [DecidablePred p] {N : ℕ} (h : ∃ s < N, p s) :
    LocalSim.optCode ((List.range N).find? fun s => decide (p s)) - 1 < N ∧
      p (LocalSim.optCode ((List.range N).find? fun s => decide (p s)) - 1) := by
  obtain ⟨s, hs, hp⟩ := h
  cases hf : (List.range N).find? fun s => decide (p s) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (decide_eq_true hp) (hf s (List.mem_range.mpr hs))
  | some x =>
    have hx := List.find?_some hf
    have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    simp only [LocalSim.optCode, Nat.add_sub_cancel]
    exact ⟨hmem, of_decide_eq_true hx⟩

end NtimeDspace.ProgTerm
