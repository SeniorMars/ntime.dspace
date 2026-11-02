import NtimeDspace.CounterTerm
import NtimeDspace.SpectralIndexing
import NtimeDspace.TensorEvaluation

/-!
# Labels and tensor signs as terms

A label `Fin Q → Fin r × Fin r` is the number whose base-`r²` digit at `node`
codes the pair at `node` (`SpectralIndexing.label`). Terms read the pair
coordinates, and compute `pairEntry`, `tensorEntry`, the counts
`normExponent` and `antisymmetricCount`, `sameLabel`, and `mismatchProduct`
with node values `node + 1`, all modulo `p`.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-! ### Coordinates of a label -/

theorem label_fst (r Q : ℕ) (positive : 0 < r) (m : ℕ) (node : Fin Q) :
    ((SpectralIndexing.label r Q positive m node).1 : ℕ) = m / (r * r) ^ (node : ℕ) % (r * r) / r := by
  simp [SpectralIndexing.label, finProdFinEquiv]

theorem label_snd (r Q : ℕ) (positive : 0 < r) (m : ℕ) (node : Fin Q) :
    ((SpectralIndexing.label r Q positive m node).2 : ℕ) = m / (r * r) ^ (node : ℕ) % (r * r) % r := by
  simp [SpectralIndexing.label, finProdFinEquiv]

theorem label_eq_iff (r Q : ℕ) (positive : 0 < r) (m m' : ℕ) (node : Fin Q) :
    SpectralIndexing.label r Q positive m node = SpectralIndexing.label r Q positive m' node ↔
      m / (r * r) ^ (node : ℕ) % (r * r) = m' / (r * r) ^ (node : ℕ) % (r * r) := by
  constructor
  · intro h
    have := congrArg finProdFinEquiv h
    simp only [SpectralIndexing.label, Equiv.apply_symm_apply, Fin.mk.injEq] at this
    exact this
  · intro h
    simp only [SpectralIndexing.label, h]

section Terms

variable (rT : Term)

/-- The base-`r²` digit of label `u` at `node`. -/
def labDigT (u node : Term) : Term := digitT (mul rT rT) u node
def labFstT (u node : Term) : Term := div (labDigT rT u node) rT
def labSndT (u node : Term) : Term := mod (labDigT rT u node) rT

end Terms

theorem denote_labDigT {rT : Term} {env : List ℕ} (hr : StableAt w rT env) (u node : Term) :
    (labDigT rT u node).denote w env =
      u.denote w env / (rT.denote w env * rT.denote w env) ^ node.denote w env %
        (rT.denote w env * rT.denote w env) := by
  unfold labDigT
  rw [digitT_denote _ _ _ _ (hr.mul hr)]
  simp

theorem StableAt.labDigT {rT u node : Term} {env : List ℕ} (hr : StableAt w rT env)
    (hu : StableAt w u env) (hn : StableAt w node env) : StableAt w (labDigT rT u node) env :=
  StableAt.digitT (hr.mul hr) hu hn

theorem denote_labFstT {rT : Term} {env : List ℕ} (hr : StableAt w rT env) {r : ℕ}
    (hrv : rT.denote w env = r) (positive : 0 < r) (u node : Term) {Q : ℕ}
    (hnode : node.denote w env < Q) :
    (labFstT rT u node).denote w env =
      ((SpectralIndexing.label r Q positive (u.denote w env) ⟨node.denote w env, hnode⟩).1 : ℕ) := by
  rw [label_fst]; simp [labFstT, denote_labDigT hr, hrv]

theorem denote_labSndT {rT : Term} {env : List ℕ} (hr : StableAt w rT env) {r : ℕ}
    (hrv : rT.denote w env = r) (positive : 0 < r) (u node : Term) {Q : ℕ}
    (hnode : node.denote w env < Q) :
    (labSndT rT u node).denote w env =
      ((SpectralIndexing.label r Q positive (u.denote w env) ⟨node.denote w env, hnode⟩).2 : ℕ) := by
  rw [label_snd]; simp [labSndT, denote_labDigT hr, hrv]

theorem StableAt.labFstT {rT u node : Term} {env : List ℕ} (hr : StableAt w rT env)
    (hu : StableAt w u env) (hn : StableAt w node env) : StableAt w (labFstT rT u node) env :=
  (StableAt.labDigT hr hu hn).div hr

theorem StableAt.labSndT {rT u node : Term} {env : List ℕ} (hr : StableAt w rT env)
    (hu : StableAt w u env) (hn : StableAt w node env) : StableAt w (labSndT rT u node) env :=
  (StableAt.labDigT hr hu hn).mod hr

/-! ### Pair and tensor entries -/

/-- The pair entry, modulo `p`, from the four coordinates. -/
def pairEntryT (pT a1 a2 b1 b2 : Term) : Term :=
  ite (eqT a1 a2) (mul (eqT b1 a1) (eqT b2 a2))
    (ite (lt a1 a2) (add (mul (eqT b1 a1) (eqT b2 a2)) (mul (eqT b1 a2) (eqT b2 a1)))
      (add (mul (eqT b1 a1) (eqT b2 a2)) (sub pT (mul (eqT b1 a2) (eqT b2 a1)))))

theorem cast_pairEntryT {P r : ℕ} [Fact P.Prime] (pT a1 a2 b1 b2 : Term) (env : List ℕ)
    (hpv : pT.denote w env = P) (h1 : a1.denote w env < r) (h2 : a2.denote w env < r)
    (h3 : b1.denote w env < r) (h4 : b2.denote w env < r) :
    ((pairEntryT pT a1 a2 b1 b2).denote w env : ZMod P) =
      TensorEvaluation.pairEntry (K := ZMod P) (⟨a1.denote w env, h1⟩, ⟨a2.denote w env, h2⟩)
        (⟨b1.denote w env, h3⟩, ⟨b2.denote w env, h4⟩) := by
  have hP : 1 ≤ P := (Fact.out : P.Prime).one_lt.le
  unfold pairEntryT TensorEvaluation.pairEntry
  simp only [denote_ite, denote_eqT, denote_mul, denote_lt, denote_add, denote_sub, hpv,
    Prod.mk.injEq, Fin.mk.injEq, Prod.swap, Fin.mk_lt_mk]
  by_cases e1 : a1.denote w env = a2.denote w env
  · simp only [e1, if_true, zero_lt_one]
    by_cases x : b1.denote w env = a2.denote w env <;> by_cases y : b2.denote w env = a2.denote w env <;>
      simp [x, y]
  · simp only [e1, if_false, Nat.lt_irrefl]
    by_cases e2 : a1.denote w env < a2.denote w env
    · simp only [e2, if_true, zero_lt_one]
      by_cases x : b1.denote w env = a1.denote w env <;>
        by_cases y : b2.denote w env = a2.denote w env <;>
        by_cases x' : b1.denote w env = a2.denote w env <;>
        by_cases y' : b2.denote w env = a1.denote w env <;>
        first | (exfalso; omega) | simp [x, y, x', y', e1, Ne.symm e1]
    · simp only [e2, if_false, Nat.lt_irrefl]
      by_cases x : b1.denote w env = a1.denote w env <;>
        by_cases y : b2.denote w env = a2.denote w env <;>
        by_cases x' : b1.denote w env = a2.denote w env <;>
        by_cases y' : b2.denote w env = a1.denote w env <;>
        first | (exfalso; omega) | simp [x, y, x', y', e1, Ne.symm e1, Nat.cast_sub hP]

theorem StableAt.pairEntryT {pT a1 a2 b1 b2 : Term} {env : List ℕ} (hp : StableAt w pT env)
    (h1 : StableAt w a1 env) (h2 : StableAt w a2 env) (h3 : StableAt w b1 env)
    (h4 : StableAt w b2 env) : StableAt w (pairEntryT pT a1 a2 b1 b2) env :=
  ((h1.eqT h2).ite ((h3.eqT h1).mul (h4.eqT h2))
    ((h1.lt h2).ite (((h3.eqT h1).mul (h4.eqT h2)).add ((h3.eqT h2).mul (h4.eqT h1)))
      (((h3.eqT h1).mul (h4.eqT h2)).add (hp.sub ((h3.eqT h2).mul (h4.eqT h1))))))

/-- The tensor entry of labels `u` and `w'`, modulo `p`. -/
def tensorEntryT (pT rT QT u w' : Term) : Term :=
  Term.prodMod pT QT fun node =>
    pairEntryT pT (labFstT rT u node) (labSndT rT u node) (labFstT rT w' node) (labSndT rT w' node)

theorem cast_tensorEntryT {P r Q : ℕ} [Fact P.Prime] (positive : 0 < r) {pT rT QT u w' : Term}
    {env : List ℕ} (hp : StableAt w pT env) (hpv : pT.denote w env = P) (hr : StableAt w rT env)
    (hrv : rT.denote w env = r) (hQv : QT.denote w env = Q) (hu : StableAt w u env)
    (hw : StableAt w w' env) :
    ((tensorEntryT pT rT QT u w').denote w env : ZMod P) =
      TensorEvaluation.tensorEntry (K := ZMod P) (SpectralIndexing.label r Q positive (u.denote w env))
        (SpectralIndexing.label r Q positive (w'.denote w env)) := by
  unfold tensorEntryT TensorEvaluation.tensorEntry
  rw [GroupedAssignmentEvaluation.scanProduct_correct, mul_one,
    denote_prodModZ pT QT _ env P (fun node => if h : node < Q then
      TensorEvaluation.pairEntry (K := ZMod P) (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, h⟩)
        (SpectralIndexing.label r Q positive (w'.denote w env) ⟨node, h⟩) else 1) hp hpv, hQv,
    ← Fin.prod_univ_eq_prod_range]
  · exact Finset.prod_congr rfl fun node _ => by rw [dif_pos node.isLt]
  intro acc node hnode
  rw [hQv] at hnode
  rw [dif_pos hnode]
  have e' : acc :: node :: env = [acc, node] ++ env := rfl
  have hr' : StableAt w rT (acc :: node :: env) := hr.extend [acc, node]
  have hrv' : rT.denote w (acc :: node :: env) = r := by rw [hr.cons₂, hrv]
  have hnv : (lvl env.length).denote w (acc :: node :: env) = node := denote_lvl_index env acc node
  have hnode' : (lvl env.length).denote w (acc :: node :: env) < Q := by rw [hnv]; exact hnode
  have hb : ∀ m (hm : m < r * r), m / r < r := fun m hm => (Nat.div_lt_iff_lt_mul positive).mpr hm
  rw [cast_pairEntryT pT _ _ _ _ _ (by rw [hp.cons₂, hpv])
    (by rw [denote_labFstT hr' hrv' positive u _ hnode']; exact Fin.isLt _)
    (by rw [denote_labSndT hr' hrv' positive u _ hnode']; exact Fin.isLt _)
    (by rw [denote_labFstT hr' hrv' positive w' _ hnode']; exact Fin.isLt _)
    (by rw [denote_labSndT hr' hrv' positive w' _ hnode']; exact Fin.isLt _)]
  congr 1
  · ext
    · simp only [denote_labFstT hr' hrv' positive u _ hnode', hu.cons₂, hnv]
    · simp only [denote_labSndT hr' hrv' positive u _ hnode', hu.cons₂, hnv]
  · ext
    · simp only [denote_labFstT hr' hrv' positive w' _ hnode', hw.cons₂, hnv]
    · simp only [denote_labSndT hr' hrv' positive w' _ hnode', hw.cons₂, hnv]

/-- Residues below `P` with equal casts are equal. -/
theorem eq_of_cast_eq {P a b : ℕ} (ha : a < P) (hb : b < P) (h : (a : ZMod P) = b) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem prodMod_lt {pT n : Term} {body : Term → Term} {env : List ℕ} {P : ℕ}
    (hpv : pT.denote w env = P) (hp : StableAt w pT env) (hP : 1 < P) :
    (Term.prodMod pT n body).denote w env < P := by
  simp only [Term.prodMod, denote_foldT, denote_const]
  cases h : n.denote w env with
  | zero => simp [foldAcc]; omega
  | succ m =>
    rw [foldAcc_succ]
    simp only [denote_mod, hp.cons₂, hpv]
    exact Nat.mod_lt _ (by omega)

theorem sumMod_lt {pT n : Term} {body : Term → Term} {env : List ℕ} {P : ℕ}
    (hpv : pT.denote w env = P) (hp : StableAt w pT env) (hP : 1 < P) :
    (Term.sumMod pT n body).denote w env < P := by
  simp only [Term.sumMod, denote_foldT, denote_const]
  cases h : n.denote w env with
  | zero => simp [foldAcc]; omega
  | succ m =>
    rw [foldAcc_succ]
    simp only [denote_mod, hp.cons₂, hpv]
    exact Nat.mod_lt _ (by omega)

theorem StableAt.tensorEntryT {pT rT QT u w' : Term} {env : List ℕ} (hp : StableAt w pT env)
    (hr : StableAt w rT env) (hQ : StableAt w QT env) (hu : StableAt w u env)
    (hw : StableAt w w' env) {P r Q : ℕ} [Fact P.Prime] (positive : 0 < r)
    (hpv : pT.denote w env = P) (hrv : rT.denote w env = r) (hQv : QT.denote w env = Q) :
    StableAt w (tensorEntryT pT rT QT u w') env := by
  intro extra
  have hP : 1 < P := (Fact.out : P.Prime).one_lt
  have hpv' : pT.denote w (extra ++ env) = P := by rw [hp extra, hpv]
  have h1 := cast_tensorEntryT positive (hp.extend extra) hpv' (hr.extend extra)
    (by rw [hr extra, hrv]) (by rw [hQ extra, hQv]) (hu.extend extra) (hw.extend extra)
  have h2 := cast_tensorEntryT positive hp hpv hr hrv hQv hu hw
  rw [hu extra, hw extra] at h1
  exact eq_of_cast_eq (prodMod_lt hpv' (hp.extend extra) hP) (prodMod_lt hpv hp hP) (h1.trans h2.symm)

/-! ### Counts, equality, and the mismatch product -/

theorem ite_iff' {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1 : ℕ) else 0) = if Q then 1 else 0 := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

def antisymT (rT QT u : Term) : Term :=
  sumT QT fun node => lt (labSndT rT u node) (labFstT rT u node)

def normExpT (rT QT u : Term) : Term :=
  sumT QT fun node => sub (const 1) (eqT (labFstT rT u node) (labSndT rT u node))

def sameLabelT (rT QT u w' : Term) : Term :=
  allT QT fun node => eqT (labDigT rT u node) (labDigT rT w' node)

/-- The mismatch product with node values `node + 1`, modulo `p`. -/
def mismatchT (pT rT QT u w' point : Term) : Term :=
  Term.prodMod pT QT fun node => ite (eqT (labFstT rT w' node) (labSndT rT u node)) (const 1)
    (mod (add (const 1) (sub pT (mod (mul (invModT pT (add node (const 1))) point) pT))) pT)

section LabelFacts

variable {rT QT u w' : Term} {env : List ℕ} {r Q : ℕ} (positive : 0 < r)

theorem denote_antisymT (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQv : QT.denote w env = Q) (hu : StableAt w u env) :
    (antisymT rT QT u).denote w env =
      TensorEvaluation.antisymmetricCount (SpectralIndexing.label r Q positive (u.denote w env)) := by
  unfold antisymT TensorEvaluation.antisymmetricCount
  rw [GroupedAssignmentEvaluation.scanSum_correct, add_zero,
    denote_sumT_lt _ _ env (fun node => if h : node < Q then
      (if (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, h⟩).2 <
        (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, h⟩).1 then 1 else 0) else 0),
    hQv, ← Fin.sum_univ_eq_sum_range]
  · exact Finset.sum_congr rfl fun node _ => by rw [dif_pos node.isLt]
  intro acc node hnode
  rw [hQv] at hnode
  have hr' : StableAt w rT (acc :: node :: env) := hr.extend [acc, node]
  have hrv' : rT.denote w (acc :: node :: env) = r := by rw [hr.cons₂, hrv]
  have hnv : (lvl env.length).denote w (acc :: node :: env) = node := denote_lvl_index env acc node
  have hnode' : (lvl env.length).denote w (acc :: node :: env) < Q := by rw [hnv]; exact hnode
  rw [denote_lt, denote_labFstT hr' hrv' positive u _ hnode',
    denote_labSndT hr' hrv' positive u _ hnode', dif_pos hnode]
  simp only [hu.cons₂, hnv, Fin.lt_def]

theorem denote_sameLabelT (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQv : QT.denote w env = Q) (hu : StableAt w u env) (hw : StableAt w w' env) :
    (sameLabelT rT QT u w').denote w env =
      if TensorEvaluation.sameLabel (SpectralIndexing.label r Q positive (u.denote w env))
        (SpectralIndexing.label r Q positive (w'.denote w env)) then 1 else 0 := by
  unfold sameLabelT
  rw [allT_denote _ _ env (fun node => u.denote w env / (r * r) ^ node % (r * r) =
      w'.denote w env / (r * r) ^ node % (r * r)) fun acc node => by
    have hr' : StableAt w rT (acc :: node :: env) := hr.extend [acc, node]
    rw [denote_eqT, denote_labDigT hr', denote_labDigT hr']
    simp only [hr.cons₂, hrv, hu.cons₂, hw.cons₂, denote_lvl_index], hQv]
  apply ite_iff'
  rw [TensorEvaluation.sameLabel_correct, funext_iff]
  constructor
  · intro h node
    exact (label_eq_iff r Q positive _ _ node).mpr (h node node.isLt)
  · intro h node hnode
    exact (label_eq_iff r Q positive _ _ ⟨node, hnode⟩).mp (h ⟨node, hnode⟩)

theorem cast_mismatchT {P : ℕ} [Fact P.Prime] (hP3 : 2 < P) {pT point : Term}
    (hp : StableAt w pT env)
    (hpv : pT.denote w env = P) (hr : StableAt w rT env) (hrv : rT.denote w env = r)
    (hQv : QT.denote w env = Q) (hu : StableAt w u env) (hw : StableAt w w' env)
    (hpt : StableAt w point env) :
    ((mismatchT pT rT QT u w' point).denote w env : ZMod P) =
      TensorEvaluation.mismatchProduct (nodeValues (P := P) Q)
        (SpectralIndexing.label r Q positive (u.denote w env))
        (SpectralIndexing.label r Q positive (w'.denote w env)) (point.denote w env : ZMod P) := by
  have hP : 1 < P := (Fact.out : P.Prime).one_lt
  have hP2 : 2 ≤ P := (Fact.out : P.Prime).two_le
  unfold mismatchT TensorEvaluation.mismatchProduct
  rw [GroupedAssignmentEvaluation.scanProduct_correct, mul_one,
    denote_prodModZ pT QT _ env P (fun node => if h : node < Q then
      (if (SpectralIndexing.label r Q positive (w'.denote w env) ⟨node, h⟩).1 ≠
          (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, h⟩).2 then
        1 - (nodeValues (P := P) Q ⟨node, h⟩)⁻¹ * (point.denote w env : ZMod P) else 1) else 1)
    hp hpv, hQv, ← Fin.prod_univ_eq_prod_range]
  · exact Finset.prod_congr rfl fun node _ => by rw [dif_pos node.isLt]
  intro acc node hnode
  rw [hQv] at hnode
  rw [dif_pos hnode]
  have e' : acc :: node :: env = [acc, node] ++ env := rfl
  have hp' : StableAt w pT (acc :: node :: env) := hp.extend [acc, node]
  have hpv' : pT.denote w (acc :: node :: env) = P := by rw [hp.cons₂, hpv]
  have hr' : StableAt w rT (acc :: node :: env) := hr.extend [acc, node]
  have hrv' : rT.denote w (acc :: node :: env) = r := by rw [hr.cons₂, hrv]
  have hnv : (lvl env.length).denote w (acc :: node :: env) = node := denote_lvl_index env acc node
  have hnode' : (lvl env.length).denote w (acc :: node :: env) < Q := by rw [hnv]; exact hnode
  rw [denote_ite, denote_eqT, denote_labFstT hr' hrv' positive w' _ hnode',
    denote_labSndT hr' hrv' positive u _ hnode']
  simp only [hu.cons₂, hw.cons₂, hnv]
  by_cases heq : ((SpectralIndexing.label r Q positive (w'.denote w env) ⟨node, hnode⟩).1 : ℕ) =
      (SpectralIndexing.label r Q positive (u.denote w env) ⟨node, hnode⟩).2
  · rw [if_pos heq, if_pos Nat.one_pos, if_neg (fun h => h (Fin.ext heq))]
    simp
  · rw [if_neg heq, if_neg (lt_irrefl 0), if_pos (fun h => heq (congrArg Fin.val h))]
    have hinv := invModT_denote pT (add (lvl env.length) (const 1)) (acc :: node :: env) P
      hP3 hp' hpv' ((stableAt_lvl (by simp)).add (stableAt_const _ _))
    simp only [denote_mod, denote_add, denote_const, denote_sub, denote_mul, hpv']
    rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_one, Nat.cast_sub (Nat.mod_lt _ (by omega)).le,
      ZMod.natCast_self, ZMod.natCast_mod, Nat.cast_mul, hinv, hpt.cons₂]
    simp only [denote_add, denote_const, hnv, nodeValues]
    push_cast
    ring

end LabelFacts

end NtimeDspace.ProgTerm
