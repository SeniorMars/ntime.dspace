import NtimeDspace.DeformTerm
import NtimeDspace.WIncidenceEvaluation

/-!
# Scans over incidences as terms

An incidence of a weighted system is a constraint `e` and a scope position `i`.
`incSumModT` sums a body over all incidences modulo `p` (constraints below `m`,
positions below the arity term), and `incSumT` sums exactly. Both are proved
equal to the sum over `WeightedSystem.Incidence`, given an arity term meeting
its contract.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- Sums over incidences as nested range sums. -/
theorem sum_incidence_eq {n : ℕ} {M : Type*} [AddCommMonoid M] (formula : WeightedSystem.System n)
    (AR : ℕ → ℕ)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    (F : ℕ → ℕ → M) :
    ∑ e ∈ Finset.range formula.constraints.length, ∑ i ∈ Finset.range (AR e), F e i =
      ∑ inc : WeightedSystem.Incidence formula, F inc.1 inc.2 := by
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hAR e e.isLt, ← Fin.sum_univ_eq_sum_range]; rfl

section Def

variable (pT mT : Term) (arity : Term → Term) (body : Term → Term → Term)

/-- The sum of `body e i` over incidences, modulo `p`. -/
def incSumModT : Term := Term.sumMod pT mT fun e => Term.sumMod pT (arity e) fun i => body e i

/-- The exact sum of `body e i` over incidences. -/
def incSumT : Term := sumT mT fun e => sumT (arity e) fun i => body e i

end Def

theorem cast_incSumModT {n P : ℕ} (formula : WeightedSystem.System n) {pT mT : Term}
    {arity : Term → Term} {body : Term → Term → Term} {env : List ℕ}
    (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hmv : mT.denote w env = formula.constraints.length)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    (F : ℕ → ℕ → ZMod P)
    (hbody : ∀ (pre : List ℕ) (e i : Term), StableAt w e (pre ++ env) → StableAt w i (pre ++ env) →
      e.denote w (pre ++ env) < formula.constraints.length →
      i.denote w (pre ++ env) < AR (e.denote w (pre ++ env)) →
      ((body e i).denote w (pre ++ env) : ZMod P) =
        F (e.denote w (pre ++ env)) (i.denote w (pre ++ env))) :
    ((incSumModT pT mT arity body).denote w env : ZMod P) =
      ∑ inc : WeightedSystem.Incidence formula, F inc.1 inc.2 := by
  rw [← sum_incidence_eq formula AR hAR F]
  unfold incSumModT
  rw [denote_sumModZ pT mT _ env P _ hp hpv, hmv]
  intro acc e he
  rw [hmv] at he
  have hes : StableAt w (lvl env.length) ([acc, e] ++ env) := stableAt_lvl (by simp)
  have hev : (lvl env.length).denote w (acc :: e :: env) = e := denote_lvl_index env acc e
  obtain ⟨har, hars⟩ := iAR [acc, e] _ hes
  simp only [List.cons_append, List.nil_append] at har hars
  rw [denote_sumModZ pT _ _ (acc :: e :: env) P _ (hp.extend [acc, e]) (by rw [hp.cons₂, hpv]),
    har, hev]
  intro acc' i hi
  rw [har, hev] at hi
  have hes' : StableAt w (lvl env.length) ([acc', i, acc, e] ++ env) :=
    hes.extend [acc', i]
  have his : StableAt w (lvl (env.length + 2)) ([acc', i, acc, e] ++ env) :=
    stableAt_lvl (by simp)
  have hev' : (lvl env.length).denote w (acc' :: i :: acc :: e :: env) = e := by
    rw [denote_lvl]; simp only [List.length_cons]
    rw [show env.length + 1 + 1 + 1 + 1 - env.length - 1 = 3 by omega]; rfl
  have hiv : (lvl (env.length + 2)).denote w (acc' :: i :: acc :: e :: env) = i := by
    rw [denote_lvl]; simp only [List.length_cons]
    rw [show env.length + 1 + 1 + 1 + 1 - (env.length + 2) - 1 = 1 by omega]; rfl
  have hb := hbody [acc', i, acc, e] (lvl env.length) (lvl (env.length + 2)) hes' his
    (by simpa [hev'] using he) (by simpa [hev', hiv] using hi)
  simp only [List.cons_append, List.nil_append, hev', hiv] at hb
  have hlen : (acc :: e :: env).length = env.length + 2 := by simp
  rw [hlen]
  exact hb

end NtimeDspace.ProgTerm
