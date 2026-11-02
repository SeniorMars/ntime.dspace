import NtimeDspace.TaylorLoopEq
import NtimeDspace.RecoverTerm
import NtimeDspace.WCompressedRecoveryLoop

/-!
# The counter term: recovery over the compressed Taylor loop

`counterT` runs the recovery term with the compressed Taylor loop as its data,
one node and one nonzero residue at a time. `counterT_eq`: it computes
`WCompressedRecoveryLoop.evaluate`, the arithmetic counting loop whose value is
the weighted count modulo `p` (`WConcreteCountingLoop.countModP_correct`), for
node-dependent accessor terms meeting their contracts.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

section Def

variable (p Q order B Cap Lb M K nT groups rows width D m : Term) (gOf cGroup : Term → Term → Term)
  (arity : Term → Term) (rowNum : Term → Term → Term → Term)
  (posAll negAll : Term → Term → Term → Term → Term) (weight : Term → Term → Term)
  (localC : Term → Term → Term → Term → Term) (measCoef : Term → Term → Term → Term → Term → Term)
  (evalC : Term → Term → Term → Term → Term)

/-- **The counter term.** -/
def counterT : Term :=
  recoverT p Q order fun nd zt =>
    taylorLoopT p B Cap Lb M K nT groups rows width D m (gOf nd) (cGroup nd) arity (rowNum nd)
      (posAll nd) (negAll nd) weight (localC nd) (measCoef nd) evalC (add nd (const 1)) zt

end Def

set_option maxHeartbeats 1000000 in
/-- **The counter term computes the arithmetic counting loop.** -/
theorem counterT_eq {n r R W b P k QN : ℕ} [Fact P.Prime] {Row : Type*}
    (formula : WeightedSystem.System n) (variableGroup : Fin QN → Fin n → Fin r)
    (clauseGroup : Fin QN → Fin formula.constraints.length → Fin r)
    (rowAt : Fin QN → Fin R → Row) (rowNumber : Fin QN → (Σ _ : Fin r, Row) → Fin W)
    (measurement : ∀ node g, Row → GroupedDeformation.LocalVariable (variableGroup node) g → ℤ)
    (localCoefficient : Fin QN → WeightedSystem.Incidence formula → Fin n → ZMod P)
    (measurementCoefficient : Fin QN → WeightedSystem.Incidence formula → Fin r → Row → ZMod P)
    (evaluateCoefficient : WeightedSystem.Incidence formula → Fin n → ZMod P → ZMod P)
    (p Q order B Cap Lb M K nT groups rows width D m : Term) (gOf cGroup : Term → Term → Term)
    (arity : Term → Term) (rowNum : Term → Term → Term → Term)
    (posAll negAll : Term → Term → Term → Term → Term) (weight : Term → Term → Term)
    (localC : Term → Term → Term → Term → Term)
    (measCoef : Term → Term → Term → Term → Term → Term)
    (evalC : Term → Term → Term → Term → Term) (env : List ℕ)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hQ : StableAt w Q env) (hQv : Q.denote w env = QN) (hQP : QN < P)
    (ho : StableAt w order env) (hov : order.denote w env = Parameters.q n k + 1)
    (hJP : Parameters.q n k + 1 ≤ P)
    (hn : StableAt w nT env) (hnv : nT.denote w env = n)
    (hgroups : StableAt w groups env) (hgroupsv : groups.denote w env = r)
    (hrows : StableAt w rows env) (hrowsv : rows.denote w env = R)
    (hwidth : StableAt w width env) (hwidthv : width.denote w env = W)
    (hD : StableAt w D env) (hDv : D.denote w env = b)
    (hm : StableAt w m env) (hmv : m.denote w env = formula.constraints.length)
    (pp : ParserParams w env n (Parameters.q n k) (SupportBudget.limit n k) B Cap Lb M K)
    (G CG : ℕ → ℕ → ℕ) (AR : ℕ → ℕ) (RN : ℕ → ℕ → ℕ → ℕ) (Cp Cn : ℕ → ℕ → ℕ → ℕ → ℕ)
    (Wt : ℕ → ℕ → ZMod P) (LC : ℕ → ℕ → ℕ → ℕ → ZMod P) (MC : ℕ → ℕ → ℕ → ℕ → ℕ → ZMod P)
    (EC : ℕ → ℕ → ℕ → ℕ → ZMod P)
    (iG : ∀ pre nd, StableAt w nd (pre ++ env) →
      ImplN w (pre ++ env) (gOf nd) (G (nd.denote w (pre ++ env))))
    (iCG : ∀ pre nd, StableAt w nd (pre ++ env) →
      ImplN w (pre ++ env) (cGroup nd) (CG (nd.denote w (pre ++ env))))
    (iAR : ImplN w env arity AR)
    (iRN : ∀ pre nd, StableAt w nd (pre ++ env) →
      ImplN2 w (pre ++ env) (rowNum nd) (RN (nd.denote w (pre ++ env))))
    (iCp : ∀ pre nd, StableAt w nd (pre ++ env) →
      ImplN3 w (pre ++ env) (posAll nd) (Cp (nd.denote w (pre ++ env))))
    (iCn : ∀ pre nd, StableAt w nd (pre ++ env) →
      ImplN3 w (pre ++ env) (negAll nd) (Cn (nd.denote w (pre ++ env))))
    (iWt : ImplZ2 w env P weight Wt)
    (iLC : ∀ pre nd, StableAt w nd (pre ++ env) →
      ImplZ3 w (pre ++ env) P (localC nd) (LC (nd.denote w (pre ++ env))))
    (iMC : ∀ pre nd, StableAt w nd (pre ++ env) →
      ImplZ4 w (pre ++ env) P (measCoef nd) (MC (nd.denote w (pre ++ env))))
    (iEC : ImplZ4 w env P evalC EC)
    (hG : ∀ ν (hν : ν < QN) v (h : v < n), G ν v = (variableGroup ⟨ν, hν⟩ ⟨v, h⟩).val)
    (hCG : ∀ ν (hν : ν < QN) e (h : e < formula.constraints.length),
      CG ν e = (clauseGroup ⟨ν, hν⟩ ⟨e, h⟩).val)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    (hRN : ∀ ν (hν : ν < QN) g ρ (hg : g < r) (hρ : ρ < R),
      RN ν g ρ = (rowNumber ⟨ν, hν⟩ ⟨⟨g, hg⟩, rowAt ⟨ν, hν⟩ ⟨ρ, hρ⟩⟩).val)
    (hcoef : ∀ ν (hν : ν < QN) g ρ (hg : g < r) (hρ : ρ < R) v,
      measurement ⟨ν, hν⟩ ⟨g, hg⟩ (rowAt ⟨ν, hν⟩ ⟨ρ, hρ⟩) v =
        (Cp ν g ρ v.val.val : ℤ) - Cn ν g ρ v.val.val)
    (hWt : ∀ e (h : e < formula.constraints.length) A,
      Wt e A = ((formula.constraints[e]).weight (AssignmentLoop.assignment _ A) : ZMod P))
    (hLC : ∀ ν (hν : ν < QN) e i v (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hv : v < n),
      LC ν e i v = localCoefficient ⟨ν, hν⟩ ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨v, hv⟩)
    (hMC : ∀ ν (hν : ν < QN) e i g ρ (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hg : g < r) (hρ : ρ < R),
      MC ν e i g ρ = measurementCoefficient ⟨ν, hν⟩ ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨g, hg⟩
        (rowAt ⟨ν, hν⟩ ⟨ρ, hρ⟩))
    (hEC : ∀ e i v x (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hv : v < n),
      EC e i v x = evaluateCoefficient ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨v, hv⟩ (x : ZMod P))
    (hP2 : 2 < P) :
    ((counterT p Q order B Cap Lb M K nT groups rows width D m gOf cGroup arity rowNum posAll
        negAll weight localC measCoef evalC).denote w env : ZMod P) =
      WCompressedRecoveryLoop.evaluate formula variableGroup clauseGroup rowAt rowNumber b k
        (nodeValues (P := P) QN) measurement localCoefficient measurementCoefficient
        evaluateCoefficient := by
  unfold counterT WCompressedRecoveryLoop.evaluate
  refine recoverT_denote p Q order _ env hP2 QN (Parameters.q n k + 1) hp hpv hQ hQv hQP ho hov
    (by omega) hJP _ ?_
  intro pre nd zt hnd hzt hν
  set ν := nd.denote w (pre ++ env)
  have ext : ∀ {t : Term} {x : ℕ}, StableAt w t env → t.denote w env = x →
      StableAt w t (pre ++ env) ∧ t.denote w (pre ++ env) = x :=
    fun h hx => ⟨h.extend pre, by rw [h pre, hx]⟩
  have hnode : StableAt w (add nd (const 1)) (pre ++ env) := hnd.add (stableAt_const _ _)
  have hnodev : ((add nd (const 1)).denote w (pre ++ env) : ZMod P) =
      nodeValues (P := P) QN ⟨ν, hν⟩ := by
    simp [nodeValues, ν]
  rw [← hnodev]
  exact taylorLoopT_eq formula (variableGroup ⟨ν, hν⟩) (clauseGroup ⟨ν, hν⟩) (rowAt ⟨ν, hν⟩)
    (rowNumber ⟨ν, hν⟩) (measurement ⟨ν, hν⟩) (localCoefficient ⟨ν, hν⟩)
    (measurementCoefficient ⟨ν, hν⟩) evaluateCoefficient p B Cap Lb M K nT groups rows width D m
    (gOf nd) (cGroup nd) arity (rowNum nd) (posAll nd) (negAll nd) weight (localC nd)
    (measCoef nd) evalC (add nd (const 1)) zt (pre ++ env)
    (ext hp hpv).1 (ext hp hpv).2 (ext hn hnv).1 (ext hn hnv).2 (ext hgroups hgroupsv).1
    (ext hgroups hgroupsv).2 (ext hrows hrowsv).1 (ext hrows hrowsv).2 (ext hwidth hwidthv).1
    (ext hwidth hwidthv).2 (ext hD hDv).1 (ext hD hDv).2 (ext hm hmv).1 (ext hm hmv).2
    (pp.extend pre) (G ν) (CG ν) AR (RN ν) (Cp ν) (Cn ν) Wt (LC ν) (MC ν) EC
    (iG pre nd hnd) (iCG pre nd hnd) (iAR.extend pre) (iRN pre nd hnd) (iCp pre nd hnd)
    (iCn pre nd hnd) (iWt.extend pre) (iLC pre nd hnd) (iMC pre nd hnd) (iEC.extend pre)
    (hG ν hν) (hCG ν hν) hAR (hRN ν hν) (hcoef ν hν) hWt (hLC ν hν) (hMC ν hν) hEC
    hnode hzt hP2

end NtimeDspace.ProgTerm
