import NtimeDspace.FormulaCounter

/-!
# Weighted constraint systems

A weighted constraint system on `n` Boolean variables is a list of constraints,
each with an ordered scope and a natural-number weight on the assignments of its
scope. Its weighted count is `∑_x ∏_e weight_e(x|scope_e)`. Bounded-occurrence
CNFs (with 0/1 weights) and Complexitylib's explicit tensor networks (with
table weights) are both instances.

Each constraint enters the counting construction only through the multilinear
extension of its weight, a polynomial in the incidence variables of that
constraint. This module gives the extension, its values at Boolean points and
its degree bound, and recovers the weighted count modulo a prime from the
generic `AlgebraicCounter.scalarExpression`.
-/

namespace NtimeDspace.WeightedSystem

open scoped BigOperators

/-- A constraint: an ordered scope and a weight on the assignments of the scope. -/
structure Constraint (n : ℕ) where
  scope : List (Fin n)
  weight : (Fin scope.length → Bool) → ℕ

/-- A weighted constraint system. -/
structure System (n : ℕ) where
  constraints : List (Constraint n)

variable {n : ℕ} {K : Type*} [CommRing K]

/-- The values an assignment puts on the scope of a constraint. -/
def Constraint.restrict (c : Constraint n) (x : Fin n → Bool) : Fin c.scope.length → Bool :=
  fun i => x c.scope[i]

/-- The weighted count. -/
noncomputable def System.count (S : System n) : ℕ :=
  ∑ x : Fin n → Bool, ∏ e : Fin S.constraints.length,
    (S.constraints[e]).weight ((S.constraints[e]).restrict x)

/-- Incidences: a constraint and a position in its scope. -/
abbrev Incidence (S : System n) :=
  (e : Fin S.constraints.length) × Fin (S.constraints[e]).scope.length

/-- The variable at an incidence. -/
def incidenceVariable (S : System n) (inc : Incidence S) : Fin n :=
  (S.constraints[inc.1]).scope[inc.2]

/-- The multilinear selector of a bit. -/
noncomputable def selector {ι : Type*} (a : Bool) (X : MvPolynomial ι K) : MvPolynomial ι K :=
  if a then X else 1 - X

/-- The multilinear extension of a constraint's weight, in its incidence variables. -/
noncomputable def constraintPolynomial (S : System n) (e : Fin S.constraints.length) :
    MvPolynomial (Incidence S) K :=
  ∑ a : Fin (S.constraints[e]).scope.length → Bool,
    MvPolynomial.C ((S.constraints[e]).weight a : K) *
      ∏ i, selector (a i) (MvPolynomial.X ⟨e, i⟩)

/-- The factor polynomial: the product of the constraint extensions. -/
noncomputable def factorPolynomial (S : System n) : MvPolynomial (Incidence S) K :=
  ∏ e : Fin S.constraints.length, constraintPolynomial S e

/-- Deformation coefficients, one linear form per incidence. -/
abbrev Coefficients (S : System n) (K : Type*) [CommRing K] :=
  (e : Fin S.constraints.length) → Fin (S.constraints[e]).scope.length → Fin n → Polynomial K

def coefficients (S : System n) (L : Coefficients S K) : Incidence S → Fin n → Polynomial K :=
  fun inc v => L inc.1 inc.2 v

/-- The incidence form is the incidence's variable at parameter zero. -/
def OriginCondition (S : System n) (L : Coefficients S K) : Prop :=
  ∀ e i v, (L e i v).eval 0 = if v = (S.constraints[e]).scope[i] then 1 else 0

/-- The number of incidences. -/
def incidenceCount (S : System n) : ℕ :=
  ∑ e : Fin S.constraints.length, (S.constraints[e]).scope.length

/-- The deformed linear form of an incidence at a Boolean assignment. -/
noncomputable def incidenceForm (S : System n) (L : Coefficients S K)
    (e : Fin S.constraints.length) (i : Fin (S.constraints[e]).scope.length)
    (assignment : Fin n → Bool) : Polynomial K :=
  ∑ v, L e i v * Polynomial.C (CountingPolynomial.boolValue (assignment v))

theorem linearValue_eq_incidenceForm (S : System n) (L : Coefficients S K)
    (support : Finset (Fin n)) (inc : Incidence S) :
    DeformationTaylor.linearValue Finset.univ (coefficients S L) support inc =
      incidenceForm S L inc.1 inc.2 (FormulaCounter.assignmentOfSupport support) := by
  simp only [DeformationTaylor.linearValue, incidenceForm, coefficients]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ support <;>
    simp [FormulaCounter.assignmentOfSupport, CountingPolynomial.boolValue, hv]

/-- Evaluating after substituting polynomials is substituting their values. -/
theorem eval_eval₂_C {σ : Type*} (P : MvPolynomial σ K) (f : σ → Polynomial K) (x : K) :
    (P.eval₂ Polynomial.C f).eval x = P.eval₂ (RingHom.id K) (fun i => (f i).eval x) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The scalar value of a constraint's extension at incidence values. -/
theorem constraintPolynomial_eval₂ (S : System n) (e : Fin S.constraints.length)
    (value : Incidence S → K) :
    (constraintPolynomial S e).eval₂ (RingHom.id K) value =
      ∑ a : Fin (S.constraints[e]).scope.length → Bool, ((S.constraints[e]).weight a : K) *
        ∏ i, (if a i then value ⟨e, i⟩ else 1 - value ⟨e, i⟩) := by
  simp only [constraintPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_prod, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  cases a i <;> simp [selector]

/-! ### Values at Boolean points -/

theorem selector_eval_bool {ι : Type*} (a b : Bool) (point : ι → K) (i : ι)
    (hi : point i = CountingPolynomial.boolValue b) :
    MvPolynomial.eval point (selector a (MvPolynomial.X i)) = if a = b then 1 else 0 := by
  cases a <;> cases b <;> simp [selector, hi, CountingPolynomial.boolValue]

/-- At a Boolean point, the extension is the weight. -/
theorem constraintPolynomial_eval_bool (S : System n) (e : Fin S.constraints.length)
    (point : Incidence S → K) (b : Fin (S.constraints[e]).scope.length → Bool)
    (hpoint : ∀ i, point ⟨e, i⟩ = CountingPolynomial.boolValue (b i)) :
    MvPolynomial.eval point (constraintPolynomial (K := K) S e) =
      ((S.constraints[e]).weight b : K) := by
  classical
  simp only [constraintPolynomial, map_sum, map_mul, MvPolynomial.eval_C, map_prod]
  rw [Finset.sum_eq_single b]
  · rw [Finset.prod_eq_one (fun i _ => by rw [selector_eval_bool _ _ _ _ (hpoint i)]; simp),
      mul_one]
  · intro a _ hab
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := Function.ne_iff.mp hab
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [selector_eval_bool _ _ _ _ (hpoint i)]; simp [hi]), mul_zero]
  · simp

/-! ### Degree -/

theorem selector_degree {ι : Type*} (a : Bool) (i : ι) :
    (selector (K := K) a (MvPolynomial.X i)).totalDegree ≤ 1 := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · have : selector (K := K) a (MvPolynomial.X i) = 0 := Subsingleton.elim _ _
    rw [this, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  cases a
  · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  · simp [selector]

theorem constraintPolynomial_degree (S : System n) (e : Fin S.constraints.length) :
    (constraintPolynomial (K := K) S e).totalDegree ≤ (S.constraints[e]).scope.length := by
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun a _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.zero_add]
  refine (FormulaCounter.totalDegree_product _ _).trans ?_
  calc _ ≤ ∑ _i : Fin (S.constraints[e]).scope.length, 1 :=
        Finset.sum_le_sum fun i _ => selector_degree _ _
    _ = _ := by simp

theorem factorPolynomial_degree (S : System n) :
    (factorPolynomial (K := K) S).totalDegree ≤ incidenceCount S :=
  (FormulaCounter.totalDegree_product _ _).trans
    (Finset.sum_le_sum fun e _ => constraintPolynomial_degree S e)

/-! ### The counting polynomial at the origin -/

theorem linearValue_eval_zero (S : System n) (L : Coefficients S K)
    (origin : OriginCondition S L) (support : Finset (Fin n)) (inc : Incidence S) :
    (DeformationTaylor.linearValue Finset.univ (coefficients S L) support inc).eval 0 =
      CountingPolynomial.boolValue (decide (incidenceVariable S inc ∈ support)) := by
  classical
  simp only [DeformationTaylor.linearValue, NtimeDspace.PolynomialFacts.eval_finset_sum]
  rw [Finset.sum_eq_single (incidenceVariable S inc)]
  · have one : (L inc.1 inc.2 (incidenceVariable S inc)).eval 0 = 1 := by
      simpa [incidenceVariable] using origin inc.1 inc.2 (incidenceVariable S inc)
    by_cases h : incidenceVariable S inc ∈ support
    · rw [if_pos h, decide_eq_true h]
      simpa [coefficients, CountingPolynomial.boolValue] using one
    · rw [if_neg h, decide_eq_false h]
      simp [CountingPolynomial.boolValue]
  · intro v _ hv
    have zero := origin inc.1 inc.2 v
    rw [if_neg (by simpa [incidenceVariable] using hv)] at zero
    by_cases h : v ∈ support
    · rw [if_pos h]
      simpa [coefficients] using zero
    · rw [if_neg h]
      simp
  · simp

/-- **The weighted count at the origin.** -/
theorem countingPolynomial_origin (S : System n) (L : Coefficients S K)
    (origin : OriginCondition S L) :
    (DeformationTaylor.countingPolynomial Finset.univ (factorPolynomial S)
      (coefficients S L)).eval 0 = (S.count : K) := by
  classical
  simp only [DeformationTaylor.countingPolynomial, Finset.powerset_univ,
    NtimeDspace.PolynomialFacts.eval_finset_sum]
  have term (support : Finset (Fin n)) :
      ((factorPolynomial S).eval₂ Polynomial.C
        (DeformationTaylor.linearValue Finset.univ (coefficients S L) support)).eval 0 =
      ∏ e : Fin S.constraints.length, ((S.constraints[e]).weight
        ((S.constraints[e]).restrict (FormulaCounter.assignmentOfSupport support)) : K) := by
    rw [show ((factorPolynomial S).eval₂ Polynomial.C
        (DeformationTaylor.linearValue Finset.univ (coefficients S L) support)).eval 0 =
        Polynomial.evalRingHom 0 ((factorPolynomial S).eval₂ Polynomial.C
          (DeformationTaylor.linearValue Finset.univ (coefficients S L) support)) from rfl,
      MvPolynomial.eval₂_comp_left]
    have hC : (Polynomial.evalRingHom (0 : K)).comp Polynomial.C = RingHom.id K := by
      ext; simp
    rw [hC, ← MvPolynomial.coe_eval₂Hom, show MvPolynomial.eval₂Hom (RingHom.id K) _ =
      MvPolynomial.eval _ from rfl, factorPolynomial, map_prod]
    refine Finset.prod_congr rfl fun e _ => constraintPolynomial_eval_bool S e _ _ fun i => ?_
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom]
    rw [linearValue_eval_zero S L origin]
    simp only [Constraint.restrict, FormulaCounter.assignmentOfSupport, incidenceVariable]
    rfl
  simp only [term]
  rw [System.count, Nat.cast_sum]
  simp only [Nat.cast_prod]
  exact (FormulaCounter.supportAssignmentEquiv n).sum_comp
    (fun x => ∏ e : Fin S.constraints.length,
      ((S.constraints[e]).weight ((S.constraints[e]).restrict x) : K))

variable {p : ℕ} [Fact p.Prime]

/-- The scalar recovery expression for a weighted system. -/
noncomputable def scalarExpression (S : System n) (L : Coefficients S (ZMod p))
    (nodes : Finset (ZMod p)) (order : ℕ) : ZMod p :=
  AlgebraicCounter.scalarExpression Finset.univ (factorPolynomial S) (coefficients S L) nodes order

/-- **Scalar recovery of the weighted count**, for any deformation with the
origin condition and the degree and capacity bounds. -/
theorem scalarExpression_correct (S : System n) (L : Coefficients S (ZMod p))
    (origin : OriginCondition S L) (nodes : Finset (ZMod p)) (order bound : ℕ)
    (positive : 0 < order) (below_prime : order < p)
    (nonzero_nodes : ∀ node ∈ nodes, node ≠ 0)
    (degrees : ∀ e i v, (L e i v).natDegree ≤ bound)
    (interpolation_capacity : incidenceCount S * bound < nodes.card * order)
    (no_alias : incidenceCount S * bound ≤ p - 2) :
    scalarExpression S L nodes order = (S.count : ZMod p) := by
  unfold scalarExpression
  rw [AlgebraicCounter.scalarExpression_correct Finset.univ (factorPolynomial S)
    (coefficients S L) nodes order bound positive below_prime nonzero_nodes
    (fun inc v _ => degrees inc.1 inc.2 v)
    ((Nat.mul_le_mul_right bound (factorPolynomial_degree S)).trans_lt interpolation_capacity)
    ((Nat.mul_le_mul_right bound (factorPolynomial_degree S)).trans no_alias)]
  exact countingPolynomial_origin S L origin

end NtimeDspace.WeightedSystem
