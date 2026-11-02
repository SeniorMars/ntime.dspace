import NtimeDspace.InnerLoopTerm

/-!
# The grouped inner loop: specification side

The specification's `WGroupedInnerLoop.sumGroup` uses `Fin`-indexed scans,
local variables and Boolean assignments. Here its ingredients are rewritten as
the range sums and products computed by `sumGroupT`.
-/

namespace NtimeDspace.InnerLoopSpec

open WGroupedAssignmentEvaluation

variable {n : ℕ} {K : Type*} [CommRing K]

/-- A constraint value as a sum over numbers `A < 2^arity`. -/
theorem clauseValue_range (formula : WeightedSystem.System n)
    (value : WeightedSystem.Incidence formula → K) (e : Fin formula.constraints.length) :
    clauseValue formula value e =
      ∑ A ∈ Finset.range (2 ^ (formula.constraints[e]).scope.length),
        ((formula.constraints[e]).weight (AssignmentLoop.assignment _ A) : K) *
          ∏ i ∈ Finset.range (formula.constraints[e]).scope.length,
            (if A.testBit i then
              (if h : i < (formula.constraints[e]).scope.length then value ⟨e, ⟨i, h⟩⟩ else 0)
            else 1 - (if h : i < (formula.constraints[e]).scope.length then value ⟨e, ⟨i, h⟩⟩
              else 0)) := by
  rw [clauseValue]
  have := AssignmentLoop.sumAssignments_correct (formula.constraints[e]).scope.length
    (fun a => ((formula.constraints[e]).weight a : K) *
      ∏ i, (if a i then value ⟨e, i⟩ else 1 - value ⟨e, i⟩)) 0
  rw [add_zero] at this
  rw [← this, AssignmentLoop.sumAssignments, sumLoop_correct, add_zero]
  refine Finset.sum_congr rfl fun A _ => ?_
  congr 1
  rw [← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [AssignmentLoop.assignment]
  rfl

variable {groups : ℕ}

/-- A local sum as a range sum with an indicator. -/
theorem localSum_range {R : Type*} [AddCommMonoid R] (groupOf : Fin n → Fin groups)
    (group : Fin groups) (term : ℕ → R) :
    localSum groupOf group (fun v => term v.val.val) =
      ∑ v ∈ Finset.range n, (if h : v < n then (if groupOf ⟨v, h⟩ = group then term v else 0)
        else 0) := by
  rw [localSum, scanSum_correct, add_zero, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dif_pos v.isLt]
  split_ifs <;> rfl

/-- The assignment bit of a local variable is a bit of the mask at its rank. -/
theorem assignment_bit (groupOf : Fin n → Fin groups) (group : Fin groups) (mask : ℕ)
    (v : GroupedDeformation.LocalVariable groupOf group) :
    LocalAssignmentLoop.assignment groupOf group mask v =
      mask.testBit (LocalAssignmentLoop.countBefore groupOf group v.val.val) := rfl

/-- **The support test as a property of numbers.** -/
theorem supportTest_iff (groupOf : Fin n → Fin groups) (group : Fin groups)
    (supportBit : Fin n → Bool) (mask : ℕ) :
    WGroupedInnerLoop.supportTest groupOf group supportBit mask = true ↔
      ∀ v (h : v < n), (groupOf ⟨v, h⟩).val = group.val → (supportBit ⟨v, h⟩).toNat = 1 →
        mask.testBit (LocalAssignmentLoop.countBefore groupOf group v) = true := by
  rw [WGroupedInnerLoop.supportTest, WGroupedInnerLoop.scanAll_correct]
  constructor
  · intro hall v h hg hs
    have := hall ⟨v, h⟩
    rw [dif_pos (Fin.ext hg)] at this
    cases hb : supportBit ⟨v, h⟩
    · rw [hb] at hs; simp at hs
    · rw [hb] at this; simpa [assignment_bit] using this
  · intro hall v
    split_ifs with hg
    · cases hb : supportBit v
      · simp
      · have := hall v.val v.isLt (by rw [hg]) (by simp [hb])
        simpa [assignment_bit] using this
    · rfl

variable {rows : ℕ} {Row : Type*}

/-- **The measurement test as a natural-number equation**, for coefficients
`Cp - Cn` and targets `Td - D`. -/
theorem measurementTest_iff (groupOf : Fin n → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row)
    (coefficient : Row → GroupedDeformation.LocalVariable groupOf group → ℤ)
    (target : Row → ℤ) (mask : ℕ) (G : ℕ → ℕ) (hG : ∀ v (h : v < n), G v = (groupOf ⟨v, h⟩).val)
    (Cp Cn : ℕ → ℕ → ℕ) (Td : ℕ → ℕ) (D : ℕ)
    (hcoef : ∀ (ρ : Fin rows) v, coefficient (rowAt ρ) v = (Cp ρ v.val.val : ℤ) - Cn ρ v.val.val)
    (htarget : ∀ ρ : Fin rows, target (rowAt ρ) = (Td ρ : ℤ) - D) :
    WGroupedInnerLoop.measurementTest groupOf group rowAt coefficient target mask = true ↔
      ∀ ρ < rows,
        ∑ v ∈ Finset.range n, (if G v = group.val then 1 else 0) * (Cp ρ v *
            (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat) + D =
          Td ρ + ∑ v ∈ Finset.range n, (if G v = group.val then 1 else 0) * (Cn ρ v *
            (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat) := by
  rw [WGroupedInnerLoop.measurementTest, WGroupedInnerLoop.scanAll_correct]
  have key (ρ : Fin rows) :
      measurement groupOf group (coefficient (rowAt ρ)) mask =
        (∑ v ∈ Finset.range n, (if G v = group.val then 1 else 0) * (Cp ρ v *
            (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat) : ℕ) -
          (∑ v ∈ Finset.range n, (if G v = group.val then 1 else 0) * (Cn ρ v *
            (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat) : ℕ) := by
    rw [measurement]
    simp only [hcoef ρ, assignment_bit]
    rw [localSum_range groupOf group (fun v => ((Cp ρ v : ℤ) - Cn ρ v) *
      CountingPolynomial.boolValue (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)))]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' : v < n := Finset.mem_range.mp hv
    rw [dif_pos hv', hG v hv']
    by_cases hg : groupOf ⟨v, hv'⟩ = group
    · rw [if_pos hg, if_pos (by rw [hg])]
      cases mask.testBit (LocalAssignmentLoop.countBefore groupOf group v) <;>
        simp [CountingPolynomial.boolValue]
    · rw [if_neg hg, if_neg (fun h => hg (Fin.ext h))]
      simp
  constructor
  · intro hall ρ hρ
    have := hall ⟨ρ, hρ⟩
    rw [decide_eq_true_eq, key, htarget] at this
    simp only [Fin.val_mk] at this
    omega
  · intro hall ρ
    rw [decide_eq_true_eq, key, htarget]
    have := hall ρ.val ρ.isLt
    omega

/-- The linear value: an indicator range sum plus the measurement part. -/
theorem linearValue_range (groupOf : Fin n → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row) (localCoefficient : Fin n → K)
    (measurementCoefficient : Fin groups → Row → K) (target : Fin groups → Row → ℤ) (mask : ℕ)
    (G : ℕ → ℕ) (hG : ∀ v (h : v < n), G v = (groupOf ⟨v, h⟩).val) :
    WGroupedInnerLoop.linearValue groupOf group rowAt localCoefficient measurementCoefficient
        target mask =
      (∑ v ∈ Finset.range n, (if G v = group.val then (1 : K) else 0) *
        ((if h : v < n then localCoefficient ⟨v, h⟩ else 0) *
          ((mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat : K))) +
      scanSum (fun g => scanSum (fun row =>
        measurementCoefficient g (rowAt row) * (target g (rowAt row) : K)) 0) 0 := by
  rw [WGroupedInnerLoop.linearValue]
  congr 1
  have hfun : (fun v : GroupedDeformation.LocalVariable groupOf group =>
      localCoefficient v.val * CountingPolynomial.boolValue
        (LocalAssignmentLoop.assignment groupOf group mask v)) =
      (fun v => (if h : v.val.val < n then localCoefficient ⟨v.val.val, h⟩ else 0) *
        CountingPolynomial.boolValue
          (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v.val.val))) :=
    funext fun v => by rw [dif_pos v.val.isLt, assignment_bit]
  rw [hfun, localSum_range groupOf group (fun v => (if h : v < n then localCoefficient ⟨v, h⟩ else 0) *
    CountingPolynomial.boolValue (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)))]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hv' : v < n := Finset.mem_range.mp hv
  rw [dif_pos hv', hG v hv']
  by_cases hg : groupOf ⟨v, hv'⟩ = group
  · rw [if_pos hg, if_pos (by rw [hg])]
    cases mask.testBit (LocalAssignmentLoop.countBefore groupOf group v) <;>
      simp [CountingPolynomial.boolValue]
  · rw [if_neg hg, if_neg (fun h => hg (Fin.ext h))]
    simp

/-- The group product as a range product. -/
theorem groupValue_range (formula : WeightedSystem.System n)
    (clauseGroup : Fin formula.constraints.length → Fin groups) (group : Fin groups)
    (value : WeightedSystem.Incidence formula → K) :
    groupValue formula clauseGroup group value =
      ∏ e ∈ Finset.range formula.constraints.length,
        (if h : e < formula.constraints.length then
          (if clauseGroup ⟨e, h⟩ = group then clauseValue formula value ⟨e, h⟩ else 1) else 1) := by
  rw [groupValue, scanProduct_correct, mul_one, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [dif_pos e.isLt]

/-- **The specification's group sum is the formula computed by `sumGroupT`.** -/
theorem sumGroup_eq {P : ℕ} (formula : WeightedSystem.System n) (groupOf : Fin n → Fin groups)
    (clauseGroup : Fin formula.constraints.length → Fin groups) (group : Fin groups)
    (rowAt : Fin rows → Row)
    (measurement : ∀ g, Row → GroupedDeformation.LocalVariable groupOf g → ℤ)
    (localCoefficient : WeightedSystem.Incidence formula → Fin n → ZMod P)
    (measurementCoefficient : WeightedSystem.Incidence formula → Fin groups → Row → ZMod P)
    (target : Fin groups → Row → ℤ) (supportBit : Fin n → Bool)
    (correctionValue : WeightedSystem.Incidence formula → ZMod P)
    (G SB CG AR Td : ℕ → ℕ) (Cp Cn : ℕ → ℕ → ℕ) (D : ℕ) (Wt : ℕ → ℕ → ZMod P)
    (LC : ℕ → ℕ → ℕ → ZMod P) (MT CR : ℕ → ℕ → ZMod P)
    (hG : ∀ v (h : v < n), G v = (groupOf ⟨v, h⟩).val)
    (hSB : ∀ v (h : v < n), SB v = (supportBit ⟨v, h⟩).toNat)
    (hcoef : ∀ (ρ : Fin rows) v, measurement group (rowAt ρ) v =
      (Cp ρ v.val.val : ℤ) - Cn ρ v.val.val)
    (htarget : ∀ ρ : Fin rows, target group (rowAt ρ) = (Td ρ : ℤ) - D)
    (hCG : ∀ e (h : e < formula.constraints.length), CG e = (clauseGroup ⟨e, h⟩).val)
    (hAR : ∀ e (h : e < formula.constraints.length), AR e = (formula.constraints[e]).scope.length)
    (hWt : ∀ e (h : e < formula.constraints.length) A,
      Wt e A = ((formula.constraints[e]).weight (AssignmentLoop.assignment _ A) : ZMod P))
    (hLC : ∀ e i v (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length) (hv : v < n),
      LC e i v = localCoefficient ⟨⟨e, he⟩, ⟨i, hi⟩⟩ ⟨v, hv⟩)
    (hMT : ∀ e i (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length),
      MT e i = scanSum (fun g => scanSum (fun row =>
        measurementCoefficient ⟨⟨e, he⟩, ⟨i, hi⟩⟩ g (rowAt row) *
          (target g (rowAt row) : ZMod P)) 0) 0)
    (hCR : ∀ e i (he : e < formula.constraints.length)
      (hi : i < (formula.constraints[e]).scope.length),
      CR e i = correctionValue ⟨⟨e, he⟩, ⟨i, hi⟩⟩) :
    WGroupedInnerLoop.sumGroup formula groupOf clauseGroup group rowAt measurement
        localCoefficient measurementCoefficient target supportBit correctionValue =
      ∑ mask ∈ Finset.range (2 ^ LocalAssignmentLoop.countBefore groupOf group n),
        if (∀ ρ < rows,
            ∑ v ∈ Finset.range n, (if G v = group.val then 1 else 0) * (Cp ρ v *
                (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat) + D =
            Td ρ + ∑ v ∈ Finset.range n, (if G v = group.val then 1 else 0) * (Cn ρ v *
                (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat)) ∧
          (∀ v < n, G v = group.val → SB v = 1 →
            mask.testBit (LocalAssignmentLoop.countBefore groupOf group v) = true) then
          ∏ e ∈ Finset.range formula.constraints.length,
            (if CG e = group.val then
              ∑ A ∈ Finset.range (2 ^ AR e), Wt e A *
                ∏ i ∈ Finset.range (AR e),
                  (if A.testBit i then
                    (∑ v ∈ Finset.range n, (if G v = group.val then (1 : ZMod P) else 0) *
                      (LC e i v * ((mask.testBit
                        (LocalAssignmentLoop.countBefore groupOf group v)).toNat : ZMod P))) +
                      MT e i + CR e i
                  else 1 - ((∑ v ∈ Finset.range n, (if G v = group.val then (1 : ZMod P) else 0) *
                      (LC e i v * ((mask.testBit
                        (LocalAssignmentLoop.countBefore groupOf group v)).toNat : ZMod P))) +
                      MT e i + CR e i))
            else 1)
        else 0 := by
  rw [WGroupedInnerLoop.sumGroup, sumLoop_correct, add_zero, LocalAssignmentLoop.groupSize]
  refine Finset.sum_congr rfl fun mask _ => ?_
  have hallowed : WGroupedInnerLoop.allowed groupOf group rowAt (measurement group) (target group)
      supportBit mask = true ↔
      (∀ ρ < rows,
          ∑ v ∈ Finset.range n, (if G v = group.val then 1 else 0) * (Cp ρ v *
              (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat) + D =
          Td ρ + ∑ v ∈ Finset.range n, (if G v = group.val then 1 else 0) * (Cn ρ v *
              (mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat)) ∧
        (∀ v < n, G v = group.val → SB v = 1 →
          mask.testBit (LocalAssignmentLoop.countBefore groupOf group v) = true) := by
    rw [WGroupedInnerLoop.allowed, Bool.and_eq_true,
      measurementTest_iff groupOf group rowAt (measurement group) (target group) mask G hG Cp Cn
        Td D hcoef htarget, supportTest_iff]
    refine and_congr Iff.rfl ⟨fun h v hv hg hs => h v hv (by rw [← hG v hv]; exact hg)
      (by rw [← hSB v hv]; exact hs), fun h v hv hg hs => h v hv (by rw [hG v hv]; exact hg)
      (by rw [hSB v hv]; exact hs)⟩
  by_cases hcond : WGroupedInnerLoop.allowed groupOf group rowAt (measurement group)
      (target group) supportBit mask = true
  · rw [if_pos hcond, if_pos (hallowed.mp hcond), groupValue_range]
    refine Finset.prod_congr rfl fun e he => ?_
    have he' : e < formula.constraints.length := Finset.mem_range.mp he
    rw [dif_pos he', hCG e he']
    by_cases hg : clauseGroup ⟨e, he'⟩ = group
    · rw [if_pos hg, if_pos (by rw [hg]), clauseValue_range, hAR e he']
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [hWt e he' A]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi' : i < (formula.constraints[e]).scope.length := Finset.mem_range.mp hi
      have hi'' : i < (formula.constraints[(⟨e, he'⟩ : Fin formula.constraints.length)]).scope.length :=
        hi'
      rw [dif_pos hi'', linearValue_range groupOf group rowAt _ _ (target) mask G hG, hMT e i he' hi',
        hCR e i he' hi']
      have hsum : ∑ v ∈ Finset.range n, (if G v = group.val then (1 : ZMod P) else 0) *
          ((if h : v < n then localCoefficient ⟨⟨e, he'⟩, ⟨i, hi'⟩⟩ ⟨v, h⟩ else 0) *
            ((mask.testBit (LocalAssignmentLoop.countBefore groupOf group v)).toNat : ZMod P)) =
          ∑ v ∈ Finset.range n, (if G v = group.val then (1 : ZMod P) else 0) *
            (LC e i v * ((mask.testBit
              (LocalAssignmentLoop.countBefore groupOf group v)).toNat : ZMod P)) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [dif_pos (Finset.mem_range.mp hv), hLC e i v he' hi' (Finset.mem_range.mp hv)]
      rw [hsum]
    · rw [if_neg hg, if_neg (fun h => hg (Fin.ext h))]
  · rw [if_neg hcond, if_neg (fun h => hcond (hallowed.mpr h))]

end NtimeDspace.InnerLoopSpec
