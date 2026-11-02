import NtimeDspace.AssemblyPrep

/-!
# The seed search finds a balanced seed

If some seed number below `2^(2·blk)` is balanced, the seed term (labels from
a variable term implementing the incidence variables) is stable and its value
is balanced (`seed_spec`).
-/

namespace NtimeDspace.ProgTerm

open Term Placement WeightedSystem

variable {w : List Bool} {n : ℕ}

theorem seed_spec (S : System n) (Q bits : ℕ) {QT bitsT IBT nT mT : Term}
    {arity : Term → Term} {varT : Term → Term → Term} {env : List ℕ}
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hb : StableAt w bitsT env)
    (hbv : bitsT.denote w env = bits) (hIB : StableAt w IBT env)
    (hIBv : IBT.denote w env = WSchedulePlacement.inputBits S) (hn : StableAt w nT env)
    (hnv : nT.denote w env = n) (hm : StableAt w mT env)
    (hmv : mT.denote w env = S.constraints.length)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = (S.constraints[e]).scope.length)
    {V : ℕ → ℕ → ℕ} (iV : ImplN2 w env varT V)
    (hV : ∀ inc : Incidence S, V inc.1 inc.2 = (incidenceVariable S inc).val)
    (hex : ∃ s < 2 ^ (2 * blk Q bits (WSchedulePlacement.inputBits S)), balN S Q bits s) :
    StableAt w (seedT QT bitsT IBT nT mT arity
        (fun sd e' i => labelT QT bitsT IBT sd (varT e' i) e')) env ∧
      balN S Q bits ((seedT QT bitsT IBT nT mT arity
        (fun sd e' i => labelT QT bitsT IBT sd (varT e' i) e')).denote w env) := by
  classical
  have key : ∀ pre : List ℕ, (seedT QT bitsT IBT nT mT arity
      (fun sd e' i => labelT QT bitsT IBT sd (varT e' i) e')).denote w (pre ++ env) =
      LocalSim.optCode ((List.range (2 ^ (2 * blk Q bits (WSchedulePlacement.inputBits S)))).find?
        fun s => decide (balN S Q bits s)) - 1 := by
    intro pre
    rw [seedT, denote_sub, denote_const]
    congr 1
    refine denote_firstSeedT S Q bits (hQ.extend pre) (by rw [hQ pre, hQv]) (hb.extend pre)
      (by rw [hb pre, hbv]) (hIB.extend pre) (by rw [hIB pre, hIBv]) (hn.extend pre)
      (by rw [hn pre, hnv]) (hm.extend pre) (by rw [hm pre, hmv]) (iAR.extend pre) hAR
      (LBf := fun sv e i => labelN Q bits sv (WSchedulePlacement.inputBits S) (V e i) e)
      (fun pre2 sT hs => ?_) (fun sv inc => by unfold incLabelN; rw [hV])
    have h := implN2_labelT ((hQ.extend pre).extend pre2) ((hb.extend pre).extend pre2)
      ((hIB.extend pre).extend pre2) hs ((iV.extend pre).extend pre2)
    rw [(hQ.extend pre) pre2, hQ pre, hQv, (hb.extend pre) pre2, hb pre, hbv,
      (hIB.extend pre) pre2, hIB pre, hIBv] at h
    exact h
  refine ⟨fun extra => by rw [key extra, ← key []]; rfl, ?_⟩
  have h0 := key []
  simp only [List.nil_append] at h0
  rw [h0]
  exact (find_witness hex).2

theorem seed_lt (S : System n) (Q bits : ℕ) {QT bitsT IBT nT mT : Term}
    {arity : Term → Term} {varT : Term → Term → Term} {env : List ℕ}
    (hQ : StableAt w QT env) (hQv : QT.denote w env = Q) (hb : StableAt w bitsT env)
    (hbv : bitsT.denote w env = bits) (hIB : StableAt w IBT env)
    (hIBv : IBT.denote w env = WSchedulePlacement.inputBits S) (hn : StableAt w nT env)
    (hnv : nT.denote w env = n) (hm : StableAt w mT env)
    (hmv : mT.denote w env = S.constraints.length)
    {AR : ℕ → ℕ} (iAR : ImplN w env arity AR)
    (hAR : ∀ e (h : e < S.constraints.length), AR e = (S.constraints[e]).scope.length)
    {V : ℕ → ℕ → ℕ} (iV : ImplN2 w env varT V)
    (hV : ∀ inc : Incidence S, V inc.1 inc.2 = (incidenceVariable S inc).val)
    (hex : ∃ s < 2 ^ (2 * blk Q bits (WSchedulePlacement.inputBits S)), balN S Q bits s) :
    (seedT QT bitsT IBT nT mT arity
        (fun sd e' i => labelT QT bitsT IBT sd (varT e' i) e')).denote w env <
      2 ^ (2 * blk Q bits (WSchedulePlacement.inputBits S)) := by
  classical
  have key : ∀ pre : List ℕ, (seedT QT bitsT IBT nT mT arity
      (fun sd e' i => labelT QT bitsT IBT sd (varT e' i) e')).denote w (pre ++ env) =
      LocalSim.optCode ((List.range (2 ^ (2 * blk Q bits (WSchedulePlacement.inputBits S)))).find?
        fun s => decide (balN S Q bits s)) - 1 := by
    intro pre
    rw [seedT, denote_sub, denote_const]
    congr 1
    refine denote_firstSeedT S Q bits (hQ.extend pre) (by rw [hQ pre, hQv]) (hb.extend pre)
      (by rw [hb pre, hbv]) (hIB.extend pre) (by rw [hIB pre, hIBv]) (hn.extend pre)
      (by rw [hn pre, hnv]) (hm.extend pre) (by rw [hm pre, hmv]) (iAR.extend pre) hAR
      (LBf := fun sv e i => labelN Q bits sv (WSchedulePlacement.inputBits S) (V e i) e)
      (fun pre2 sT hs => ?_) (fun sv inc => by unfold incLabelN; rw [hV])
    have h := implN2_labelT ((hQ.extend pre).extend pre2) ((hb.extend pre).extend pre2)
      ((hIB.extend pre).extend pre2) hs ((iV.extend pre).extend pre2)
    rw [(hQ.extend pre) pre2, hQ pre, hQv, (hb.extend pre) pre2, hb pre, hbv,
      (hIB.extend pre) pre2, hIB pre, hIBv] at h
    exact h
  have h0 := key []
  simp only [List.nil_append] at h0
  rw [h0]
  exact (find_witness hex).1

/-- A balanced seed number exists under the conditions of the balanced-schedule theorem. -/
theorem exists_balN (S : System n) (Q bits : ℕ) (hQ : 0 < Q) (a b : ℚ)
    (degrees_positive : 0 < a + b)
    (occurrences : ∀ v, HashVariance.bucketCount (incidenceVariable S) v ≤ a)
    (arity : ∀ e, HashVariance.bucketCount (fun inc : Incidence S => inc.1) e ≤ b)
    (positive : 0 < n) (incidences_positive : 0 < incidenceCount S)
    (incidence_parameter :
      2 * (a + b) * ((2 ^ bits : ℕ) ^ (2 * Q) : ℚ) ^ 2 ≤ incidenceCount S)
    (group_parameter : 2 * (Q : ℚ) * (2 ^ bits : ℕ) ^ 2 ≤ n) :
    ∃ s < 2 ^ (2 * blk Q bits (WSchedulePlacement.inputBits S)), balN S Q bits s := by
  haveI : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  obtain ⟨seed, hbal⟩ := WSchedulePlacement.exists_balanced_schedule (Node := Fin Q) S a b
    degrees_positive occurrences arity positive incidences_positive bits
    (by simpa using incidence_parameter) (by simpa using group_parameter)
  obtain ⟨sd, hsd, hseed⟩ := exists_seed_number S Q bits seed
  exact ⟨sd, hsd, balN_of_balanced S Q bits sd (hseed ▸ hbal)⟩

end NtimeDspace.ProgTerm
