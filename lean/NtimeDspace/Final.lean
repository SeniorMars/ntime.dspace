import NtimeDspace.FinalBounds
import NtimeDspace.FinalSeeds
import NtimeDspace.SmallTable
import NtimeDspace.ProgLength
import NtimeDspace.ComplexityReuse
import NtimeDspace.SemanticReduction
import NtimeDspace.UniformSpace

/-!
# NTIME(n) ⊊ DSPACE(n)

The decider for a language of `NTIME[n]` reads its input length and, below a
threshold, looks the input up in a finite table; above it, it runs the main
loop over schedules and primes. Every value it computes has `O(L)` bits, where
the budget `L` is `O(S)` and `S` is strictly sublinear (`S_sublinear`). The
compiled decider has simultaneous time `2^(C*S n)` and space `C*S n` for one
constant `C` and every input length. Consequently `NTIME[n] ⊆ DSPACE[S]`, and
the space hierarchy theorem gives the separation.
-/

namespace NtimeDspace

open ProgTerm Term Budget Parameters Cslib.Complexity Cslib.Complexity.CountingSimulation Filter
  Turing Turing.MultiTapeTM

/-- All words of length `m`. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (words m).flatMap fun v => [false :: v, true :: v]

theorem mem_words {m : ℕ} {v : List Bool} : v ∈ words m ↔ v.length = m := by
  induction m generalizing v with
  | zero => cases v <;> simp [words]
  | succ m ih =>
    cases v with
    | nil => simp [words]
    | cons x v =>
      simp only [words, List.mem_flatMap, List.mem_cons, List.length_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨u, hu, h⟩
        rcases h with h | h <;> (rw [List.cons.injEq] at h; rw [h.2, ih.mp hu])
      · intro h
        exact ⟨v, ih.mpr (by omega), by cases x <;> simp⟩

/-- All words of length below `n0`. -/
def smallWords (n0 : ℕ) : List (List Bool) := (List.range n0).flatMap words

theorem mem_smallWords {n0 : ℕ} {v : List Bool} : v ∈ smallWords n0 ↔ v.length < n0 := by
  simp only [smallWords, List.mem_flatMap, List.mem_range, mem_words]
  exact ⟨fun ⟨_, h, h'⟩ => h' ▸ h, fun h => ⟨_, h, rfl⟩⟩

theorem tm_ite_split {w : List Bool} {L : ℕ} {env : List ℕ} {c t e : Term} {dc d : ℕ}
    (hc : Tm w L dc c env) (hcs : StableAt w c env)
    (ht : 0 < c.denote w env → Tm w L d t env) (he : ¬ 0 < c.denote w env → Tm w L d e env) :
    Tm w L d (ite c t e) env := by
  by_cases h : 0 < c.denote w env
  · have htm := ht h
    intro pre hp
    have hcv : 0 < c.denote w (pre ++ env) := by rw [hcs pre]; exact h
    refine ⟨⟨(hc pre hp).1, ?_⟩, ?_⟩
    · exact (if_pos (show 0 < ProgLang.Prog.eval w (c (pre ++ env).length) (pre ++ env) from hcv)).symm ▸
        (htm pre hp).1
    · simp only [denote_ite, if_pos hcv]; exact (htm pre hp).2
  · have hem := he h
    intro pre hp
    have hcv : ¬ 0 < c.denote w (pre ++ env) := by rw [hcs pre]; exact h
    refine ⟨⟨(hc pre hp).1, ?_⟩, ?_⟩
    · exact (if_neg (show ¬ 0 < ProgLang.Prog.eval w (c (pre ++ env).length) (pre ++ env) from hcv)).symm ▸
        (hem pre hp).1
    · simp only [denote_ite, if_neg hcv]; exact (hem pre hp).2

/-- Every language in nondeterministic linear time has one deterministic decider
with simultaneous time `2^(C*S n)` and space `C*S n`, including the finitely many
input lengths handled by the lookup table. The constant may depend on the language. -/
theorem ntime_simultaneous_bounds {A : Set (List Bool)}
    (hA : A ∈ NTIME encBits (fun n => n)) :
    ∃ C, DecidableInTimeAndSpace A encBits
      (fun a => 2 ^ (C * S a.length)) (fun a => C * S a.length) := by
  classical
  obtain ⟨k, State, hfin, machine, s, e, c, hc, hM⟩ := SemanticReduction.exists_networks_of_mem_NTIME hA
  set C := 6 * (3 * k + 1) * (s + k + 4) with hC_def
  set C0 := bigC k s c C with hC0_def
  have hM' : ∀ a : List Bool, (a ∈ A ↔ ∃ σ < scheduleCount (k + 1) (clk c a.length),
        0 < (blockNetworkOf machine e (a, clk c a.length, σ)).2.contraction) ∧
      ∀ σ, ExplicitAdmissible C (clk c a.length) (blockNetworkOf machine e (a, clk c a.length, σ)) :=
    fun a => hM a
  have hcorr := eventually_main_correct (machine := machine) (e := e) hc hM'
  have hfacts := eventually_mainFacts (k := k) (s := s) (C := C) hc (le_refl C0)
  have hseeds := eventually_seeds (machine := machine) (e := e) hc (fun a σ => (hM' a).2 σ)
  have hT := (tendsto_edgesN k s c (by omega)).eventually (eventually_ge_atTop 1)
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp (hcorr.and (hfacts.and (hseeds.and hT)))
  set vs := (smallWords n0).filter (fun v => decide (v ∈ A)) with hvs
  set C1 := n0 + vs.length with hC1
  set B : ℕ → ℕ := fun n => L k s c C0 n + C1 with hB
  set P : Term := ite (lt (lvl 0) (const n0)) (tableT vs) (mainT k s c e machine (lvl 0)) with hP
  have hval : ∀ a : List Bool, (lvl 0).denote a [a.length] = a.length := fun a => hx_value
  have htm : ∀ a : List Bool, Tm a (B a.length) 3 P [a.length] := by
    intro a
    have hLB : L k s c C0 a.length ≤ B a.length := Nat.le_add_right _ _
    have hC1B : C1 < 2 ^ B a.length :=
      lt_of_le_of_lt (Nat.le_add_left _ _) Nat.lt_two_pow_self
    have hnB : a.length < 2 ^ B a.length :=
      lt_of_lt_of_le (lt_two_pow_L k s c C0 a.length (by omega)) (Nat.pow_le_pow_right (by norm_num) hLB)
    have hL8 : 8 ≤ B a.length := le_trans (by have := C0_le_L k s c C0 a.length; omega) hLB
    have hx : Tm a (B a.length) 1 (lvl 0) [a.length] := tm_x hnB
    refine tm_ite_split (t_lt hx (t_const (by omega)) (by omega))
      ((hx_stable).lt (stableAt_const _ _)) (fun _ => ?_) (fun hge => ?_)
    · refine (tm_tableT vs (by omega) (fun v hv => ?_) (by omega) hx).mono (by omega)
      have := mem_smallWords.mp (List.mem_filter.mp hv).1
      omega
    · have hge' : n0 ≤ a.length := by
        rw [denote_lt, hval, denote_const] at hge
        split_ifs at hge with h1
        · exact absurd Nat.one_pos hge
        · omega
      obtain ⟨-, hf, hs, hpos⟩ := hn0 a.length hge'
      exact tm_mainT_of_facts hc (hf.mono hLB) (ports_le a (fun σ => (hM' a).2 σ) hpos) (hs a rfl)
  have hdec : ∀ a : List Bool, (1 ≤ P.denote a [a.length] ↔ a ∈ A) := by
    intro a
    rw [hP, denote_ite, denote_lt, hval, denote_const]
    by_cases h : a.length < n0
    · rw [if_pos h, if_pos Nat.one_pos]
      have := tableT_denote (w := a) vs []
      rw [List.nil_append] at this
      rw [this, hvs, List.mem_filter, decide_eq_true_iff]
      exact ⟨fun h' => h'.2, fun h' => ⟨mem_smallWords.mpr h, h'⟩⟩
    · rw [if_neg h, if_neg (lt_irrefl 0)]
      exact ((hn0 a.length (by omega)).1 a rfl).symm
  obtain ⟨Cd, hCd⟩ := ProgLang.decidable_of_prog_len (enc := encBits) A (P 1) (fun a => B a.length)
    (fun a => 128 * B a.length) 128
    (fun a => le_trans (log2_add_one_le_L k s c C0 a.length (by omega)) (Nat.le_add_right _ _))
    (fun a => by have := C0_le_L k s c C0 a.length; simp only [hB]; omega) (fun a => le_rfl)
    (fun a => by
      have h1 := lt_two_pow_L k s c C0 a.length (by omega)
      have h2 : 2 ^ L k s c C0 a.length ≤ 2 ^ (128 * B a.length) :=
        Nat.pow_le_pow_right (by norm_num) (by simp only [hB]; omega)
      exact (lt_of_lt_of_le h1 h2).le)
    (fun a => (htm a).bnd) hdec
  obtain ⟨C', hC'⟩ := L_le_S k s c C0 hc
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp hC'
  let Csmall := (Finset.range n1).sup B
  have hBS (n : ℕ) : B n ≤ (2 * C' + C1 + Csmall) * S n := by
    have hS : 1 ≤ S n := by
      have hpow : 1 ≤ (n.log2 + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      exact hpow.trans (Nat.le_add_left _ _)
    by_cases hn : n < n1
    · have hsmall : B n ≤ Csmall := Finset.le_sup (Finset.mem_range.mpr hn)
      exact hsmall.trans (by nlinarith)
    · have hlarge := hn1 n (by omega)
      simp only [hB]
      nlinarith
  refine ⟨Cd * (2 * C' + C1 + Csmall), hCd.mono (fun a => ?_) (fun a => ?_)⟩
  · apply Nat.pow_le_pow_right (by norm_num)
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left Cd (hBS a.length)
  · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left Cd (hBS a.length)

/-- **`NTIME[n] ⊆ DSPACE[S]`** for the strictly sublinear `S`. -/
theorem ntime_subset_dspace : NTIME encBits (fun n => n) ⊆ DSPACE encBits S := by
  intro A hA
  obtain ⟨C, hC⟩ := ntime_simultaneous_bounds hA
  exact mem_DSPACE_iff.mpr ⟨C, 0, _, hC⟩

/-- **Nondeterministic linear time is strictly contained in deterministic linear space.** -/
theorem ntime_ssubset_dspace :
    Cslib.Complexity.NTIME encBits (fun n => n) ⊂ Cslib.Complexity.DSPACE encBits (fun n => n) :=
  ComplexityReuse.conditional_linear_separation ntime_subset_dspace S_sublinear

end NtimeDspace
