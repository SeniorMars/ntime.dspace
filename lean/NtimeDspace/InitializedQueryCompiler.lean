/-
The multi-pass proof is adapted from Complexitylib's QueryMachine.lean.
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE file.
-/
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine

/-!
# Query machines with a computed initial state

The initializer reads the original encoded input and computes only the initial
state. The multi-pass simulation then queries that same read-only input; no
whole-input work-tape copy is introduced. Its callbacks are those of one fixed
query machine, independent of the input-dependent initial state.

Initialization is certified at the requested budget. Global callback-space
certificates, first halting, output correctness, and reachable encoded-state
bounds remain explicit premises. Times and pass counts below are proof
witnesses rather than runtime clocks.
-/

namespace NtimeDspace.InitializedQueryCompiler

open Turing Turing.MultiTapeTM Turing.QueryMachine Turing.QueryMachine.Simulation

def withInitial {σ : Type} (machine : QueryMachine σ) (state : σ) : QueryMachine σ :=
  { machine with init := state }

@[simp] theorem withInitial_init {σ : Type} (machine : QueryMachine σ) (state : σ) :
    (withInitial machine state).init = state := rfl

@[simp] theorem withInitial_query {σ : Type} (machine : QueryMachine σ) (state : σ) :
    (withInitial machine state).query = machine.query := rfl

@[simp] theorem withInitial_next {σ : Type} (machine : QueryMachine σ) (state : σ) :
    (withInitial machine state).next = machine.next := rfl

@[simp] theorem withInitial_emit {σ : Type} (machine : QueryMachine σ) (state : σ) :
    (withInitial machine state).emit = machine.emit := rfl

@[simp] theorem withInitial_halted {σ : Type} (machine : QueryMachine σ) (state : σ) :
    (withInitial machine state).halted = machine.halted := rfl

@[simp] theorem withInitial_finish {σ : Type} (machine : QueryMachine σ) (state : σ) :
    (withInitial machine state).finish = machine.finish := rfl

@[simp] theorem withInitial_read {σ : Type} (machine : QueryMachine σ) (state : σ)
    (input : List Bool) : (withInitial machine state).read input = machine.read input := rfl

@[simp] theorem withInitial_step {σ : Type} (machine : QueryMachine σ) (state : σ)
    (input : List Bool) : (withInitial machine state).step input = machine.step input := rfl

/-- The existing pass simulation uses only the callbacks; its starting state
can be any computed state. -/
theorem initialized_passState_eq {σ : Type} (machine : QueryMachine σ)
    (state : σ) (input : List Bool) (index : ℕ) :
    passState ((state, 0, none) : PassState σ) (passNext machine) (passEnd machine) input index =
      ((withInitial machine state).run input index, 0, none) :=
  Simulation.passState_eq (withInitial machine state) input index

/-- A certified initializer replaces the fixed initial-state assumption, without
charging the length of the original input as work space. -/
theorem computableInSpace {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {σ : Type} {encS : σ ↪ List Bool} (M : QueryMachine σ) (initial : α → σ)
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace M.next (encPair encS (encOption encBool)) encS
      fun p => (encPair encS (encOption encBool) p).length)
    (hemit : ComputableInSpace M.emit (encPair encS (encOption encBool)) encBits
      fun p => (encPair encS (encOption encBool) p).length)
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (hfinish : ComputableInSpace M.finish encS encBits fun s => (encS s).length)
    {f : α → β} (time : α → ℕ)
    (hhalt : ∀ a, M.halted ((withInitial M (initial a)).run (enc a) (time a)) = true)
    (hpre : ∀ a, ∀ t < time a, M.halted ((withInitial M (initial a)).run (enc a) t) = false)
    (hf : ∀ a, encOut (f a) = (withInitial M (initial a)).output (enc a) (time a))
    (S : α → ℕ)
    (initialSpace : ComputableInSpace initial enc encS S)
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hsize : ∃ c, ∀ a, ∀ t ≤ time a, (encS ((withInitial M (initial a)).run (enc a) t)).length ≤ c * S a) :
    ∃ t c, ComputableInTimeAndSpace f enc encOut t fun a => c * S a := by
  obtain ⟨cS, hS⟩ := hsize
  replace hquery := hquery.tidy
  replace hnext := hnext.tidy
  replace hemit := hemit.tidy
  replace hhalted := hhalted.tidy
  replace hfinish := hfinish.tidy
  have hS1 (a : α) : 1 ≤ S a := (Nat.le_add_left _ _).trans (hlog a)
  have hS' (a : α) (t : ℕ) :
      (encS ((withInitial M (initial a)).run (enc a) t)).length ≤ cS * S a := by
    rcases le_or_gt t (time a) with h | h
    · exact hS a t h
    · rw [(withInitial M (initial a)).run_eq_of_le _ (hhalt a) h.le]
      exact hS a _ le_rfl
  -- the parts of the simulation
  have passInitializer : ComputableInSpace
      (fun state : σ => ((state, 0, none) : PassState σ)) encS (encPass encS)
      (fun state => (encS state).length) := by
    have identity : ComputableInSpace (fun state : σ => state) encS encS
        (fun state => (encS state).length) :=
      ComputableInSpace.of_inO (ComputableInO.of_eq fun _ => rfl)
    exact ComputableInSpace.budget_prod identity
      (ComputableInSpace.budget_prod
        (ComputableInSpace.budget_const 0 (.refl _))
        (ComputableInSpace.budget_const none (.refl _)))
  have initialized := ComputableInSpace.budget_comp_linear passInitializer initialSpace
  obtain ⟨TI, cI, hI, -⟩ := initialized.tidy
  obtain ⟨cE, hE⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair (encPass encS) encBool) (encOut := encBits) ([] : List Bool)
  obtain ⟨TN, cN, hN, -⟩ := passNext_inSpace (M' := M) hquery
  obtain ⟨TPE, cPE, hPE, -⟩ := passEmit_inSpace (M' := M) hemit hhalted
  obtain ⟨TPN, cPN, hPN, -⟩ := passEnd_inSpace (M' := M) hnext hhalted
  obtain ⟨TC, cC, hC, -⟩ := passCont_inSpace (M' := M) hhalted
  obtain ⟨TF, cF, hF, -⟩ := passFinish_inSpace (M' := M) hfinish
  -- the states of the passes
  have hP (a : α) (i : ℕ) := initialized_passState_eq M (initial a) (enc a) i
  have hQ (a : α) (i : ℕ) {j : ℕ} (hj : j ≤ (enc a).length) :
      streamState (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a) i)
        (passNext M) (enc a) j =
        ((withInitial M (initial a)).run (enc a) i, j, ((enc a).take j)[M.query ((withInitial M (initial a)).run (enc a) i)]?) := by
    rw [hP, (streamState_passNext M) _ _ hj]
  -- the encoded states of the passes are logarithmic
  set K := 2 * cS + 6 with hK
  have hlenQ (a : α) (i : ℕ) {j : ℕ} (hj : j ≤ (enc a).length) :
      (encPass encS (streamState (passState ((initial a, 0, none) : PassState σ) (passNext M)
        (passEnd M) (enc a) i) (passNext M) (enc a) j)).length ≤
        K * S a := by
    rw [hQ a i hj]
    refine (length_encPass_le encS _).trans ?_
    have h₁ := hS' a i
    have h₂ := (length_encNat_le_log2 hj).trans (hlog a)
    have := hS1 a
    simp only at h₂ ⊢
    rw [hK]
    nlinarith
  have hlenP (a : α) (i : ℕ) :
      (encPass encS (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M)
        (enc a) i)).length ≤ K * S a := by
    rw [hP]
    refine (length_encPass_le encS _).trans ?_
    have h₁ := hS' a i
    have := hS1 a
    simp only [encNat_apply, Nat.zero_bits, List.length_nil]
    rw [hK]
    nlinarith
  -- the passes
  have hpass (a : α) : ∀ i ≤ time a - 1,
      (passCont M) (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a)
        (i + 1)) = decide (i < time a - 1) := by
    intro i hi
    rw [hP, passCont]
    have := (withInitial M (initial a)).halted_run_iff (enc a) (hhalt a) (hpre a) (i + 1)
    simp only [withInitial_halted] at this
    rcases Nat.eq_zero_or_pos (time a) with h0 | hpos
    · rw [h0] at this hi ⊢
      have hi0 : i = 0 := by omega
      subst hi0
      simp [this.mpr (by omega)]
    · by_cases hlt : i < time a - 1
      · have : M.halted ((withInitial M (initial a)).run (enc a) (i + 1)) = false := hpre a _ (by omega)
        simp [this, hlt]
      · simp [this.mpr (by omega), hlt]
  -- the output
  have hout (a : α) : encOut (f a) =
      ((List.range (time a - 1 + 1)).map fun i =>
        streamEmit (passNext M) (fun p => encBits ((fun _ => ([] : List Bool)) p))
          (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a) i)
          (enc a) ++
        encBits ((passEmit M) (streamState (passState ((initial a, 0, none) : PassState σ)
          (passNext M) (passEnd M) (enc a) i) (passNext M) (enc a) (enc a).length))).flatten ++
      encBits ((passFinish M) (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M)
        (enc a) (time a - 1 + 1))) := by
    rw [hf, (withInitial M (initial a)).output_eq_of_not_halted _ (hpre a)]
    simp only [encBits_apply, streamEmit_const_nil, List.nil_append, hP,
      (streamState_passNext_length M), passEmit, passFinish, withInitial_emit,
      withInitial_finish, withInitial_read]
    rcases Nat.eq_zero_or_pos (time a) with h0 | hpos
    · rw [h0]
      have h1 := (withInitial M (initial a)).run_eq_of_le (enc a) (h0 ▸ hhalt a) (show 0 ≤ 1 by omega)
      have h2 : M.halted (initial a) = true := by simpa [h0, withInitial] using hhalt a
      simp [h1, h2]
    · rw [Nat.sub_add_cancel hpos]
      congr 2
      refine List.map_congr_left fun i hi => ?_
      rw [hpre a i (List.mem_range.mp hi)]
      rfl
  -- the bounds of the simulation
  set tN : PassState σ × Bool → ℕ := fun p => cN * (TN p + 1)
  set tPE : PassState σ → ℕ := fun q => cPE * (TPE q + 1)
  set tPN : PassState σ → ℕ := fun q => cPN * (TPN q + 1)
  set tC : PassState σ → ℕ := fun q => cC * (TC q + 1)
  have key := ComputableTidilyInTimeAndSpace.multiPassFold (encA := encBool)
    (encS := encPass encS) (encE := encBits) (encE' := encBits) (encF := encBits)
    (encIn := enc) (encOut := encOut)
    (⟨(), fun _ b => (none, some b)⟩ : InputReader Bool Unit) (fun b => [b])
    (fun _ => List.cons_ne_nil _ _) (fun a rest => by simp [InputReader.read])
    (fun a => enc a) (fun a => by simp)
    (init := fun a => ((initial a, 0, none) : PassState σ)) (next := (passNext M))
    (emit := fun _ => ([] : List Bool)) (passEmit := (passEmit M)) (passEnd := (passEnd M))
    (cont := (passCont M)) (finish := (passFinish M)) (g := f) (passes := fun a => time a - 1)
    hI hN hE.computableTidilyInTimeAndSpace hPE hPN hC hF
    hpass hout
    (tMax := fun a => ∑ i ∈ Finset.range (time a - 1 + 1),
      ((∑ j ∈ Finset.range (enc a).length,
        (tN (streamState (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M)
          (enc a) i) (passNext M) (enc a) j, (enc a).getD j false) + (2 * cE + 2))) +
        (tPE (streamState (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M)
          (enc a) i) (passNext M) (enc a) (enc a).length) +
        tPN (streamState (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M)
          (enc a) i) (passNext M) (enc a) (enc a).length) +
        tC (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a) (i + 1)))))
    (sMax := fun a =>
      (2 * cN + cPE + cPN + cC + 4) * ((2 * K + 3) * S a))
    (lMax := fun a => (K + 1) * S a)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left
  · intro a i hi j hj
    rw [← List.getD_eq_getElem _ false hj]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    refine le_trans ?_ (Nat.le_add_right _ _)
    exact Finset.single_le_sum (f := fun j => tN (streamState (passState
      ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a) i) (passNext M) (enc a) j,
        (enc a).getD j false) + (2 * cE + 2)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hj)
  · intro a i hi j hj
    have h := hlenQ a i hj.le
    simp only [length_encPair, encBool_apply, List.length_singleton] at h ⊢
    nlinarith
  · intro a i hi
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    exact Nat.le_add_left _ _
  · intro a i hi
    have h₁ := hlenQ a i (le_refl (enc a).length)
    have h₂ := hlenP a (i + 1)
    have := hS1 a
    simp only at h₁ h₂ ⊢
    nlinarith
  · intro a i hi j hj
    exact (hlenQ a i hj).trans (Nat.mul_le_mul_right _ (Nat.le_succ K))
  · intro a
    exact (hlenP a _).trans (Nat.mul_le_mul_right _ (Nat.le_succ K))
  · intro a j hj
    have := hS1 a
    simp only [encBool_apply, List.length_singleton]
    nlinarith
  obtain ⟨c, h⟩ := key
  refine ⟨_, c * (2 * cI + cF * (K + 1) + (2 * cN + cPE + cPN + cC + 4) * (2 * K + 3) + (K + 1) + 1),
    h.computableInTimeAndSpace.mono (fun _ => le_rfl) fun a => ?_⟩
  have h₁ := hlenP a (time a - 1 + 1)
  have hL := hS1 a
  simp only at h₁ ⊢
  generalize S a = L at *
  generalize (encPass encS (passState ((initial a, 0, none) : PassState σ) (passNext M) (passEnd M)
    (enc a) (time a - 1 + 1))).length = E at *
  rw [Nat.mul_assoc]
  refine Nat.mul_le_mul_left c ?_
  nlinarith

/-- Existential termination is enough. The least halting time is used only
to certify the fixed multi-pass machine, not stored in its working state. -/
theorem of_termination {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {σ : Type} {encS : σ ↪ List Bool} (M : QueryMachine σ) (initial : α → σ)
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace M.next (encPair encS (encOption encBool)) encS
      fun p => (encPair encS (encOption encBool) p).length)
    (hemit : ComputableInSpace M.emit (encPair encS (encOption encBool)) encBits
      fun p => (encPair encS (encOption encBool) p).length)
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (hfinish : ComputableInSpace M.finish encS encBits fun s => (encS s).length)
    {f : α → β}
    (terminates : ∀ a, ∃ n, M.halted ((withInitial M (initial a)).run (enc a) n) = true)
    (output : ∀ a n, M.halted ((withInitial M (initial a)).run (enc a) n) = true →
      encOut (f a) = (withInitial M (initial a)).output (enc a) n)
    (S : α → ℕ) (initialSpace : ComputableInSpace initial enc encS S)
    (hlog : ∀ a, (enc a).length.log2 + 1 ≤ S a)
    (hsize : ∃ c, ∀ a n, (encS ((withInitial M (initial a)).run (enc a) n)).length ≤ c * S a) :
    ∃ time C, ComputableInTimeAndSpace f enc encOut time (fun a => C * S a) := by
  let time : α → ℕ := fun a => Nat.find (terminates a)
  apply computableInSpace M initial hquery hnext hemit hhalted hfinish time
  · intro a
    exact Nat.find_spec (terminates a)
  · intro a n earlier
    exact Bool.eq_false_iff.mpr (Nat.find_min (terminates a) earlier)
  · intro a
    exact output a _ (Nat.find_spec (terminates a))
  · exact initialSpace
  · exact hlog
  · obtain ⟨c, bounded⟩ := hsize
    exact ⟨c, fun a n _ => bounded a n⟩

end NtimeDspace.InitializedQueryCompiler
