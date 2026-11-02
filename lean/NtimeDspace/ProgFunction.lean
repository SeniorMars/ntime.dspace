/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/
import NtimeDspace.ProgLength

-- upstream: local-only (compiler bridge for the application's program language)

/-!
# Natural-valued programs with length initialization

`ProgLang.computable_of_prog_len` compiles a bounded program to a machine that
returns its natural-number result, encoded by `encNat`. It uses the same
register and logarithmic-input budgets as `ProgLang.decidable_of_prog_len`.

The counter program's query, transition, emission, and halting callbacks are
unchanged. Its final-output callback reads and encodes the designated register;
`Simulation.evalConfig_inSpace` certifies that callback. Configuration counting
then supplies simultaneous exponential time and linear workspace for one machine.
-/

namespace NtimeDspace.BigCounterProgram

open Turing Turing.MultiTapeTM Turing.CounterProgram

/-- Replace the final output word by the binary value of one register.
Earlier emissions are unchanged; the reachability theorem below excludes them. -/
def withRegisterOutput (P : CounterProgram) (result : ℕ) : QueryMachine Config :=
  { P.toQueryMachine with finish := fun s => encNat (s.2.getD result 0) }

/-- Reaching a halting instruction with the desired register value suffices for
function computation. The register bound includes the final configuration. -/
theorem simultaneous_bounds_of_register_reaches (P : CounterProgram) {α : Type}
    {enc : α ↪ List Bool} (f : α → ℕ) (result : ℕ) (budget : α → ℕ) (c : ℕ)
    (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (h : ∀ a, ∃ s, P.Reaches (enc a)
        (fun s => (P.instr s.1).IsStep ∧ (encList encNat s.2).length ≤ c * budget a)
        P.init s ∧
      P.halted s = true ∧ s.2.getD result 0 = f a ∧
      (encList encNat s.2).length ≤ c * budget a) :
    ∃ C, ComputableInTimeAndSpace f enc encNat
      (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  choose s hs using h
  choose t ht hpre using fun a => (hs a).1
  have hrun (a : α) (u : ℕ) :
      (withRegisterOutput P result).run (enc a) u = (P.step (enc a))^[u] P.init := rfl
  have hstep (a : α) {u : ℕ} (hu : u < t a) :
      (withRegisterOutput P result).halted
        ((withRegisterOutput P result).run (enc a) u) = false := by
    have := (hpre a u hu).1
    rw [hrun]
    change P.halted ((P.step (enc a))^[u] P.init) = false
    rw [halted]
    revert this
    cases P.instr ((P.step (enc a))^[u] P.init).1 <;> simp [Instr.IsStep, Instr.halts]
  have finishSpace : ComputableInSpace
      (withRegisterOutput P result).finish Simulation.encConfig encBits
      (fun s => (Simulation.encConfig s).length) :=
    ((Simulation.evalConfig_inSpace (.reg result)).of_enc_eq fun _ => rfl).computableInSpace
  refine ComplexityReuse.query_simultaneous_bounds (encState := Simulation.encConfig)
    (withRegisterOutput P result)
    (Simulation.query_inSpace (P := P)).computableInSpace
    (Simulation.exec_inSpace (P := P)).computableInSpace
    (Simulation.emitted_inSpace (P := P)).computableInSpace
    (Simulation.halted_inSpace (P := P)).computableInSpace
    finishSpace t (fun a => ?_) (fun a u hu => hstep a hu) (fun a => ?_)
    budget logarithmic
    ⟨2 * (encNat P.maxLabel).length + 1 + c, fun a u hu => ?_⟩
  · rw [hrun, ht]
    exact (hs a).2.1
  · rw [(withRegisterOutput P result).output_eq_of_not_halted _ (fun i hi => hstep a hi)]
    have hnil : ((List.range (t a)).map fun i =>
        (withRegisterOutput P result).emit
          ((withRegisterOutput P result).run (enc a) i,
            (withRegisterOutput P result).read (enc a)
              ((withRegisterOutput P result).run (enc a) i))).flatten = [] := by
      simp only [List.flatten_eq_nil_iff, List.mem_map, List.mem_range]
      rintro _ ⟨i, hi, rfl⟩
      have := (hpre a i hi).1
      change (P.instr ((P.step (enc a))^[i] P.init).1).emitted = []
      revert this
      cases P.instr ((P.step (enc a))^[i] P.init).1 <;> simp [Instr.IsStep, Instr.emitted]
    rw [hnil, List.nil_append, hrun, ht]
    change encNat (f a) = encNat ((s a).2.getD result 0)
    rw [(hs a).2.2.1]
  · have registerBound :
        (encList encNat ((P.step (enc a))^[u] P.init).2).length ≤ c * budget a := by
      rcases lt_or_eq_of_le hu with hlt | rfl
      · exact (hpre a u hlt).2
      · rw [ht]
        exact (hs a).2.2.2
    have positive : 1 ≤ budget a := (Nat.le_add_left _ _).trans (logarithmic a)
    change (Simulation.encConfig (P.run (enc a) u)).length ≤ _
    calc
      _ ≤ 2 * (encNat P.maxLabel).length + 1 +
          (encList encNat (P.run (enc a) u).2).length :=
        length_encConfig_le P (P.run_fst_le _ u)
      _ ≤ (2 * (encNat P.maxLabel).length + 1) * budget a + c * budget a := by
        change (encList encNat (P.run (enc a) u).2).length ≤ _ at registerBound
        nlinarith
      _ = _ := by ring

end NtimeDspace.BigCounterProgram

namespace NtimeDspace.Structured

open Turing Turing.MultiTapeTM Turing.CounterProgram Stmt

/-- Execute a structured statement, then return its designated natural-valued
register. Both intermediate and final encoded registers obey the same budget. -/
theorem computable_of_exec {α : Type} {enc : α ↪ List Bool} (f : α → ℕ) (s : Stmt)
    (result registers : ℕ) (budget : α → ℕ) (c : ℕ)
    (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (final : α → List ℕ)
    (exec : ∀ a, Exec (enc a) (fun r => (encList encNat r).length ≤ c * budget a) s
      (List.replicate registers 0) (final a))
    (finalBound : ∀ a, (encList encNat (final a)).length ≤ c * budget a)
    (computes : ∀ a, (final a).getD result 0 = f a) :
    ∃ C, ComputableInTimeAndSpace f enc encNat
      (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  let P : CounterProgram := ⟨s.compile 0 ++ [.halt []], registers⟩
  refine BigCounterProgram.simultaneous_bounds_of_register_reaches P f result budget c
    logarithmic fun a => ?_
  have body : P.CodeAt 0 (s.compile 0) :=
    codeAt_of_eq (codeAt_of_code_eq (pre := []) (post := [.halt []]) (by simp [P])) rfl
  have tail : P.CodeAt s.length [.halt []] :=
    codeAt_of_eq (codeAt_of_code_eq (pre := s.compile 0) (post := []) (by simp [P]))
      (by simp)
  have run := (exec a).reaches (P := P) body
  simp only [Nat.zero_add] at run
  refine ⟨(s.length, final a), run, ?_, computes a, finalBound a⟩
  rw [halted, codeAt_singleton.mp tail]
  rfl

end NtimeDspace.Structured

namespace NtimeDspace.ProgLang

open Turing Turing.CounterProgram Structured Prog Turing.MultiTapeTM

/-- A bounded program with the input length in variable `0` computes its full
natural-number value in simultaneous exponential time and linear workspace.
The program is fixed across inputs; no clock or initial length oracle is assumed. -/
theorem computable_of_prog_len {α : Type} {enc : α ↪ List Bool} (f : α → ℕ) (P : Prog)
    (budget K : α → ℕ) (c : ℕ)
    (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (K_pos : ∀ a, 1 ≤ K a) (K_le : ∀ a, K a ≤ c * budget a)
    (len_le : ∀ a, (enc a).length ≤ 2 ^ K a)
    (bounded : ∀ a, P.Bounded (enc a) (2 ^ K a) [(enc a).length])
    (computes : ∀ a, P.eval (enc a) [(enc a).length] = f a) :
    ∃ C, ComputableInTimeAndSpace f enc encNat
      (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  set R := P.span + 4
  have hbudget (a : α) : 1 ≤ budget a := (Nat.le_add_left _ _).trans (logarithmic a)
  have hreg (a : α) {x : List ℕ} (hx : LeB (2 ^ K a) x) (hl : x.length = R) :
      (encList encNat x).length ≤ (R * (2 * c + 3)) * budget a := by
    refine (encList_le_of_LeB hx).trans ?_
    rw [hl, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith [K_le a, hbudget a])
  have hB (a : α) : 2 ≤ 2 ^ K a := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (K_pos a); simpa using this
  have run (a : α) : ∃ final, Exec (enc a) (LeB (2 ^ K a))
      (.seq lengthStmt (P.compile [0] 2 3)) (List.replicate R 0) final ∧
      final.length = R ∧ final.getD 2 0 = P.eval (enc a) [(enc a).length] ∧
      LeB (2 ^ K a) final := by
    set r0 : List ℕ := List.replicate R 0
    have hz : LeB (2 ^ K a) r0 := fun x hx => by
      rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _
    set r1 := r0.set 1 1
    have hb1 : LeB (2 ^ K a) r1 := by
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact hz x hx
      · exact (hB a).trans' (by norm_num)
    have hlen1 : r1.length = R := by simp [r1, r0]
    obtain ⟨r2, e2, l2, v2, -, b2⟩ := lengthLoop_exec (w := enc a) (len_le a)
      ((hB a).trans' (by norm_num))
      (enc a).length r1
      (by simp [r1, r0, List.getD_eq_getElem?_getD, R])
      (by simp [r1, r0, List.getD_eq_getElem?_getD, R])
      (by rw [hlen1]; omega) hb1
    obtain ⟨r3, e3, l3, v3, -, b3⟩ := compile_correct (w := enc a) (B := 2 ^ K a) (hB a)
      P [(enc a).length] [0] 2 3 r2
      ⟨rfl, fun i hi => by
        simp only [List.length_singleton, Nat.lt_one_iff] at hi
        subst hi; simpa using v2⟩
      (by omega) (by rw [l2, hlen1]; omega) b2 (bounded a)
    exact ⟨r3, .seq (.seq (.assign hz) e2) e3, by rw [l3, l2, hlen1], v3, b3⟩
  choose final hfinal using run
  refine Structured.computable_of_exec f (.seq lengthStmt (P.compile [0] 2 3)) 2 R budget
    (R * (2 * c + 3)) logarithmic final (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · obtain ⟨e, -⟩ := hfinal a
    exact (exec_weaken e fun x hx hl => hreg a hx (by simpa using hl)).1
  · obtain ⟨_, l, _, b⟩ := hfinal a
    exact hreg a b l
  · obtain ⟨_, _, v, _⟩ := hfinal a
    rw [v]; exact computes a

end NtimeDspace.ProgLang
