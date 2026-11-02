import NtimeDspace.HermiteWeightBudget

/-!
Global machine certificates for the complete Hermite-weight loop. The header
contains all five scalar parameters. Raw remaining/accumulator registers need
not satisfy reachable-state bounds: every coefficient query is normalized to
the certified bounded domain. The step budget separately charges the retained
state and the coefficient routine's quadratic-bit workspace.
-/

namespace NtimeDspace.HermiteWeightSpace

open Turing Turing.MultiTapeTM ComputableInSpace HermiteWeightLoop HermiteWeightBudget

private abbrev encData := encPair encHeader (encPair encNat encNat)

private theorem stateData_inSpace :
    ComputableInSpace stateData encState encData (fun s => (encState s).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem header_inSpace :
    ComputableInSpace State.header encState encHeader (fun s => (encState s).length) :=
  fst' stateData_inSpace

private theorem rawHeader_inSpace :
    ComputableInSpace (fun h : Header => h.val) encHeader HermiteFactorSpace.encInput
      (fun h => (encHeader h).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem headerFields_inSpace :
    ComputableInSpace (fun s : State => s.header.val) encState HermiteFactorSpace.encInput
      (fun s => (encState s).length) :=
  budget_comp_linear rawHeader_inSpace header_inSpace

private theorem modulus_inSpace :
    ComputableInSpace (fun s : State => modulus s.header) encState encNat
      (fun s => (encState s).length) := fst' headerFields_inSpace

private theorem count_inSpace :
    ComputableInSpace (fun s : State => count s.header) encState encNat
      (fun s => (encState s).length) := fst' (snd' headerFields_inSpace)

private theorem node_inSpace :
    ComputableInSpace (fun s : State => node s.header) encState encNat
      (fun s => (encState s).length) := fst' (snd' (snd' headerFields_inSpace))

private theorem order_inSpace :
    ComputableInSpace (fun s : State => order s.header) encState encNat
      (fun s => (encState s).length) := fst' (snd' (snd' (snd' headerFields_inSpace)))

private theorem point_inSpace :
    ComputableInSpace (fun s : State => point s.header) encState encNat
      (fun s => (encState s).length) := snd' (snd' (snd' (snd' headerFields_inSpace)))

private theorem remaining_inSpace :
    ComputableInSpace State.remaining encState encNat (fun s => (encState s).length) :=
  fst' (snd' stateData_inSpace)

private theorem accumulator_inSpace :
    ComputableInSpace State.accumulator encState encNat (fun s => (encState s).length) :=
  snd' (snd' stateData_inSpace)

private theorem assemble {α : Type} {encIn : α ↪ List Bool} {B : α → ℕ}
    {header : α → Header} {remaining accumulator : α → ℕ}
    (hh : ComputableInSpace header encIn encHeader B)
    (hr : ComputableInSpace remaining encIn encNat B)
    (ha : ComputableInSpace accumulator encIn encNat B) :
    ComputableInSpace (fun x => (⟨header x, remaining x, accumulator x⟩ : State))
      encIn encState B :=
  (budget_prod hh (budget_prod hr ha)).of_enc_eq fun _ => rfl

theorem initial_inSpace :
    ComputableInSpace initial encHeader encState (fun h => (encHeader h).length) := by
  have identity : ComputableInSpace (fun h : Header => h) encHeader encHeader
      (fun h => (encHeader h).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  exact assemble identity (fst' (snd' (snd' (snd' rawHeader_inSpace))))
    (budget_const (encB := encNat) 0 (.refl _))

theorem queryIndex_inSpace :
    ComputableInSpace queryIndex encState encNat (fun s => (encState s).length) :=
  budget_natMod (budget_natPred remaining_inSpace) (budget_natSucc modulus_inSpace)

/-- Building the bounded subtype adds no proof or validation oracle to the
runtime word: its encoding is exactly the five computed binary scalars. -/
theorem coefficientInput_inSpace :
    ComputableInSpace coefficientInput encState HermiteCoefficientMachine.encBoundedInput
      (fun s => (encState s).length) :=
  (budget_prod modulus_inSpace (budget_prod count_inSpace
    (budget_prod node_inSpace (budget_prod order_inSpace queryIndex_inSpace)))).of_enc_eq
      fun _ => rfl

/-- Reuse the actual coefficient machine, charging its workspace in addition
to the argument-generation budget. -/
theorem coefficient_inSpace :
    ComputableInSpace (fun s => HermiteCoefficientMachine.coefficient (coefficientInput s).val)
      encState encNat stepBudget :=
  HermiteCoefficientMachine.coefficient_inSpace_bits.comp coefficientInput_inSpace

private theorem liftBudget {β : Type} {enc : β ↪ List Bool} {f : State → β}
    (h : ComputableInSpace f encState enc (fun s => (encState s).length)) :
    ComputableInSpace f encState enc stepBudget :=
  h.mono_le (fun s => Nat.le_add_right _ (bitBudget s.header))

theorem power_inSpace :
    ComputableInSpace (fun s : State =>
      ResidueArithmetic.power (modulus s.header) (point s.header) (queryIndex s))
      encState encNat stepBudget := by
  have arguments := budget_prod (liftBudget modulus_inSpace)
    (budget_prod (liftBudget point_inSpace) (liftBudget queryIndex_inSpace))
  have computed := budget_comp_linear ResidueArithmetic.power_inSpace arguments
  exact computed

private theorem accumulated_inSpace :
    ComputableInSpace (fun s : State => ResidueArithmetic.add (modulus s.header)
      (ResidueArithmetic.mul (modulus s.header)
        (HermiteCoefficientMachine.coefficient (coefficientInput s).val)
        (ResidueArithmetic.power (modulus s.header) (point s.header) (queryIndex s)))
      s.accumulator) encState encNat stepBudget := by
  have product := budget_comp_linear ResidueArithmetic.mul_inSpace
    (budget_prod (liftBudget modulus_inSpace) (budget_prod coefficient_inSpace power_inSpace))
  exact budget_comp_linear ResidueArithmetic.add_inSpace
    (budget_prod (liftBudget modulus_inSpace) (budget_prod product (liftBudget accumulator_inSpace)))

/-- The complete transition certificate is global on encoded states. Only
the header's input-domain conditions are used; counters may be arbitrary. -/
theorem step_inSpace : ComputableInSpace HermiteWeightLoop.step encState encState stepBudget := by
  have unchanged : ComputableInSpace (fun s : State => s) encState encState stepBudget :=
    liftBudget (of_inO (ComputableInO.of_eq fun _ => rfl))
  have advanced := assemble (liftBudget header_inSpace)
    (budget_natPred (liftBudget remaining_inSpace)) accumulated_inSpace
  apply (budget_ite (budget_natIsZero (liftBudget remaining_inSpace)) unchanged advanced).of_enc_eq
  intro s
  simp only [HermiteWeightLoop.step, decide_eq_true_eq]

theorem halted_inSpace :
    ComputableInSpace halted encState encBool (fun s => (encState s).length) :=
  budget_natIsZero remaining_inSpace

theorem output_inSpace :
    ComputableInSpace output encState encNat (fun s => (encState s).length) :=
  accumulator_inSpace

end NtimeDspace.HermiteWeightSpace
