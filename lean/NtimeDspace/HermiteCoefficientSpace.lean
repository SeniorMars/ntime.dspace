import NtimeDspace.HermiteCoefficientLoop
import NtimeDspace.CoefficientTransitionSpace

/-!
# Machine certificates for the closed Hermite coefficient loop

All parameters are stored in the explicit binary input and state. These global
certificates cover initialization, guarded concrete factor access, one complete
transition, the halting test, and result extraction. No callback certificate,
primality assumption, or reachable-state premise is used here. Termination and
the space envelope of a complete evaluation are supplied by separate theorems.
-/

namespace NtimeDspace.HermiteCoefficientSpace

open Turing Turing.MultiTapeTM ComputableInSpace
open HermiteCoefficientLoop

private abbrev encData := encPair encNat (encPair encNat (encPair encNat
  (encPair encNat CoefficientStackEncoding.encState)))

private theorem stateData_inSpace :
    ComputableInSpace stateData encState encData (fun s => (encState s).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem modulus_inSpace :
    ComputableInSpace State.modulus encState encNat (fun s => (encState s).length) :=
  fst' stateData_inSpace

private theorem count_inSpace :
    ComputableInSpace State.count encState encNat (fun s => (encState s).length) :=
  fst' (snd' stateData_inSpace)

private theorem node_inSpace :
    ComputableInSpace State.node encState encNat (fun s => (encState s).length) :=
  fst' (snd' (snd' stateData_inSpace))

private theorem order_inSpace :
    ComputableInSpace State.order encState encNat (fun s => (encState s).length) :=
  fst' (snd' (snd' (snd' stateData_inSpace)))

private theorem evaluator_inSpace :
    ComputableInSpace State.evaluator encState CoefficientStackEncoding.encState
      (fun s => (encState s).length) :=
  snd' (snd' (snd' (snd' stateData_inSpace)))

private theorem rawData_inSpace :
    ComputableInSpace CoefficientStackEncoding.stateData CoefficientStackEncoding.encState
      (encPair CoefficientStackEncoding.encRequest
        (encPair (encOption encNat) (encList CoefficientStackEncoding.encContinuation)))
      (fun s => (CoefficientStackEncoding.encState s).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem requestData_inSpace :
    ComputableInSpace CoefficientStackEncoding.requestData CoefficientStackEncoding.encRequest
      (encPair encNat (encPair encNat (encPair encNat encNat)))
      (fun request => (CoefficientStackEncoding.encRequest request).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem request_inSpace :
    ComputableInSpace (fun s : State => s.evaluator.request) encState
      CoefficientStackEncoding.encRequest (fun s => (encState s).length) :=
  fst' (budget_comp_linear rawData_inSpace evaluator_inSpace)

private theorem requestStart_inSpace :
    ComputableInSpace (fun s : State => s.evaluator.request.start) encState encNat
      (fun s => (encState s).length) :=
  fst' (snd' (budget_comp_linear requestData_inSpace request_inSpace))

private theorem result_inSpace :
    ComputableInSpace (fun s : State => s.evaluator.result) encState (encOption encNat)
      (fun s => (encState s).length) :=
  fst' (snd' (budget_comp_linear rawData_inSpace evaluator_inSpace))

private theorem assembleState {α : Type} {encIn : α ↪ List Bool} {B : α → ℕ}
    {modulus count node order : α → ℕ} {evaluator : α → CoefficientStackEncoding.RawState}
    (hp : ComputableInSpace modulus encIn encNat B)
    (hc : ComputableInSpace count encIn encNat B)
    (hn : ComputableInSpace node encIn encNat B)
    (ho : ComputableInSpace order encIn encNat B)
    (he : ComputableInSpace evaluator encIn CoefficientStackEncoding.encState B) :
    ComputableInSpace (fun x => (⟨modulus x, count x, node x, order x, evaluator x⟩ : State))
      encIn encState B :=
  (budget_prod hp (budget_prod hc (budget_prod hn (budget_prod ho he)))).of_enc_eq
    fun _ => rfl

/-- Initialization constructs height and span by the certified bounded register
iteration, rather than exponentiating an unbounded input height. -/
theorem initial_inSpace :
    ComputableInSpace initial encInput encState (fun input => (encInput input).length) := by
  have fields : ComputableInSpace (fun input : Input => input) encInput encInput
      (fun input => (encInput input).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  have modulus := fst' fields
  have count := fst' (snd' fields)
  have node := fst' (snd' (snd' fields))
  have order := fst' (snd' (snd' (snd' fields)))
  have index := snd' (snd' (snd' (snd' fields)))
  have evaluator := budget_comp_linear CoefficientInitialization.initialState_inSpace
    (budget_prod count (budget_prod (budget_const (encB := encNat) 0 (.refl _)) index))
  exact assembleState modulus count node order evaluator

theorem needsFactor_inSpace :
    ComputableInSpace needsFactor encState encBool (fun s => (encState s).length) := by
  have hasResult := budget_comp_linear
    (of_inO (ComputableInDegree.isSome encNat).inO_one) result_inSpace
  have height := fst' (budget_comp_linear requestData_inSpace request_inSpace)
  have zero := budget_natIsZero height
  have occupied := budget_natLt requestStart_inSpace count_inSpace
  have conditions := budget_prod hasResult (budget_prod zero occupied)
  apply (budget_finite (encC := encBool)
    (fun bits : Bool × Bool × Bool => !bits.1 && bits.2.1 && bits.2.2) conditions).of_enc_eq
  intro s
  cases value : s.evaluator.result <;>
    simp [needsFactor, value]
  rfl

/-- The complete factor access is part of the certified callback, with a fixed
dummy pair outside occupied leaf evaluation. -/
theorem currentFactor_inSpace :
    ComputableInSpace currentFactor encState HermiteFactorSpace.encFactor
      (fun s => (encState s).length) := by
  have computed := budget_comp_linear HermiteFactorSpace.factor_inSpace
    (budget_prod modulus_inSpace (budget_prod count_inSpace
      (budget_prod node_inSpace (budget_prod order_inSpace requestStart_inSpace))))
  exact budget_ite needsFactor_inSpace computed
    (budget_const (encB := HermiteFactorSpace.encFactor) (0, 0) (.refl _))

/-- One fixed finite-control machine performs each closed loop transition,
including factor access and reciprocal arithmetic, on all raw encoded states. -/
theorem step_inSpace :
    ComputableInSpace HermiteCoefficientLoop.step encState encState
      (fun s => (encState s).length) := by
  have evaluator := budget_comp_linear CoefficientTransitionSpace.advance_inSpace
    (budget_prod modulus_inSpace (budget_prod count_inSpace
      (budget_prod (fst' currentFactor_inSpace)
        (budget_prod (snd' currentFactor_inSpace) evaluator_inSpace))))
  exact assembleState modulus_inSpace count_inSpace node_inSpace order_inSpace evaluator

theorem halted_inSpace :
    ComputableInSpace halted encState encBool (fun s => (encState s).length) := by
  have computed := budget_comp_linear CoefficientTransitionSpace.halted_inSpace evaluator_inSpace
  exact computed

theorem output_inSpace :
    ComputableInSpace output encState encNat (fun s => (encState s).length) := by
  have computed := budget_comp_linear (of_inO (ComputableInDegree.getD (enc₁ := encNat) 0).inO_one)
    result_inSpace
  exact computed

end NtimeDspace.HermiteCoefficientSpace
