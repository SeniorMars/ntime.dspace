import NtimeDspace.CoefficientTransition

/-!
# Global work-space certificates for coefficient-stack control

Each certificate applies to every encoded raw state, including malformed
requests, empty stacks, and unreduced natural residues. The field modulus and
current factor are explicit input data. Fetching that factor and bounding a
complete run's encoded state remain separate obligations.
-/

namespace NtimeDspace.CoefficientTransitionSpace

open Turing Turing.MultiTapeTM ComputableInSpace
open CoefficientStackEncoding CoefficientTransition

private abbrev encRequestData :=
  encPair encNat (encPair encNat (encPair encNat encNat))

private abbrev encContinuationData := encPair encNat (encPair encNat (encPair encNat
  (encPair encNat (encPair encNat (encPair encNat (encOption encNat))))))

private abbrev encStateData :=
  encPair encRequest (encPair (encOption encNat) (encList encContinuation))

private theorem requestData_inSpace :
    ComputableInSpace requestData encRequest encRequestData
      (fun r => (encRequest r).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem continuationData_inSpace :
    ComputableInSpace continuationData encContinuation encContinuationData
      (fun r => (encContinuation r).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem stateData_inSpace :
    ComputableInSpace stateData encState encStateData
      (fun s => (encState s).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

section Constructors

variable {α : Type} {encIn : α ↪ List Bool} {B : α → ℕ}

private theorem assembleRequest {height start degree span : α → ℕ}
    (hh : ComputableInSpace height encIn encNat B)
    (hs : ComputableInSpace start encIn encNat B)
    (hd : ComputableInSpace degree encIn encNat B)
    (hw : ComputableInSpace span encIn encNat B) :
    ComputableInSpace (fun x => (⟨height x, start x, degree x, span x⟩ : RawRequest))
      encIn encRequest B :=
  (budget_prod hh (budget_prod hs (budget_prod hd hw))).of_enc_eq fun _ => rfl

private theorem assembleContinuation {height start degree split span accumulator : α → ℕ}
    {savedLeft : α → Option ℕ}
    (hh : ComputableInSpace height encIn encNat B)
    (hs : ComputableInSpace start encIn encNat B)
    (hd : ComputableInSpace degree encIn encNat B)
    (hk : ComputableInSpace split encIn encNat B)
    (hw : ComputableInSpace span encIn encNat B)
    (ha : ComputableInSpace accumulator encIn encNat B)
    (hl : ComputableInSpace savedLeft encIn (encOption encNat) B) :
    ComputableInSpace (fun x =>
      (⟨height x, start x, degree x, split x, span x, accumulator x, savedLeft x⟩ :
        RawContinuation)) encIn encContinuation B :=
  (budget_prod hh (budget_prod hs (budget_prod hd
    (budget_prod hk (budget_prod hw (budget_prod ha hl)))))).of_enc_eq fun _ => rfl

private theorem assembleState {request : α → RawRequest} {result : α → Option ℕ}
    {stack : α → List RawContinuation}
    (hr : ComputableInSpace request encIn encRequest B)
    (hv : ComputableInSpace result encIn (encOption encNat) B)
    (hs : ComputableInSpace stack encIn (encList encContinuation) B) :
    ComputableInSpace (fun x => (⟨request x, result x, stack x⟩ : RawState))
      encIn encState B :=
  (budget_prod hr (budget_prod hv hs)).of_enc_eq fun _ => rfl

private theorem optionIsSome {value : α → Option ℕ}
    (h : ComputableInSpace value encIn (encOption encNat) B) :
    ComputableInSpace (fun x => (value x).isSome) encIn encBool B :=
  budget_comp_linear (of_inO (ComputableInDegree.isSome encNat).inO_one) h

private theorem optionGetD {value : α → Option ℕ}
    (h : ComputableInSpace value encIn (encOption encNat) B) :
    ComputableInSpace (fun x => (value x).getD 0) encIn encNat B :=
  budget_comp_linear (of_inO (ComputableInDegree.getD (enc₁ := encNat) 0).inO_one) h

end Constructors

theorem parent_inSpace :
    ComputableInSpace parent encContinuation encRequest
      (fun frame => (encContinuation frame).length) := by
  have fields := continuationData_inSpace
  have height := fst' fields
  have start := fst' (snd' fields)
  have degree := fst' (snd' (snd' fields))
  have span := fst' (snd' (snd' (snd' (snd' fields))))
  exact assembleRequest (budget_natSucc height) start degree
    (budget_natMul (budget_const (encB := encNat) 2 (.refl _)) span)

theorem child_inSpace :
    ComputableInSpace child encContinuation encRequest
      (fun frame => (encContinuation frame).length) := by
  have fields := continuationData_inSpace
  have height := fst' fields
  have start := fst' (snd' fields)
  have degree := fst' (snd' (snd' fields))
  have split := fst' (snd' (snd' (snd' fields)))
  have span := fst' (snd' (snd' (snd' (snd' fields))))
  have saved := snd' (snd' (snd' (snd' (snd' (snd' fields)))))
  exact budget_ite (optionIsSome saved)
    (assembleRequest height (budget_natAdd start span) (budget_natSub degree split) span)
    (assembleRequest height start split span)

theorem descend_inSpace :
    ComputableInSpace descend encState encState (fun s => (encState s).length) := by
  have fields := stateData_inSpace
  have request := budget_comp_linear requestData_inSpace (fst' fields)
  have height := fst' request
  have start := fst' (snd' request)
  have degree := fst' (snd' (snd' request))
  have span := snd' (snd' (snd' request))
  have frame := assembleContinuation (budget_natPred height) start degree degree
    (budget_natDiv span (budget_const (encB := encNat) 2 (.refl _)))
    (budget_const (encB := encNat) 0 (.refl _))
    (budget_const (encB := encOption encNat) none (.refl _))
  exact assembleState (budget_comp_linear child_inSpace frame)
    (budget_const (encB := encOption encNat) none (.refl _))
    (budget_cons frame (snd' (snd' fields)))

theorem saveLeft_inSpace :
    ComputableInSpace saveLeft encState encState (fun s => (encState s).length) := by
  have fields := stateData_inSpace
  have result := fst' (snd' fields)
  have stack := snd' (snd' fields)
  have top := budget_comp_linear continuationData_inSpace (budget_headD defaultFrame stack)
  have frame := assembleContinuation (fst' top) (fst' (snd' top)) (fst' (snd' (snd' top)))
    (fst' (snd' (snd' (snd' top)))) (fst' (snd' (snd' (snd' (snd' top)))))
    (fst' (snd' (snd' (snd' (snd' (snd' top)))))) result
  exact assembleState (budget_comp_linear child_inSpace frame)
    (budget_const (encB := encOption encNat) none (.refl _))
    (budget_cons frame (budget_tail stack))

abbrev CombineInput := ℕ × RawState

def encCombineInput : CombineInput ↪ List Bool := encPair encNat encState

theorem combine_inSpace :
    ComputableInSpace (fun input : CombineInput => combine input.1 input.2)
      encCombineInput encState (fun input => (encCombineInput input).length) := by
  have modulus : ComputableInSpace (fun input : CombineInput => input.1)
      encCombineInput encNat (fun input => (encCombineInput input).length) := fst _ _
  have state : ComputableInSpace (fun input : CombineInput => input.2)
      encCombineInput encState (fun input => (encCombineInput input).length) := snd _ _
  have fields := budget_comp_linear stateData_inSpace state
  have result := fst' (snd' fields)
  have stack := snd' (snd' fields)
  have frame := budget_headD defaultFrame stack
  have top := budget_comp_linear continuationData_inSpace frame
  have height := fst' top
  have start := fst' (snd' top)
  have degree := fst' (snd' (snd' top))
  have split := fst' (snd' (snd' (snd' top)))
  have span := fst' (snd' (snd' (snd' (snd' top))))
  have accumulator := fst' (snd' (snd' (snd' (snd' (snd' top)))))
  have saved := snd' (snd' (snd' (snd' (snd' (snd' top)))))
  have product := budget_comp_linear ResidueArithmetic.mul_inSpace
    (budget_prod modulus (budget_prod (optionGetD saved) (optionGetD result)))
  have accumulated := budget_comp_linear ResidueArithmetic.add_inSpace
    (budget_prod modulus (budget_prod product accumulator))
  have returned := assembleState (budget_comp_linear parent_inSpace frame)
    (budget_optionSome accumulated) (budget_tail stack)
  have next := assembleContinuation height start degree (budget_natPred split) span accumulated
    (budget_const (encB := encOption encNat) none (.refl _))
  have resumed := assembleState (budget_comp_linear child_inSpace next)
    (budget_const (encB := encOption encNat) none (.refl _))
    (budget_cons next (budget_tail stack))
  apply (budget_ite (budget_natIsZero split) returned resumed).of_enc_eq
  intro input
  simp only [combine, decide_eq_true_eq]
  rfl

private theorem inputFields_inSpace :
    ComputableInSpace (fun input : Input => input) encInput encInput
      (fun input => (encInput input).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem modulus_inSpace :
    ComputableInSpace modulus encInput encNat (fun input => (encInput input).length) :=
  fst' inputFields_inSpace

private theorem count_inSpace :
    ComputableInSpace count encInput encNat (fun input => (encInput input).length) :=
  fst' (snd' inputFields_inSpace)

private theorem factorValue_inSpace :
    ComputableInSpace factorValue encInput encNat (fun input => (encInput input).length) :=
  fst' (snd' (snd' inputFields_inSpace))

private theorem factorMultiplicity_inSpace :
    ComputableInSpace factorMultiplicity encInput encNat (fun input => (encInput input).length) :=
  fst' (snd' (snd' (snd' inputFields_inSpace)))

theorem state_inSpace :
    ComputableInSpace state encInput encState (fun input => (encInput input).length) :=
  snd' (snd' (snd' (snd' inputFields_inSpace)))

theorem leaf_inSpace :
    ComputableInSpace leaf encInput encNat (fun input => (encInput input).length) := by
  have fields := budget_comp_linear stateData_inSpace state_inSpace
  have request := budget_comp_linear requestData_inSpace (fst' fields)
  have start := fst' (snd' request)
  have degree := fst' (snd' (snd' request))
  have computed := budget_comp_linear ReciprocalLeafSpace.reciprocal_inSpace
    (budget_prod modulus_inSpace (budget_prod factorValue_inSpace
      (budget_prod factorMultiplicity_inSpace degree)))
  have padding := budget_ite (budget_natIsZero degree)
    (budget_natMod (budget_const (encB := encNat) 1 (.refl _)) modulus_inSpace)
    (budget_const (encB := encNat) 0 (.refl _))
  apply (budget_ite (budget_natLt start count_inSpace) computed padding).of_enc_eq
  intro input
  simp only [leaf, decide_eq_true_eq]
  rfl

/-- One actual machine handles every encoded transition input. No field or
factor-access callback, canonical-state premise, or reachability bound is
assumed by this certificate. -/
theorem advance_inSpace :
    ComputableInSpace advance encInput encState (fun input => (encInput input).length) := by
  have fields := budget_comp_linear stateData_inSpace state_inSpace
  have request := fst' fields
  have requestFields := budget_comp_linear requestData_inSpace request
  have result := fst' (snd' fields)
  have stack := snd' (snd' fields)
  have top := budget_comp_linear continuationData_inSpace (budget_headD defaultFrame stack)
  have saved := snd' (snd' (snd' (snd' (snd' (snd' top)))))
  have combined := budget_comp_linear combine_inSpace (budget_prod modulus_inSpace state_inSpace)
  have savedLeft := budget_comp_linear saveLeft_inSpace state_inSpace
  have popped := budget_ite (budget_isEmpty stack) state_inSpace
    (budget_ite (optionIsSome saved) combined savedLeft)
  have returned := assembleState request (budget_optionSome leaf_inSpace) stack
  have descended := budget_comp_linear descend_inSpace state_inSpace
  have entered := budget_ite (budget_natIsZero (fst' requestFields)) returned descended
  apply (budget_ite (optionIsSome result) popped entered).of_enc_eq
  intro input
  simp only [advance, decide_eq_true_eq]
  rfl

theorem halted_inSpace :
    ComputableInSpace halted encState encBool (fun s => (encState s).length) := by
  have fields := stateData_inSpace
  have hasResult := optionIsSome (fst' (snd' fields))
  have empty := budget_isEmpty (snd' (snd' fields))
  exact budget_finite (encC := encBool) (fun pair : Bool × Bool => pair.1 && pair.2)
    (budget_prod hasResult empty)

end NtimeDspace.CoefficientTransitionSpace
