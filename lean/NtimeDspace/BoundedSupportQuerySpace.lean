import NtimeDspace.BoundedSupportQuery
import NtimeDspace.BoundedGammaQuerySpace

/-!
Global machine certificates for the support reader's bootstrap and callbacks.
Only the `(bound,capacity)` header is projected. The original support bit word
remains on the read-only input tape through every codeword and validation step.
-/

namespace NtimeDspace.BoundedSupportQuerySpace

open Turing Turing.MultiTapeTM ComputableInSpace BoundedSupportQuery

abbrev encRead := encPair encState (encOption encBool)

private theorem stateData_inSpace :
    ComputableInSpace stateData encState encStateData (fun s => (encState s).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem bound_inSpace :
    ComputableInSpace State.bound encState encNat (fun s => (encState s).length) :=
  fst' stateData_inSpace

private theorem capacity_inSpace :
    ComputableInSpace State.capacity encState encNat (fun s => (encState s).length) :=
  fst' (snd' stateData_inSpace)

private theorem offset_inSpace :
    ComputableInSpace State.payloadOffset encState encNat (fun s => (encState s).length) :=
  fst' (snd' (snd' stateData_inSpace))

private theorem parser_inSpace :
    ComputableInSpace State.parser encState BoundedSupportPayloadSpace.encState
      (fun s => (encState s).length) := snd' (snd' (snd' stateData_inSpace))

private theorem assemble {α : Type} {encIn : α ↪ List Bool} {B : α → ℕ}
    {bound capacity offset : α → ℕ} {parser : α → BoundedSupportPayload.State}
    (hb : ComputableInSpace bound encIn encNat B)
    (hc : ComputableInSpace capacity encIn encNat B)
    (ho : ComputableInSpace offset encIn encNat B)
    (hp : ComputableInSpace parser encIn BoundedSupportPayloadSpace.encState B) :
    ComputableInSpace (fun x => (⟨bound x, capacity x, offset x, parser x⟩ : State))
      encIn encState B :=
  (budget_prod hb (budget_prod hc (budget_prod ho hp))).of_enc_eq fun _ => rfl

/-- The same two-number header codec is used by the bounded gamma client. -/
theorem payloadOffset_inSpace :
    ComputableInSpace payloadOffset encHeader encNat (fun h => (encHeader h).length) :=
  BoundedGammaQuerySpace.payloadOffset_inSpace

theorem initialHeader_inSpace :
    ComputableInSpace initialHeader encHeader encState (fun h => (encHeader h).length) := by
  have initialized := budget_comp_linear BoundedSupportPayloadSpace.initial_inSpace
    (fst encNat encNat)
  exact assemble (fst _ _) (snd _ _) payloadOffset_inSpace initialized

/-- Header-only initialization: no payload projection or copied suffix. -/
theorem initial_inSpace :
    ComputableInSpace initial encPacket encState (fun packet => (encHeader packet.1).length) := by
  have computed := budget_comp_linear initialHeader_inSpace
    (SmallHeaderProjection.project_inSpace encHeader encBits)
  exact computed

theorem query_inSpace :
    ComputableInSpace machine.query encState encNat (fun s => (encState s).length) := by
  have cursor := budget_comp_linear BoundedSupportPayloadSpace.query_inSpace parser_inSpace
  exact budget_natAdd offset_inSpace cursor

private theorem stateRead_inSpace :
    ComputableInSpace (fun argument : State × Option Bool => argument.1) encRead encState
      (fun argument => (encRead argument).length) := fst _ _

private theorem bitRead_inSpace :
    ComputableInSpace (fun argument : State × Option Bool => argument.2) encRead (encOption encBool)
      (fun argument => (encRead argument).length) := snd _ _

theorem next_inSpace :
    ComputableInSpace machine.next encRead encState (fun argument => (encRead argument).length) := by
  have bound := budget_comp_linear bound_inSpace stateRead_inSpace
  have capacity := budget_comp_linear capacity_inSpace stateRead_inSpace
  have offset := budget_comp_linear offset_inSpace stateRead_inSpace
  have parser := budget_comp_linear parser_inSpace stateRead_inSpace
  have advanced := budget_comp_linear BoundedSupportPayloadSpace.next_inSpace
    (budget_prod bound (budget_prod capacity (budget_prod parser bitRead_inSpace)))
  exact assemble bound capacity offset advanced

theorem emit_inSpace :
    ComputableInSpace machine.emit encRead encBits (fun argument => (encRead argument).length) :=
  budget_const [] (.refl _)

theorem halted_inSpace :
    ComputableInSpace machine.halted encState encBool (fun s => (encState s).length) := by
  have computed := budget_comp_linear BoundedSupportPayloadSpace.halted_inSpace parser_inSpace
  exact computed

theorem output_inSpace :
    ComputableInSpace output encState encOutput (fun s => (encState s).length) := by
  have computed := budget_comp_linear BoundedSupportPayloadSpace.output_inSpace parser_inSpace
  exact computed

theorem finish_inSpace :
    ComputableInSpace machine.finish encState encBits (fun s => (encState s).length) := by
  have encode : ComputableInSpace (fun value => encOutput value) encOutput encBits
      (fun value => (encOutput value).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  have computed := budget_comp_linear encode output_inSpace
  exact computed

end NtimeDspace.BoundedSupportQuerySpace
