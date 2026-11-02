import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
The first framed component can be projected without retaining its following
payload. The actual finite-state transducer emits only the header, scans the
remaining read-only input without emitting it, then rewinds its input head.
Its work-tape usage is zero. The `ComputableInSpace` certificate additionally
charges the emitted header, so its budget depends only on that header's size.

For two numeric parameters, place the pair together in the first component:
`encPair (encPair encNat encNat) encBits` on `((bound, start), payload)`.
The frame's length is the payload offset; no payload word is projected or
copied by these certificates. Input-query compilation is separate.
-/

namespace NtimeDspace.SmallHeaderProjection

open Turing Turing.MultiTapeTM Internal.FrameMachines

universe u

/-- The same zero-work-tape machine works for every header and payload value.
Its time includes scanning the payload and rewinding the read-only input. -/
theorem project_tidily {Header Payload : Type u}
    (encHeader : Header ↪ List Bool) (encPayload : Payload ↪ List Bool) :
    ComputableTidilyInTimeAndSpace Prod.fst (encPair encHeader encPayload) encHeader
      (fun pair => 4 * (encPair encHeader encPayload pair).length + 8) (fun _ => 0) := by
  apply (readFrameT true).computableTidilyInTimeAndSpace
  intro pair
  rw [show (readFrameT true).q₀ = FrameState.marker by rfl, readFrameT_run_true]
  simp

/-- Small-output projection: the payload length is absent from the workspace
budget, while the complete emitted header is explicitly charged. -/
theorem project_inSpace {Header Payload : Type u}
    (encHeader : Header ↪ List Bool) (encPayload : Payload ↪ List Bool) :
    ComputableInSpace Prod.fst (encPair encHeader encPayload) encHeader
      (fun pair => (encHeader pair.1).length) := by
  refine ⟨_, 1, (project_tidily encHeader encPayload).computableInTimeAndSpace.mono
    (fun _ => le_rfl) (fun _ => Nat.zero_le _), ?_⟩
  intro pair
  simp

/-- The small-header projection is available to an initializer that requires
tidy callbacks, retaining the same output-size budget. -/
theorem project_tidilyInSpace {Header Payload : Type u}
    (encHeader : Header ↪ List Bool) (encPayload : Payload ↪ List Bool) :
    ComputableTidilyInSpace Prod.fst (encPair encHeader encPayload) encHeader
      (fun pair => (encHeader pair.1).length) :=
  (project_inSpace encHeader encPayload).tidy

/-- Exact size of the two-parameter header before its outer framing. -/
theorem pairHeader_length (bound start : ℕ) :
    (encPair encNat encNat (bound, start)).length =
      2 * (encNat bound).length + (encNat start).length + 1 := by
  simp only [length_encPair]
  omega

theorem pairHeader_length_le (bound start : ℕ) :
    (encPair encNat encNat (bound, start)).length ≤
      2 * (bound.log2 + 1) + (start.log2 + 1) + 1 := by
  have first := length_encNat_le_log2 (Nat.le_refl bound)
  have second := length_encNat_le_log2 (Nat.le_refl start)
  rw [pairHeader_length]
  omega

/-- Exact read-only input offset of the payload in the selected packet format. -/
theorem pairHeader_frame_length (bound start : ℕ) :
    (frame (encPair encNat encNat (bound, start))).length =
      4 * (encNat bound).length + 2 * (encNat start).length + 3 := by
  rw [length_frame, pairHeader_length]
  omega

/-- Two runtime natural parameters are extracted together without projecting
or storing the trailing payload. This statement includes zero-valued headers. -/
theorem pairHeader_inSpace {Payload : Type}
    (encPayload : Payload ↪ List Bool) :
    ComputableInSpace Prod.fst (encPair (encPair encNat encNat) encPayload)
      (encPair encNat encNat)
      (fun pair => 2 * (pair.1.1.log2 + 1) + (pair.1.2.log2 + 1) + 1) :=
  (project_inSpace (encPair encNat encNat) encPayload).mono_le
    (fun pair => pairHeader_length_le pair.1.1 pair.1.2)

end NtimeDspace.SmallHeaderProjection
