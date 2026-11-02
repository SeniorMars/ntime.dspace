import NtimeDspace.BoundedSupportParser

/-!
Cardinality does not depend on the auxiliary membership flag retained by the
bounded support scan. This lets a cursor-only cardinality machine reuse the
existing full-validation specification without storing that unused flag.
-/

namespace NtimeDspace.SupportScanSemantics

open BoundedSupportParser

theorem scan_rank_found (bound capacity : ℕ) (query : Fin (bound + 1))
    (state : Registers bound capacity) (flag : Bool) (input : List Bool) :
    (scan bound capacity query { state with found := flag } input).map
        (fun result => result.rank.val) =
      (scan bound capacity query state input).map (fun result => result.rank.val) := by
  conv_lhs => rw [scan]
  conv_rhs => rw [scan]
  dsimp only
  split_ifs with finished room
  · rfl
  · cases parsed : gamma bound input with
    | none => rfl
    | some pair =>
      rcases pair with ⟨gap, rest⟩
      simp only
      split_ifs with positive fits
      · exact scan_rank_found bound capacity query
          { cumulative := ⟨state.cumulative.val + gap.val, by
              have := state.cumulative.isLt
              omega⟩
            rank := ⟨state.rank.val + 1, by omega⟩
            found := state.found || decide (state.cumulative.val + gap.val = query.val) }
          (flag || decide (state.cumulative.val + gap.val = query.val)) rest
      · rfl
      · rfl
  · rfl
termination_by capacity - state.rank.val
decreasing_by omega

end NtimeDspace.SupportScanSemantics
