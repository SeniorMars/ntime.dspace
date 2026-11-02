import NtimeDspace.BoundedSupportParser

/-!
# The bounded support parser as a bit-step machine

`BoundedSupportParser.scan` consumes gamma codewords recursively. A loop
program reads its input one bit at a time, so here the same parser is a state
machine with one transition per bit: ready for a codeword, inside the zero
prefix, inside the payload, or failed. `scan_eq_fold` says that finalizing the
left fold of the transition over the input is exactly `scan`.
-/

namespace NtimeDspace.ParserFold

open BoundedSupportParser

variable {bound capacity : ℕ}

/-- Parser states between bits. -/
inductive State (bound capacity : ℕ) where
  | fail
  | ready (regs : Registers bound capacity)
  | prefixZ (regs : Registers bound capacity) (zeros : Fin (bound.log2 + 1))
  | payload (regs : Registers bound capacity) (remaining : Fin (bound.log2 + 1))
      (acc : Fin (bound + 1))

/-- Accept a completed gap. -/
def finish (query : Fin (bound + 1)) (regs : Registers bound capacity) (gap : Fin (bound + 1)) :
    State bound capacity :=
  if positive : 0 < gap.val then
    if fits : gap.val ≤ bound - regs.cumulative.val then
      if room : regs.rank.val < capacity then
        .ready { cumulative := ⟨regs.cumulative.val + gap.val, by
                  have h := regs.cumulative.isLt
                  omega⟩
                 rank := ⟨regs.rank.val + 1, by omega⟩
                 found := regs.found || decide (regs.cumulative.val + gap.val = query.val) }
      else .fail
    else .fail
  else .fail

/-- One payload bit. -/
def payloadStep (query : Fin (bound + 1)) (regs : Registers bound capacity)
    (remaining : Fin (bound.log2 + 1)) (acc : Fin (bound + 1)) (bit : Bool) :
    State bound capacity :=
  match appendBit bound acc bit with
  | none => .fail
  | some next =>
    if last : remaining.val - 1 = 0 then finish query regs next
    else .payload regs ⟨remaining.val - 1, by omega⟩ next

/-- One prefix bit. -/
def prefixStep (query : Fin (bound + 1)) (regs : Registers bound capacity)
    (zeros : Fin (bound.log2 + 1)) : Bool → State bound capacity
  | false => if room : zeros.val < bound.log2 then .prefixZ regs ⟨zeros.val + 1, by omega⟩
      else .fail
  | true => if positive : 0 < bound then
      (if empty : zeros.val = 0 then finish query regs ⟨1, by omega⟩
        else .payload regs zeros ⟨1, by omega⟩)
      else .fail

/-- The transition on one bit. -/
def step (query : Fin (bound + 1)) : State bound capacity → Bool → State bound capacity
  | .fail, _ => .fail
  | .ready regs, bit =>
      if regs.rank.val < capacity then prefixStep query regs ⟨0, by omega⟩ bit else .fail
  | .prefixZ regs zeros, bit => prefixStep query regs zeros bit
  | .payload regs remaining acc, bit => payloadStep query regs remaining acc bit

/-- The result at the end of the input. -/
def finalize : State bound capacity → Option (Registers bound capacity)
  | .ready regs => some regs
  | _ => none

theorem foldl_fail (query : Fin (bound + 1)) (input : List Bool) :
    input.foldl (step (capacity := capacity) query) .fail = .fail := by
  induction input with
  | nil => rfl
  | cons b bs ih => simpa [List.foldl, step] using ih

variable (query : Fin (bound + 1))

theorem foldl_append_eq (s : State bound capacity) (consumed rest : List Bool) :
    (consumed ++ rest).foldl (step query) s = rest.foldl (step query) (consumed.foldl (step query) s) :=
  List.foldl_append

/-- The payload phase: success reaches `finish` after a consumed prefix; failure
is final. -/
theorem payload_fold (regs : Registers bound capacity) :
    ∀ (input : List Bool) (remaining : Fin (bound.log2 + 1)) (acc : Fin (bound + 1)),
      0 < remaining.val →
      (∀ gap rest, readPayload bound remaining acc input = some (gap, rest) →
        ∃ consumed, input = consumed ++ rest ∧ consumed ≠ [] ∧
          consumed.foldl (step query) (.payload regs remaining acc) = finish query regs gap) ∧
      (readPayload bound remaining acc input = none →
        finalize (input.foldl (step query) (.payload regs remaining acc)) = none) := by
  intro input
  induction input with
  | nil =>
    intro remaining acc hpos
    refine ⟨fun gap rest h => ?_, fun _ => rfl⟩
    rw [readPayload.eq_def] at h
    simp only [show remaining.val ≠ 0 by omega, ↓reduceDIte] at h
    exact absurd h (by simp)
  | cons bit rest ih =>
    intro remaining acc hpos
    have hunfold : readPayload bound remaining acc (bit :: rest) =
        match appendBit bound acc bit with
        | none => none
        | some next => readPayload bound ⟨remaining.val - 1, by omega⟩ next rest := by
      rw [readPayload.eq_def]
      simp only [show remaining.val ≠ 0 by omega, ↓reduceDIte]
      rfl
    rcases happ : appendBit bound acc bit with _ | next
    · simp only [hunfold, happ]
      refine ⟨fun gap rest' h => absurd h (by simp), fun _ => ?_⟩
      simp [List.foldl, step, payloadStep, happ, foldl_fail, finalize]
    · simp only [hunfold, happ]
      by_cases hlast : remaining.val - 1 = 0
      · have hdone : readPayload bound ⟨remaining.val - 1, by omega⟩ next rest = some (next, rest) := by
          rw [readPayload.eq_def]
          simp [hlast]
        rw [hdone]
        refine ⟨fun gap rest' h => ?_, fun h => absurd h (by simp)⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[bit], rfl, by simp, ?_⟩
        simp [List.foldl, step, payloadStep, happ, hlast]
      · obtain ⟨hs, hn⟩ := ih ⟨remaining.val - 1, by omega⟩ next (by simp; omega)
        have hstep : step query (.payload regs remaining acc) bit =
            .payload regs ⟨remaining.val - 1, by omega⟩ next := by
          simp [step, payloadStep, happ, hlast]
        refine ⟨fun gap rest' h => ?_, fun h => ?_⟩
        · obtain ⟨consumed, hrest, -, hfold⟩ := hs gap rest' h
          refine ⟨bit :: consumed, by simp [hrest], by simp, ?_⟩
          rw [List.foldl_cons, hstep, hfold]
        · rw [List.foldl_cons, hstep]
          exact hn h

/-- The prefix phase. -/
theorem prefix_fold (regs : Registers bound capacity) :
    ∀ (input : List Bool) (zeros : Fin (bound.log2 + 1)),
      (∀ gap rest, readPrefix bound zeros input = some (gap, rest) →
        ∃ consumed, input = consumed ++ rest ∧ consumed ≠ [] ∧
          consumed.foldl (step query) (.prefixZ regs zeros) = finish query regs gap) ∧
      (readPrefix bound zeros input = none →
        finalize (input.foldl (step query) (.prefixZ regs zeros)) = none) := by
  intro input
  induction input with
  | nil =>
    intro zeros
    exact ⟨fun gap rest h => absurd h (by simp [readPrefix]), fun _ => rfl⟩
  | cons bit rest ih =>
    intro zeros
    cases bit with
    | false =>
      by_cases room : zeros.val < bound.log2
      · have hr : readPrefix bound zeros (false :: rest) =
            readPrefix bound ⟨zeros.val + 1, by omega⟩ rest := by
          simp [readPrefix, room]
        have hstep : step query (.prefixZ regs zeros) false =
            .prefixZ regs ⟨zeros.val + 1, by omega⟩ := by
          simp [step, prefixStep, room]
        obtain ⟨hs, hn⟩ := ih ⟨zeros.val + 1, by omega⟩
        rw [hr]
        refine ⟨fun gap rest' h => ?_, fun h => ?_⟩
        · obtain ⟨consumed, hrest, -, hfold⟩ := hs gap rest' h
          exact ⟨false :: consumed, by simp [hrest], by simp, by rw [List.foldl_cons, hstep, hfold]⟩
        · rw [List.foldl_cons, hstep]; exact hn h
      · have hr : readPrefix bound zeros (false :: rest) = none := by simp [readPrefix, room]
        rw [hr]
        refine ⟨fun gap rest' h => absurd h (by simp), fun _ => ?_⟩
        simp [List.foldl, step, prefixStep, room, foldl_fail, finalize]
    | true =>
      by_cases positive : 0 < bound
      · have hr : readPrefix bound zeros (true :: rest) =
            readPayload bound zeros ⟨1, by omega⟩ rest := by
          simp [readPrefix, positive]
        rw [hr]
        by_cases empty : zeros.val = 0
        · have hdone : readPayload bound zeros ⟨1, by omega⟩ rest = some (⟨1, by omega⟩, rest) := by
            rw [readPayload.eq_def]; simp [empty]
          rw [hdone]
          refine ⟨fun gap rest' h => ?_, fun h => absurd h (by simp)⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨[true], rfl, by simp, by simp [List.foldl, step, prefixStep, positive, empty]⟩
        · have hstep : step query (.prefixZ regs zeros) true = .payload regs zeros ⟨1, by omega⟩ := by
            simp [step, prefixStep, positive, empty]
          obtain ⟨hs, hn⟩ := payload_fold query regs rest zeros ⟨1, by omega⟩ (by omega)
          refine ⟨fun gap rest' h => ?_, fun h => ?_⟩
          · obtain ⟨consumed, hrest, -, hfold⟩ := hs gap rest' h
            exact ⟨true :: consumed, by simp [hrest], by simp,
              by rw [List.foldl_cons, hstep, hfold]⟩
          · rw [List.foldl_cons, hstep]; exact hn h
      · have hr : readPrefix bound zeros (true :: rest) = none := by simp [readPrefix, positive]
        rw [hr]
        refine ⟨fun gap rest' h => absurd h (by simp), fun _ => ?_⟩
        simp [List.foldl, step, prefixStep, positive, foldl_fail, finalize]

/-- **The parser is a left fold of the bit transition.** -/
theorem scan_eq_fold (regs : Registers bound capacity) (input : List Bool) :
    finalize (input.foldl (step query) (.ready regs)) = scan bound capacity query regs input := by
  induction h : input.length using Nat.strong_induction_on generalizing regs input with
  | _ len ih =>
    rcases input with _ | ⟨bit, bits⟩
    · rw [scan]; simp [finalize]
    · rw [scan, dif_neg (by simp)]
      by_cases room : regs.rank.val < capacity
      · rw [dif_pos room]
        have hready : (bit :: bits).foldl (step query) (.ready regs) =
            (bit :: bits).foldl (step query) (.prefixZ regs ⟨0, by omega⟩) := by
          simp [List.foldl, step, room]
        rw [hready]
        obtain ⟨hs, hn⟩ := prefix_fold query regs (bit :: bits) ⟨0, by omega⟩
        rcases hg : gamma bound (bit :: bits) with _ | ⟨gap, rest⟩
        · exact hn hg
        · obtain ⟨consumed, hrest, hne, hfold⟩ := hs gap rest hg
          rw [hrest, List.foldl_append, hfold]
          simp only
          have hlen : rest.length < len := by
            rw [← h, hrest, List.length_append]
            have : 0 < consumed.length := List.length_pos_of_ne_nil hne
            omega
          unfold finish
          by_cases hpos : 0 < gap.val
          · rw [dif_pos hpos, dif_pos hpos]
            by_cases hfits : gap.val ≤ bound - regs.cumulative.val
            · rw [dif_pos hfits, dif_pos hfits, dif_pos room]
              exact ih rest.length hlen _ rest rfl
            · rw [dif_neg hfits, dif_neg hfits, foldl_fail]; rfl
          · rw [dif_neg hpos, dif_neg hpos, foldl_fail]; rfl
      · rw [dif_neg room]
        simp [List.foldl, step, room, foldl_fail, finalize]

end NtimeDspace.ParserFold
