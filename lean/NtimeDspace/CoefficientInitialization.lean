import NtimeDspace.ModularPowerSpace
import NtimeDspace.CoefficientStackEncoding

/-!
# Uniform construction of a coefficient interval

Starting with `(count-1, 0, 1)`, each active transition halves the remaining
counter, increments the height, and doubles the stored span. The executing
definitions never exponentiate an input height. Iterating `count` times is a
simple sufficient driver; the state stops changing once the counter is zero.
The global space certificate charges the encoded iteration counter as well as
the three registers. It makes no polynomial-time claim.
-/

namespace NtimeDspace.CoefficientInitialization

open Turing Turing.MultiTapeTM ComputableInSpace

/-- Register order: remaining counter, height, span. -/
abbrev State := ℕ × ℕ × ℕ

abbrev encRegisters : State ↪ List Bool := ModularPowerSpace.encTriple

def seed (count : ℕ) : State := (count - 1, 0, 1)

def step (state : State) : State :=
  if state.1 = 0 then state else (state.1 / 2, state.2.1 + 1, 2 * state.2.2)

def initialRegisters (count : ℕ) : State := step^[count] (seed count)

def height (count : ℕ) : ℕ := (initialRegisters count).2.1
def span (count : ℕ) : ℕ := (initialRegisters count).2.2

def request (count start degree : ℕ) : CoefficientStackEncoding.RawRequest :=
  ⟨height count, start, degree, span count⟩

/-- The two adjacent-product inequalities locate `count-1` within the current
span. They support both endpoint correctness and global register bounds. -/
def Invariant (count : ℕ) (state : State) : Prop :=
  state.2.2 = 2 ^ state.2.1 ∧ state.2.1 + state.1 ≤ count - 1 ∧
    state.2.2 * state.1 ≤ count - 1 ∧ count - 1 < state.2.2 * (state.1 + 1) ∧
    state.2.2 ≤ 2 * max 1 count ∧ state.2.1 ≤ Nat.clog 2 count

theorem seed_invariant (count : ℕ) : Invariant count (seed count) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, Nat.zero_le _⟩
  · change 0 + (count - 1) ≤ count - 1
    omega
  · change 1 * (count - 1) ≤ count - 1
    omega
  · change count - 1 < 1 * (count - 1 + 1)
    omega
  · change 1 ≤ 2 * max 1 count
    have positive : 1 ≤ max 1 count := le_max_left _ _
    omega

theorem step_invariant (count : ℕ) (state : State) (valid : Invariant count state) :
    Invariant count (step state) := by
  by_cases done : state.1 = 0
  · simpa [step, done] using valid
  · obtain ⟨power, combined, lower, upper, spanBound, heightBound⟩ := valid
    have positive : 0 < state.1 := Nat.pos_of_ne_zero done
    have halfLower : 2 * (state.1 / 2) ≤ state.1 := by omega
    have halfUpper : state.1 + 1 ≤ 2 * (state.1 / 2 + 1) := by omega
    have oldSpan : state.2.2 ≤ count - 1 :=
      (Nat.le_mul_of_pos_right _ positive).trans lower
    have strictPower : 2 ^ state.2.1 < count := by rw [← power]; omega
    have nextHeight : state.2.1 < Nat.clog 2 count :=
      (Nat.lt_clog_iff_pow_lt (by decide)).mpr strictPower
    dsimp [step]
    rw [ite_eq_right done]
    dsimp [Invariant]
    refine ⟨?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [power, pow_succ]
      omega
    · omega
    · nlinarith
    · nlinarith
    · have countBound : count ≤ max 1 count := le_max_right _ _
      omega

theorem iterate_invariant (count iterations : ℕ) :
    Invariant count (step^[iterations] (seed count)) := by
  induction iterations with
  | zero => exact seed_invariant count
  | succ iterations ih =>
    rw [Function.iterate_succ_apply']
    exact step_invariant count _ ih

theorem remaining_le (count iterations : ℕ) :
    (step^[iterations] (seed count)).1 ≤ count - 1 - iterations := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply']
    change (if (step^[iterations] (seed count)).1 = 0 then step^[iterations] (seed count)
      else ((step^[iterations] (seed count)).1 / 2,
        (step^[iterations] (seed count)).2.1 + 1,
        2 * (step^[iterations] (seed count)).2.2)).1 ≤ _
    split_ifs with done
    · omega
    · dsimp only
      omega

theorem initialRegisters_remaining (count : ℕ) : (initialRegisters count).1 = 0 := by
  have bound := remaining_le count count
  unfold initialRegisters
  omega

theorem span_eq_pow_height (count : ℕ) : span count = 2 ^ height count :=
  (iterate_invariant count count).1

theorem count_le_span (count : ℕ) : count ≤ span count := by
  have upper := (iterate_invariant count count).2.2.2.1
  change count - 1 < span count * ((initialRegisters count).1 + 1) at upper
  rw [initialRegisters_remaining, zero_add, mul_one] at upper
  omega

theorem span_le (count : ℕ) : span count ≤ 2 * max 1 count :=
  (iterate_invariant count count).2.2.2.2.1

theorem height_eq_clog (count : ℕ) : height count = Nat.clog 2 count := by
  apply Nat.le_antisymm (iterate_invariant count count).2.2.2.2.2
  exact Nat.clog_le_of_le_pow ((count_le_span count).trans_eq (span_eq_pow_height count))

theorem span_zero : span 0 = 1 := rfl
theorem height_zero : height 0 = 0 := rfl
theorem span_one : span 1 = 1 := rfl
theorem height_one : height 1 = 0 := rfl

theorem request_span (count start degree : ℕ) :
    (request count start degree).span = 2 ^ (request count start degree).height :=
  span_eq_pow_height count

/-- Uniform bit bound on every iteration state, not only on the final state.
The span needs at most two additional bits beyond the encoded count. -/
theorem iterate_encoding_length (count iterations : ℕ) :
    (encRegisters (step^[iterations] (seed count))).length ≤ 5 * ((encNat count).length + 1) := by
  let state := step^[iterations] (seed count)
  obtain ⟨_, combined, _, _, spanBound, _⟩ := iterate_invariant count iterations
  change state.2.1 + state.1 ≤ count - 1 at combined
  have remainingDigits : (encNat state.1).length ≤ (encNat count).length := by
    rw [length_encNat_eq_size, length_encNat_eq_size]
    exact Nat.size_le_size (by omega)
  have heightDigits : (encNat state.2.1).length ≤ (encNat count).length := by
    rw [length_encNat_eq_size, length_encNat_eq_size]
    exact Nat.size_le_size (by omega)
  have spanDigits : (encNat state.2.2).length ≤ (encNat count).length + 2 := by
    rw [length_encNat_eq_size, length_encNat_eq_size, Nat.size_le]
    have below := Nat.lt_size_self count
    have positive := Nat.two_pow_pos (Nat.size count)
    have maxBound : max 1 count ≤ 2 ^ Nat.size count := by omega
    have bounded : state.2.2 ≤ 2 * max 1 count := spanBound
    rw [pow_add]
    norm_num
    nlinarith
  change (ModularPowerSpace.encTriple state).length ≤ _
  rw [ModularPowerSpace.encTriple_length]
  omega

private theorem first_inSpace :
    ComputableInSpace (fun state : State => state.1) encRegisters encNat
      (fun state => (encRegisters state).length) := fst _ _

private theorem rest_inSpace :
    ComputableInSpace (fun state : State => state.2) encRegisters (encPair encNat encNat)
      (fun state => (encRegisters state).length) := snd _ _

private theorem second_inSpace :
    ComputableInSpace (fun state : State => state.2.1) encRegisters encNat
      (fun state => (encRegisters state).length) := fst' rest_inSpace

private theorem third_inSpace :
    ComputableInSpace (fun state : State => state.2.2) encRegisters encNat
      (fun state => (encRegisters state).length) := snd' rest_inSpace

/-- Every transition is globally linear in its binary argument, including
arbitrary triples that do not satisfy the initialization invariant. -/
theorem step_inSpace :
    ComputableInSpace step encRegisters encRegisters (fun state => (encRegisters state).length) := by
  have half := budget_natDiv first_inSpace (budget_const (encB := encNat) 2 (.refl _))
  have incremented := budget_natSucc second_inSpace
  have doubled := budget_natMul (budget_const (encB := encNat) 2 (.refl _)) third_inSpace
  have advanced := budget_prod half (budget_prod incremented doubled)
  have unchanged := budget_prod first_inSpace (budget_prod second_inSpace third_inSpace)
  apply (budget_ite (budget_natIsZero first_inSpace) unchanged advanced).of_enc_eq
  intro state
  simp only [step, decide_eq_true_eq, ModularPowerSpace.encTriple]

theorem seed_inSpace :
    ComputableInSpace seed encNat encRegisters (fun count => (encNat count).length) := by
  have identity : ComputableInSpace (fun count : ℕ => count) encNat encNat
      (fun count => (encNat count).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  exact budget_prod (budget_natPred identity)
    (budget_prod (budget_const (encB := encNat) 0 (.refl _)) (budget_const 1 (.refl _)))

/-- One fixed finite-control CSLib machine constructs the canonical height and
span in work space linear in the binary count, including count zero. -/
theorem initialRegisters_inSpace :
    ComputableInSpace initialRegisters encNat encRegisters (fun count => (encNat count).length) := by
  have identity : ComputableInSpace (fun count : ℕ => count) encNat encNat
      (fun count => (encNat count).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  exact budget_iterate identity seed_inSpace step_inSpace
    (B := fun count => 5 * ((encNat count).length + 1))
    (fun count iterations _ => iterate_encoding_length count iterations) (linear_mul 5)

theorem height_inSpace :
    ComputableInSpace height encNat encNat (fun count => (encNat count).length) :=
  fst' (snd' initialRegisters_inSpace)

theorem span_inSpace :
    ComputableInSpace span encNat encNat (fun count => (encNat count).length) :=
  snd' (snd' initialRegisters_inSpace)

/-- Construct the complete raw request from `(count,start,degree)` in global
linear space. The supplied start and degree are preserved as binary data. -/
theorem request_inSpace :
    ComputableInSpace (fun input : State => request input.1 input.2.1 input.2.2)
      encRegisters CoefficientStackEncoding.encRequest
      (fun input => (encRegisters input).length) := by
  have computedHeight := budget_comp_linear height_inSpace first_inSpace
  have computedSpan := budget_comp_linear span_inSpace first_inSpace
  apply (budget_prod computedHeight
    (budget_prod second_inSpace (budget_prod third_inSpace computedSpan))).of_enc_eq
  intro input
  rfl

def initialState (count start degree : ℕ) : CoefficientStackEncoding.RawState :=
  ⟨request count start degree, none, []⟩

/-- The complete initial raw evaluator state, including its empty result and
stack, has a fixed-machine certificate with no supplied height or span. -/
theorem initialState_inSpace :
    ComputableInSpace (fun input : State => initialState input.1 input.2.1 input.2.2)
      encRegisters CoefficientStackEncoding.encState
      (fun input => (encRegisters input).length) := by
  apply (budget_prod request_inSpace
    (budget_prod (budget_const (encB := encOption encNat) none (.refl _))
      (budget_const (encB := encList CoefficientStackEncoding.encContinuation) [] (.refl _)))).of_enc_eq
  intro input
  rfl

end NtimeDspace.CoefficientInitialization
