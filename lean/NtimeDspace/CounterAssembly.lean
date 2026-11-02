import NtimeDspace.AssemblyPrep
import NtimeDspace.MeasTerm

/-!
# The counter term computes the weighted count modulo `p`

`systemCounterT` is the counter term with every accessor filled in: groups and
labels from the seed number `s`, copies as ranks, the spectral accessors, and
the system's own arity, variable and weight terms. `systemCounterT_eq`: for a
balanced seed number and the parameter conditions of
`WConcreteCountingLoop.countModP_correct`, it computes `S.count` modulo `p`.
-/

namespace NtimeDspace.ProgTerm

open Term Placement WeightedSystem

variable {w : List Bool} {n : ℕ}

section Def

variable (pT QT orderT B Cap Lb M K nT mT bitsT IBT sT sPT sNT widthT copiesT : Term)
  (arity : Term → Term) (varT : Term → Term → Term) (weight : Term → Term → Term)

def rT' : Term := pow2 bitsT
def lbT' : Term → Term → Term := fun e i => labelT QT bitsT IBT sT (varT e i) e
def cpT' : Term → Term → Term := copyRankT mT arity (lbT' QT bitsT IBT sT varT)
def rowsT' : Term := mul copiesT (badCountT (rT' bitsT) QT sPT sNT widthT)

/-- **The counter term for a weighted system** with all accessors filled in. -/
def systemCounterT : Term :=
  counterT pT QT orderT B Cap Lb M K nT (rT' bitsT)
    (rowsT' QT bitsT sPT sNT widthT copiesT)
    (mul (rT' bitsT) (rowsT' QT bitsT sPT sNT widthT copiesT))
    (powT (rT' bitsT) (mul (const 2) QT)) mT
    (fun nd v => grpT QT bitsT IBT sT (const 0) nd v)
    (fun nd e => grpT QT bitsT IBT sT (const 1) nd e) arity
    (rowNumT (rowsT' QT bitsT sPT sNT widthT copiesT))
    (fun nd => measSignT (rT' bitsT) QT sPT sNT widthT mT arity (cpT' QT mT bitsT IBT sT arity varT)
      (lbT' QT bitsT IBT sT varT) varT (signPosT (rT' bitsT) QT) nd)
    (fun nd => measSignT (rT' bitsT) QT sPT sNT widthT mT arity (cpT' QT mT bitsT IBT sT arity varT)
      (lbT' QT bitsT IBT sT varT) varT (signNegT (rT' bitsT) QT) nd)
    weight
    (fun nd => lcT pT (rT' bitsT) QT sPT sNT widthT mT arity (cpT' QT mT bitsT IBT sT arity varT)
      (lbT' QT bitsT IBT sT varT) varT nd)
    (fun _nd => mcT pT (rT' bitsT) QT sPT sNT widthT (cpT' QT mT bitsT IBT sT arity varT)
      (lbT' QT bitsT IBT sT varT))
    (evalCT pT (rT' bitsT) QT sPT sNT widthT mT arity (cpT' QT mT bitsT IBT sT arity varT)
      (lbT' QT bitsT IBT sT varT) varT)

end Def

theorem nodeValues_injective {P Q : ℕ} [Fact P.Prime] (hQP : Q < P) :
    Function.Injective (nodeValues (P := P) Q) := by
  intro a b h
  unfold nodeValues at h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at this
  exact Fin.ext (by omega)

theorem nodeValues_ne_zero {P Q : ℕ} [Fact P.Prime] (hQP : Q < P) (a : Fin Q) : nodeValues (P := P) Q a ≠ 0 := by
  unfold nodeValues
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at this
  omega

theorem two_ne_zero_of_lt {P : ℕ} [Fact P.Prime] (hP3 : 2 < P) : (2 : ZMod P) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [show ((2 : ZMod P)) = ((2 : ℕ) : ZMod P) by simp, ZMod.val_natCast, Nat.mod_eq_of_lt hP3,
    ZMod.val_zero] at this
  omega

end NtimeDspace.ProgTerm
