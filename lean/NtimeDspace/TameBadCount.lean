import NtimeDspace.TameTac
import NtimeDspace.CounterAssembly

/-!
# Tier of the bad-row count

The number of bad measurement rows is a sum over the `(r²)^Q` label tuples.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool} {L : ℕ} {env : List ℕ}

theorem tm_badCountT {rT QT sP sN widthT : Term} (hL : 8 ≤ L) (hr : Tm w L 1 rT env)
    (hQ : Tm w L 1 QT env) (hsP : Tm w L 1 sP env) (hsN : Tm w L 1 sN env)
    (hwd : Tm w L 1 widthT env) (hls : Tm w L 1 (powT (mul rT rT) QT) env) :
    Tm w L 8 (badCountT rT QT sP sN widthT) env := by
  unfold badCountT badBeforeT
  tame

end NtimeDspace.ProgTerm
