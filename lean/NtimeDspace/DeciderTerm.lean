import NtimeDspace.ParamTerm
import NtimeDspace.ArithHelpers
import NtimeDspace.PlacementSearch
import NtimeDspace.CounterAssembly

/-!
# The decider as a term

For a machine with `k` tapes, `s` states and clock constant `c`, at input
length `x` (`lvl 0`): for every schedule `σ < 3^((k+1)·numBlocks t)` and every
`p ≤ N³` with `4N² < p` prime, run the network counter modulo `p`; accept if
some residue is nonzero (`mainT`). The counter runs only for such primes, so
its values stay bounded.
-/

namespace NtimeDspace.ProgTerm

open Term LocalSim Turing

variable (k s c : ℕ) {State : Type} [DecidableEq State] (e : State ≃ Fin s)
  (machine : MultiTapePTM k Bool State) (xT : Term)

/-- The number of vertices of the block network. -/
def verticesT : Term :=
  add (mul (numBlocksT c xT) (const (3 * k + 2)))
    (mul (mul (numBlocksT c xT) (const (3 * k + 1))) (mul (const (s + k + 4)) (blockLenT c xT)))

/-- `identifierBits N m = log₂ (max N m) + 1`. -/
def inputBitsT : Term :=
  add (log2T (maxT (edgesNT k s c xT) (verticesT k s c xT)) (maxT (edgesNT k s c xT) (verticesT k s c xT)))
    (const 1)

/-- The local simulation radix `3^(4b) + |x| + s + 3`. -/
def localRadixT : Term :=
  add (add (add (powT (const 3) (mul (const 4) (blockLenT c xT))) xT) (const s)) (const 3)

/-- The number of copies `2·(2N) / (2^k·2^k)^Q`. -/
def copiesT : Term :=
  div (mul (const 2) (mul (const 2) (edgesNT k s c xT)))
    (powT (mul (pow2 (kpT k s c xT)) (pow2 (kpT k s c xT))) (QpT k s c xT))

/-- The arity, port and weight terms of schedule `σ`. -/
def arityAt (σT : Term) : Term → Term := arityNT k s (numBlocksT c xT) (blockLenT c xT) σT
def portAt (σT : Term) : Term → Term → Term := portAtT k s (numBlocksT c xT) (blockLenT c xT) σT
def weightAt (σT : Term) : Term → Term → Term :=
  weightNT k s e machine (localRadixT s c xT) xT (numBlocksT c xT) (blockLenT c xT) σT

/-- The first balanced seed number of schedule `σ`. -/
def seedAt (σT : Term) : Term :=
  seedT (QpT k s c xT) (kpT k s c xT) (inputBitsT k s c xT) (edgesNT k s c xT) (verticesT k s c xT)
    (arityAt k s c xT σT)
    (fun sd e' i => labelT (QpT k s c xT) (kpT k s c xT) (inputBitsT k s c xT) sd (portAt k s c xT σT e' i) e')

/-- The network counter of schedule `σ` modulo `p`. -/
def counterAt (σT pT : Term) : Term :=
  systemCounterT pT (QpT k s c xT) (add (qpT k s c xT) (const 1)) (edgesNT k s c xT) (qpT k s c xT)
    (lgNT k s c xT) (radixPT k s c xT) (limitT k s c xT) (edgesNT k s c xT) (verticesT k s c xT)
    (kpT k s c xT) (inputBitsT k s c xT) (seedAt k s c xT σT) (startPT k s c xT) (const 0)
    (RpT k s c xT) (copiesT k s c xT) (arityAt k s c xT σT) (portAt k s c xT σT)
    (weightAt k s c e machine xT σT)

/-- The main loop: the number of pairs (schedule, prime) with a nonzero residue. -/
def mainT : Term :=
  sumT (powT (const 3) (mul (const (k + 1)) (numBlocksT c xT))) fun σT =>
    sumT (add (mul (edgesNT k s c xT) (mul (edgesNT k s c xT) (edgesNT k s c xT))) (const 1)) fun pT =>
      ite (mul (lt (mul (const 4) (mul (edgesNT k s c xT) (edgesNT k s c xT))) pT) (primeT pT))
        (lt (const 0) (mod (counterAt k s c e machine xT σT pT) pT)) (const 0)

end NtimeDspace.ProgTerm
