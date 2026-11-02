import NtimeDspace.ConcreteCountingLoop
import NtimeDspace.ModularCounting
import NtimeDspace.BoundedGammaQuery
import NtimeDspace.BoundedSupportQuery

/-!
Executable smoke checks of the new scalar counter, separate from theorem
validation. Tiny one-group instances keep runtime practical. An additional
spectral check exercises a nonempty bad-label residual. Bounded gamma examples
compare the scalar specification with actual queries on the encoded packet,
including invalid codewords and register bounds. These checks import only the
new project and its pinned trusted dependencies.
Support examples additionally compare whole-payload validation and cardinality
with the preexisting bounded list specification, including invalid suffixes.
-/

namespace NtimeDspace.CountingExamples

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Each literal position gets its own copy; singleton labels suffice here. -/
def copies {n : ℕ} (formula : Formula n) (inc : FormulaCounter.Incidence formula) :
    Fin (3 * formula.clauses.length) :=
  ⟨3 * inc.1.val + inc.2.val, by
    have hc := inc.1.isLt
    have hl := inc.2.isLt
    have hw := (formula.clauses[inc.1]).width_le_three
    omega⟩

def count {n : ℕ} (formula : Formula n) : ℕ :=
  (ConcreteCountingLoop.countModP 7 (r := 1) (Q := 1) (by decide) formula
    (copies formula) (fun _ _ => (0, 0)) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ => 1) 6 0 1).val

def positive : Clause 1 := ⟨[⟨0, true⟩], by decide⟩
def negative : Clause 1 := ⟨[⟨0, false⟩], by decide⟩
def repeated : Clause 1 := ⟨[⟨0, true⟩, ⟨0, true⟩], by decide⟩
def tautology : Clause 1 := ⟨[⟨0, true⟩, ⟨0, false⟩], by decide⟩

def oneUsed : Formula 2 := ⟨[⟨[⟨0, true⟩], by decide⟩]⟩

def check (name : String) (actual expected : ℕ) : IO Unit := do
  if actual != expected then
    throw (IO.userError s!"{name}: expected {expected}, got {actual}")
  IO.println s!"PASS {name}: {actual}"

/-- Check both the relative-cursor reader and the query run on the full packet. -/
def checkGamma (name : String) (packet : BoundedGammaQuery.Packet)
    (expected : Option (ℕ × ℕ)) : IO Unit := do
  let actual := BoundedGammaQuery.read packet
  let terminal := BoundedGammaQuery.run packet (packet.2.length + 1)
  let queried := BoundedGammaQuery.output terminal
  if actual != expected || queried != expected || !BoundedGammaQuery.halted terminal then
    throw (IO.userError s!"{name}: expected {repr expected}, reader {repr actual}, query {repr queried}")
  IO.println s!"PASS {name}: {repr actual}"

/-- A support is accepted only after its entire encoded payload is validated. -/
def checkSupport (name : String) (packet : BoundedSupportQuery.Packet)
    (expected : Option ℕ) : IO Unit := do
  let actual := BoundedSupportQuery.read packet
  let terminal := BoundedSupportQuery.run packet (packet.2.length + 1)
  let queried := BoundedSupportQuery.output terminal
  let specification := (SupportCardinality.count packet.1.1 packet.1.2 packet.2).map Fin.val
  if actual != expected || queried != expected || specification != expected ||
      !BoundedSupportQuery.halted terminal then
    throw (IO.userError s!"{name}: expected {repr expected}, reader {repr actual}, query {repr queried}, spec {repr specification}")
  IO.println s!"PASS {name}: {repr actual}"

#eval do
  check "positive unit" (count (⟨[positive]⟩ : Formula 1)) 1
  check "negative unit" (count (⟨[negative]⟩ : Formula 1)) 1
  check "contradiction" (count (⟨[positive, negative]⟩ : Formula 1)) 0
  check "repeated occurrence" (count (⟨[repeated]⟩ : Formula 1)) 1
  check "tautology" (count (⟨[tautology]⟩ : Formula 1)) 2
  check "empty clause" (count (⟨[⟨[], by decide⟩]⟩ : Formula 1)) 0
  check "unused declared variables" (count (⟨[]⟩ : Formula 2)) 4
  check "count reduced modulo 7" (count (⟨[]⟩ : Formula 3)) 1
  check "total counter empty formula n=0"
    (ModularCounting.countModP 7 (⟨[]⟩ : Formula 0) (by simp [Formula.BoundedOccurrence, Formula.occurrences])).val 1
  check "total counter empty clause n=0"
    (ModularCounting.countModP 7 (⟨[⟨[], by decide⟩]⟩ : Formula 0) (by simp [Formula.BoundedOccurrence, Formula.occurrences])).val 0
  check "total counter positive unit"
    (ModularCounting.countModP 7 (⟨[positive]⟩ : Formula 1) (by simp [Formula.BoundedOccurrence, Formula.occurrences, positive])).val 1
  check "total counter modular reduction"
    (ModularCounting.countModP 7 (⟨[]⟩ : Formula 3) (by simp [Formula.BoundedOccurrence, Formula.occurrences])).val 1
  check "population includes unused dummy" (PopulationAccess.populationCount oneUsed) 2
  check "scalar used-variable occurrences" (PopulationAccess.occurrences oneUsed 0) 1
  check "scalar unused-variable occurrences" (PopulationAccess.occurrences oneUsed 1) 0
  check "explicit seed search balances tiny instance"
    (if ScheduleSearch.test oneUsed 1 (ScheduleSearch.select oneUsed 1 1) then 1 else 0) 1
  check "joint seed bit-layout roundtrip"
    (AffineSeedEncoding.seedEncode
      (AffineSeedEncoding.seedDecode (inputBits := 2) (Q := 1) (bits := 1) ⟨61, by decide⟩)).val 61
  check "offset-only seed roundtrip"
    (AffineSeedEncoding.seedEncode
      (AffineSeedEncoding.seedDecode (inputBits := 0) (Q := 1) (bits := 1) ⟨3, by decide⟩)).val 3
  checkGamma "gamma zero bound rejects leading one" ((0, 0), [true]) none
  checkGamma "gamma nonzero cursor preserves suffix"
    ((5, 2), [true, false] ++ SupportEncoding.gammaEncode 5 ++ [false, true]) (some (5, 7))
  checkGamma "gamma payload overflow rejects"
    ((5, 0), SupportEncoding.gammaEncode 6) none
  checkGamma "gamma truncated payload rejects"
    ((6, 0), (SupportEncoding.gammaEncode 6).take 4) none
  checkGamma "gamma starting cursor beyond EOF" ((7, 1000), [true]) none
  let longZeros : BoundedGammaQuery.Packet := ((3, 0), List.replicate 128 false ++ [true])
  checkGamma "gamma excessive leading zeros reject" longZeros none
  let rejected := (BoundedGammaQuery.run longZeros 2).parser
  let bounded := (List.range (longZeros.2.length + 2)).all fun fuel =>
    let state := (BoundedGammaQuery.run longZeros fuel).parser
    state.cursor ≤ longZeros.2.length && state.zeros ≤ 1 && state.remaining ≤ 1 &&
      state.accumulator ≤ 3 && state.room ≤ 3
  check "gamma long prefix rejects early with every prefix bounded"
    (if rejected == (⟨3, 1, 1, 0, 0, 1⟩ : BoundedGammaPayload.State) && bounded then 1 else 0) 1
  checkSupport "support empty zero universe and capacity" ((0, 0), []) (some 0)
  checkSupport "support empty with unused capacity" ((10, 8), []) (some 0)
  checkSupport "support nonempty zero capacity" ((10, 0), [true]) none
  checkSupport "support actual width below capacity"
    ((5, 5), SupportEncoding.encodeGaps [1, 2, 2]) (some 3)
  checkSupport "support exactly full capacity accepts EOF"
    ((5, 3), SupportEncoding.encodeGaps [1, 2, 2]) (some 3)
  checkSupport "support capacity overflow rejects extra entry"
    ((10, 3), SupportEncoding.encodeGaps [1, 1, 1, 1]) none
  checkSupport "support cumulative index overflow"
    ((5, 3), SupportEncoding.encodeGaps [3, 3]) none
  checkSupport "support valid prefix with truncated final codeword"
    ((10, 3), SupportEncoding.encodeGaps [1, 2] ++ [false]) none
  checkSupport "support zero universe rejects positive entry" ((0, 3), [true]) none
  checkSupport "support rejects long malformed prefix"
    ((3, 3), List.replicate 128 false ++ [true]) none
  let indices : List (Fin 2 × Fin 2) := [(0, 0), (0, 1), (1, 0), (1, 1)]
  for u in indices do
    for w in indices do
      let actual := DeformationEvaluation.coefficient 7 (by decide : 0 < 2)
        (fun _ : Fin 1 => 1) 0 1 (fun _ => u) (fun _ => w) 3
      check s!"spectral coefficient {u}/{w}" actual.val (if u = w then 1 else 0)

end NtimeDspace.CountingExamples
