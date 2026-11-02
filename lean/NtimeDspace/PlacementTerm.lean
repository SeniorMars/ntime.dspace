import NtimeDspace.PlacementNum

/-!
# Hash placement as terms

Terms for the group of an input at a node (`grpT`, computing `grpN`) and the
label number of an incidence (`labelT`, computing `labelN`).
-/

namespace NtimeDspace.ProgTerm

open Term Placement

variable {w : List Bool}

section Def

variable (QT bitsT IBT sT : Term)

def seedPosT (h o c : Term) : Term :=
  add (add (mul h (mul (mul QT bitsT) (add IBT (const 1)))) (mul o (add IBT (const 1)))) c

def parityNT (h node j x : Term) : Term :=
  mod (add (sumT IBT fun c => mul (bit sT (seedPosT QT bitsT IBT h (add (mul node bitsT) j) c))
      (bit x c))
    (bit sT (seedPosT QT bitsT IBT h (add (mul node bitsT) j) IBT))) (const 2)

def grpT (h node x : Term) : Term :=
  sumT bitsT fun j => mul (parityNT QT bitsT IBT sT h node j x) (pow2 j)

def labelT (v e : Term) : Term :=
  sumT QT fun node => mul (add (grpT QT bitsT IBT sT (const 1) node e)
      (mul (pow2 bitsT) (grpT QT bitsT IBT sT (const 0) node v)))
    (powT (mul (pow2 bitsT) (pow2 bitsT)) node)

end Def

theorem StableAt.pow2 {a : Term} {env : List ℕ} (h : StableAt w a env) :
    StableAt w (pow2 a) env := fun extra => by rw [denote_pow2, denote_pow2, h extra]

variable {QT bitsT IBT sT : Term} {env : List ℕ}

theorem denote_seedPosT (h o c : Term) :
    (seedPosT QT bitsT IBT h o c).denote w env =
      seedPos (QT.denote w env) (bitsT.denote w env) (IBT.denote w env) (h.denote w env)
        (o.denote w env) (c.denote w env) := by
  simp [seedPosT, seedPos]

theorem denote_parityNT (hIB : StableAt w IBT env) (hQ : StableAt w QT env)
    (hb : StableAt w bitsT env) (hs : StableAt w sT env) {h node j x : Term}
    (hh : StableAt w h env) (hn : StableAt w node env) (hj : StableAt w j env)
    (hx : StableAt w x env) :
    (parityNT QT bitsT IBT sT h node j x).denote w env =
      parityN (QT.denote w env) (bitsT.denote w env) (IBT.denote w env) (sT.denote w env)
        (h.denote w env) (node.denote w env) (j.denote w env) (x.denote w env) := by
  unfold parityNT parityN
  rw [denote_mod, denote_add, denote_sumT _ _ env (fun c =>
    ((sT.denote w env).testBit (seedPos (QT.denote w env) (bitsT.denote w env) (IBT.denote w env)
      (h.denote w env) (node.denote w env * bitsT.denote w env + j.denote w env) c)).toNat *
      ((x.denote w env).testBit c).toNat)]
  · simp [denote_seedPosT]
  · intro acc c
    simp only [denote_mul, denote_bit, denote_seedPosT, denote_add, denote_lvl_index,
      hIB.cons₂, hQ.cons₂, hb.cons₂, hs.cons₂, hh.cons₂, hn.cons₂, hj.cons₂, hx.cons₂]

theorem StableAt.parityNT (hIB : StableAt w IBT env) (hQ : StableAt w QT env)
    (hb : StableAt w bitsT env) (hs : StableAt w sT env) {h node j x : Term}
    (hh : StableAt w h env) (hn : StableAt w node env) (hj : StableAt w j env)
    (hx : StableAt w x env) : StableAt w (parityNT QT bitsT IBT sT h node j x) env := fun extra => by
  rw [denote_parityNT (hIB.extend extra) (hQ.extend extra) (hb.extend extra) (hs.extend extra)
    (hh.extend extra) (hn.extend extra) (hj.extend extra) (hx.extend extra),
    denote_parityNT hIB hQ hb hs hh hn hj hx, hIB extra, hQ extra, hb extra, hs extra, hh extra,
    hn extra, hj extra, hx extra]

theorem denote_grpT (hIB : StableAt w IBT env) (hQ : StableAt w QT env)
    (hb : StableAt w bitsT env) (hs : StableAt w sT env) {h node x : Term}
    (hh : StableAt w h env) (hn : StableAt w node env) (hx : StableAt w x env) :
    (grpT QT bitsT IBT sT h node x).denote w env =
      grpN (QT.denote w env) (bitsT.denote w env) (IBT.denote w env) (sT.denote w env)
        (h.denote w env) (node.denote w env) (x.denote w env) := by
  unfold grpT grpN
  rw [denote_sumT _ _ env (fun j => parityN (QT.denote w env) (bitsT.denote w env) (IBT.denote w env)
    (sT.denote w env) (h.denote w env) (node.denote w env) j (x.denote w env) * 2 ^ j)]
  intro acc j
  have e : acc :: j :: env = [acc, j] ++ env := rfl
  rw [denote_mul, denote_pow2, e, denote_parityNT (hIB.extend _) (hQ.extend _) (hb.extend _)
    (hs.extend _) (hh.extend _) (hn.extend _) (stableAt_lvl (by simp)) (hx.extend _), ← e]
  simp only [hIB.cons₂, hQ.cons₂, hb.cons₂, hs.cons₂, hh.cons₂, hn.cons₂, hx.cons₂,
    denote_lvl_index]

theorem StableAt.grpT (hIB : StableAt w IBT env) (hQ : StableAt w QT env)
    (hb : StableAt w bitsT env) (hs : StableAt w sT env) {h node x : Term}
    (hh : StableAt w h env) (hn : StableAt w node env) (hx : StableAt w x env) :
    StableAt w (grpT QT bitsT IBT sT h node x) env := fun extra => by
  rw [denote_grpT (hIB.extend extra) (hQ.extend extra) (hb.extend extra) (hs.extend extra)
    (hh.extend extra) (hn.extend extra) (hx.extend extra), denote_grpT hIB hQ hb hs hh hn hx,
    hIB extra, hQ extra, hb extra, hs extra, hh extra, hn extra, hx extra]

theorem denote_labelT (hIB : StableAt w IBT env) (hQ : StableAt w QT env)
    (hb : StableAt w bitsT env) (hs : StableAt w sT env) {v e : Term}
    (hv : StableAt w v env) (he : StableAt w e env) :
    (labelT QT bitsT IBT sT v e).denote w env =
      labelN (QT.denote w env) (bitsT.denote w env) (sT.denote w env) (IBT.denote w env)
        (v.denote w env) (e.denote w env) := by
  unfold labelT labelN
  rw [denote_sumT _ _ env (fun node => (grpN (QT.denote w env) (bitsT.denote w env)
      (IBT.denote w env) (sT.denote w env) 1 node (e.denote w env) +
      2 ^ bitsT.denote w env * grpN (QT.denote w env) (bitsT.denote w env) (IBT.denote w env)
        (sT.denote w env) 0 node (v.denote w env)) *
      (2 ^ bitsT.denote w env * 2 ^ bitsT.denote w env) ^ node)]
  intro acc node
  have e' : acc :: node :: env = [acc, node] ++ env := rfl
  have hn : StableAt w (lvl env.length) ([acc, node] ++ env) := stableAt_lvl (by simp)
  rw [denote_mul, denote_add, denote_mul, denote_pow2, e',
    denote_grpT (hIB.extend _) (hQ.extend _) (hb.extend _) (hs.extend _) (stableAt_const _ _) hn
      (he.extend _),
    denote_grpT (hIB.extend _) (hQ.extend _) (hb.extend _) (hs.extend _) (stableAt_const _ _) hn
      (hv.extend _),
    powT_denote _ _ _ (((hb.extend _).pow2).mul ((hb.extend _).pow2)), ← e']
  simp only [hIB.cons₂, hQ.cons₂, hb.cons₂, hs.cons₂, hv.cons₂, he.cons₂, denote_lvl_index,
    denote_const, denote_mul, denote_pow2]

end NtimeDspace.ProgTerm
