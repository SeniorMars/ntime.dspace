import NtimeDspace.TameTac

/-!
# Deciding finitely many inputs by a table

`tableT vs` is positive at input `w` (with the input length on the
environment) exactly when `w ∈ vs`. Its values are at most `|vs|` and its
constants at most the largest word length, so it is bounded by any `B` above
both (`tableT_bnd`).
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- `1` if the input bits from position `i` on are `v`. -/
def bitsMatchT : List Bool → ℕ → Term
  | [], _ => const 1
  | b :: bs, i => mul (eqT (input (const i)) (const (if b then 1 else 0))) (bitsMatchT bs (i + 1))

/-- `1` if the input is `v`, reading the input length from `lvl 0`. -/
def matchT (v : List Bool) : Term := mul (eqT (lvl 0) (const v.length)) (bitsMatchT v 0)

/-- The number of words of `vs` equal to the input. -/
def tableT : List (List Bool) → Term
  | [] => const 0
  | v :: vs => add (matchT v) (tableT vs)

theorem inputValue_eq (w : List Bool) (i : ℕ) (h : i < w.length) :
    ProgLang.Prog.inputValue w i = if w[i] then 1 else 0 := by
  unfold ProgLang.Prog.inputValue
  rw [List.getElem?_eq_getElem h]
  cases w[i] <;> rfl

theorem bitsMatchT_denote (v : List Bool) (i : ℕ) (env : List ℕ) (hlen : i + v.length = w.length) :
    (bitsMatchT v i).denote w env = if w.drop i = v then 1 else 0 := by
  induction v generalizing i with
  | nil =>
    simp only [bitsMatchT, denote_const]
    rw [if_pos (List.drop_eq_nil_of_le (by simp at hlen; omega))]
  | cons b bs ih =>
    have hi : i < w.length := by simp at hlen; omega
    have hin : (input (const i)).denote w env = if w[i] then 1 else 0 := by
      rw [denote_input, denote_const, inputValue_eq w i hi]
    simp only [bitsMatchT, denote_mul, denote_eqT, hin, denote_const]
    rw [ih (i + 1) (by simp at hlen; omega), List.drop_eq_getElem_cons hi]
    have hiff : ((if w[i] then 1 else 0 : ℕ) = (if b then 1 else 0)) ↔ w[i] = b := by
      cases w[i] <;> cases b <;> simp
    by_cases h1 : w[i] = b
    · rw [if_pos (hiff.mpr h1), one_mul]
      by_cases h2 : w.drop (i + 1) = bs
      · rw [if_pos h2, if_pos (by rw [h1, h2])]
      · rw [if_neg h2, if_neg (fun h => h2 (List.cons.inj h).2)]
    · rw [if_neg (fun h => h1 (hiff.mp h)), zero_mul, if_neg (fun h => h1 (List.cons.inj h).1)]

theorem matchT_denote (v : List Bool) (env : List ℕ) :
    (matchT v).denote w (env ++ [w.length]) = if w = v then 1 else 0 := by
  have h0 : (lvl 0).denote w (env ++ [w.length]) = w.length := by
    simp [denote_lvl, List.getD_eq_getElem?_getD, List.getElem?_append_right]
  simp only [matchT, denote_mul, denote_eqT, h0, denote_const]
  by_cases hl : w.length = v.length
  · rw [if_pos hl, one_mul, bitsMatchT_denote v 0 _ (by omega), List.drop_zero]
  · rw [if_neg hl, zero_mul, if_neg (fun h => hl (by rw [h]))]

theorem tableT_denote (vs : List (List Bool)) (env : List ℕ) :
    (1 ≤ (tableT vs).denote w (env ++ [w.length]) ↔ w ∈ vs) := by
  induction vs with
  | nil => simp [tableT]
  | cons v vs ih =>
    simp only [tableT, denote_add, matchT_denote, List.mem_cons]
    by_cases h : w = v
    · simp [h]
    · simp [h, ih]

variable {L : ℕ}

theorem Tm.of_le {t : Term} {d d' : ℕ} {env : List ℕ} (h : Tm w L d t env)
    (hv : ∀ env', t.denote w env' < 2 ^ (d' * L)) : Tm w L d' t env :=
  fun pre hp => ⟨(h pre hp).1, hv _⟩

theorem bitsMatchT_le (v : List Bool) (i : ℕ) (env : List ℕ) : (bitsMatchT v i).denote w env ≤ 1 := by
  induction v generalizing i with
  | nil => simp [bitsMatchT]
  | cons b bs ih =>
    simp only [bitsMatchT, denote_mul, denote_eqT]
    have := ih (i + 1)
    split_ifs <;> omega

theorem matchT_le (v : List Bool) (env : List ℕ) : (matchT v).denote w env ≤ 1 := by
  simp only [matchT, denote_mul, denote_eqT]
  have := bitsMatchT_le (w := w) v 0 env
  split_ifs <;> omega

theorem tableT_le (vs : List (List Bool)) (env : List ℕ) : (tableT vs).denote w env ≤ vs.length := by
  induction vs with
  | nil => simp [tableT]
  | cons v vs ih =>
    simp only [tableT, denote_add, List.length_cons]
    have := matchT_le (w := w) v env
    omega

theorem tm_bitsMatchT (v : List Bool) (i : ℕ) {env : List ℕ} (hL : 2 ≤ L)
    (hc : i + v.length < 2 ^ L) : Tm w L 1 (bitsMatchT v i) env := by
  induction v generalizing i with
  | nil => exact t_const (lit_lt_two_pow (by omega) hL)
  | cons b bs ih =>
    have ih' := ih (i + 1) (by simp at hc; omega)
    have hi : Tm w L 1 (const i) env := t_const (by simp at hc; omega)
    have hb : Tm w L 1 (const (if b then 1 else 0)) env := t_const (lit_lt_two_pow (by split_ifs <;> omega) hL)
    refine Tm.of_le (d := 3) ?_ (fun env' => ?_)
    · show Tm w L 3 (mul (eqT (input (const i)) (const (if b then 1 else 0))) (bitsMatchT bs (i + 1))) env
      refine (tm_mul (d1 := 1) (d2 := 1) (d := 2) ?_ ih' (by omega) (by omega)).mono (by omega)
      tame
    · have h2 := lit_lt_two_pow (L := L) (k := 1) (by omega) hL
      have := bitsMatchT_le (w := w) (b :: bs) i env'
      simp only [one_mul]; omega

theorem tm_matchT (v : List Bool) {env : List ℕ} (hL : 2 ≤ L) (hc : v.length < 2 ^ L)
    (hx : Tm w L 1 (lvl 0) env) : Tm w L 1 (matchT v) env := by
  have hbm := tm_bitsMatchT (w := w) (env := env) v 0 hL (by omega)
  have hv : Tm w L 1 (const v.length) env := t_const hc
  refine Tm.of_le (d := 2) ?_ (fun env' => ?_)
  · unfold matchT
    exact tm_mul (d1 := 1) (d2 := 1) (by tame) hbm (by omega) (by omega)
  · have h2 := lit_lt_two_pow (L := L) (k := 1) (by omega) hL
    have := matchT_le (w := w) v env'
    simp only [one_mul]; omega

theorem tm_tableT (vs : List (List Bool)) {env : List ℕ} (hL : 2 ≤ L)
    (hlen : ∀ v ∈ vs, v.length < 2 ^ L) (hcnt : vs.length < 2 ^ L) (hx : Tm w L 1 (lvl 0) env) :
    Tm w L 1 (tableT vs) env := by
  induction vs with
  | nil => exact t_const (lit_lt_two_pow (by omega) hL)
  | cons v vs ih =>
    have ih' := ih (fun u hu => hlen u (List.mem_cons_of_mem _ hu)) (by simp at hcnt; omega)
    have hm := tm_matchT (w := w) v hL (hlen v List.mem_cons_self) hx
    refine Tm.of_le (d := 2) (tm_add hm ih' (by omega) (by omega) (by omega) (by omega))
      (fun env' => ?_)
    have := tableT_le (w := w) (v :: vs) env'
    simp only [one_mul]; omega

end NtimeDspace.ProgTerm
