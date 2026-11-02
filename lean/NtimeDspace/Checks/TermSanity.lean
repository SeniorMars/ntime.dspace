import NtimeDspace.ProgTerm
open NtimeDspace.ProgTerm Term
example (w : List Bool) (env : List ℕ) :
    (letT (const 5) fun x => foldT (const 3) (const 0) fun acc i => add acc x).denote w env = 15 := by
  term_simp [foldAcc_succ]
example (w : List Bool) (env : List ℕ) :
    (letT (const 3) fun x => letT (const 4) fun y => add x (mul y x)).denote w env = 15 := by
  term_simp
