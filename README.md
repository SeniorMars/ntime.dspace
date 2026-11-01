# Nondeterministic Linear Time Is Strictly Contained in Deterministic Linear Space

Charlie Cruz · draft of November 1, 2026 · [PDF](paper.pdf) · [LaTeX source](paper.tex)

We intend to post this paper on arXiv. It is an unrefereed draft, its
proofs have not been independently verified, and the Lean formalization below
is still in progress.

## Claimed results

- Main theorem: `NTIME(n) ⊊ DSPACE(n)` for multitape Turing machines.
  Some language in deterministic linear space needs nondeterministic time
  `Ω(n√log n / (log log n)²)` at every large input length.
- Simulation: `NTIME(T) ∪ coNTIME(T) ⊆ DSPACE(κ(T))`, where
  `κ(T) = T(log log T)²/√log T = o(T)`.
- Sublinear-space counting: the satisfying assignments of a
  bounded-occurrence constraint system of logarithmic arity on `N` variables
  can be counted modulo a prime in space `O(κ(N))`.
- Further consequences:
  - `NTIME(t√log t/(log log t)²) ⊆ DSPACE(t)`, which is partial progress on a
    question of Hopcroft, Paul and Valiant;
  - the same separations for probabilistic and parity time.

## Proof idea

1. Computations as constraint systems. Using the block decomposition of
   Hopcroft, Paul and Valiant, cut a computation of length `t` into intervals
   of about `log t` steps. Once the head moves between blocks are fixed,
   accepting computations correspond one-to-one with the satisfying
   assignments of a system of local constraints on `O(t)` variables.
2. Count, don't follow. Count those assignments in sublinear space, using
   a small-space implementation of Kintali's form of the counting algorithm
   behind the recent refutations of the Exponential Time Hypothesis. The paper
   reproves the construction it uses. The new ingredients are:
   - an identity that recovers the count without Hermite interpolation;
   - group schedules generated from a short seed;
   - coefficients computed on demand;
   - a compact encoding of supports;
   - a retuning of the parameters.
3. Apply the space hierarchy theorem.

The argument does not relativize. Section 7 of the paper discusses its limits
and what remains to be checked.

## Status and verification

- The paper is self-contained apart from classical facts: the space hierarchy
  theorem, Hoeffding's inequality, the prime number theorem, and Chinese
  remaindering in logarithmic space.
- The draft was prepared with the help of large language models, as stated in
  the paper. Responsibility for the claims rests with the author.
- Finite exact-arithmetic checks of the algebra are in [scripts/](scripts/)
  (paper, Appendix C). They test toy sizes, not the asymptotic bounds.
- A Lean 4 formalization is underway in [lean/](lean/); see
  [progress and plan](lean_progress.md). The checked parts are free of
  `sorry` and user axioms. The full separation is not yet machine-verified.

Feedback, especially on the space accounting of Section 4 and on Lemma 5.1 (computations as constraint systems), is
very welcome.

## Building

```sh
latexmk -pdf paper.tex
```

## Repository

- [Lean formalization](lean/README.md) and [progress](lean_progress.md)
- [Mathematical audit](notes/paper-audit.md)
- [Reuse of Complexitylib](references/complexitylib/README.md), [CSLib model notes](references/cslib/README.md), [ETH source snapshots](references/eth/README.md)
