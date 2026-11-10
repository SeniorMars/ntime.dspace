# Simulating Nondeterministic Time in Sublinear Deterministic Space

Charlie Cruz · draft of November 8, 2026 · [PDF](paper.pdf) · [LaTeX source](paper.tex)

Every nondeterministic multitape Turing machine running in time `t(n) ≥ n` can be simulated
deterministically in space `O(t/√log t)`. By the space hierarchy theorem,
`NTIME[n] ⊊ SPACE[n]`. The draft is unrefereed. The proof is verified in Lean.

We found the result on Monday, October 26, 2026, the day the refutation of the Exponential Time
Hypothesis came out. Since then we have written a better account, checked the mathematics and
formalized the proof.

## The paper

The simulation computes the number of accepting computations. Hopcroft, Paul and Valiant's
blocking writes this number as a sum of values of sparse networks of size `s = O(t)`. Each value
is computed with the grid recursion behind Anthropic's refutation of the Exponential Time
Hypothesis, using new crossing pieces built from walks on the Boolean cube. Each merge halves the
node names, and the potential divided by the name length never increases. The last label has
`O(s/√log s)` bits. The recursion is an integer formula, and each bit of its value is computed
depth first in space about the length of the indices on one path.

Since the simulation computes every bit of the count, the same bound holds for `PPTIME[t]`.
Reaching space `t/log t` this way would count the satisfying assignments of 3-CNF formulas
faster than any known algorithm.

## Lean

[lean/](lean/) proves Theorem 1.1, Corollary 1.2, Theorem 7.1, Corollary 7.2, Propositions 8.1
and 8.2 and Remark 8.3 for every `t(n) ≥ n`, together with the implications of §8 and the examples
and remarks of §5. It uses Complexitylib's definitions of machines and
classes and only Lean's standard axioms. [Comparator](https://github.com/leanprover/comparator)
confirms that the main endpoints prove statements written against Complexitylib alone. See
[lean/README.md](lean/README.md).

## Building

```sh
latexmk -pdf paper.tex
cd lean && lake exe cache get && lake build
```

## Files

- `paper.tex`, `paper.pdf`: the paper.
- `lean/`: the formalization (see [lean/README.md](lean/README.md)).

The paper and the formalization were developed with assistance from Anthropic's
Claude and OpenAI's ChatGPT. The author is responsible for all claims.
