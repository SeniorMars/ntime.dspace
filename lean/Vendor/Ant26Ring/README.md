# Vendored: Anthropic's 3-SAT statement

`ThreeSatStatement.lean` is copied from
[anthropics/formal-math](https://github.com/anthropics/formal-math), `eth/` at commit
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, file `proof/statements/ThreeSatStatement.lean`, under
the Apache-2.0 license ([LICENSE](LICENSE), [NOTICE](NOTICE)). It defines 3-SAT on Mathlib's
Turing machines and the tape encoding of an instance (namespace `Sat3`). Corollary 7.2
(`Cross.ThreeSat`) counts the satisfying assignments of instances in this encoding. The file
imports only Mathlib.

The file keeps Anthropic's copyright header, followed by a two-line notice giving its eth path
and its one change: imports renamed under `Vendor.Ant26Ring`. Declarations are unchanged.

No other vendored module is used.
