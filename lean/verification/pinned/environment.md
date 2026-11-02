# Workspace-local pinned Lean environment

The compiler and package sources here are the exact versions in `lean/lean-toolchain` and `lean/lake-manifest.json`. The project manifest is unchanged. Source archives were downloaded over verified TLS using `rclone --ca-cert /etc/ssl/cert.pem`. No downloaded ETH source, lakefile, or verification command was executed. No compiler or dependency was installed globally.

The intended compiler is Lean **4.36.0-rc2**, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`, installed at `.toolchains/lean-4.36.0-rc2-darwin_aarch64`. Its official release archive was 637,514,990 bytes and its independently supplied SHA-256 was verified before extraction:

`800c09adb81ac667fd9e8e4211d54bdc5cc5e193b107599f6ae72f69ee9b91ad`

Release URL: https://github.com/leanprover/lean4/releases/download/v4.36.0-rc2/lean-4.36.0-rc2-darwin_aarch64.tar.zst

## Exact dependency source archives

Each archive came from `https://codeload.github.com/OWNER/REPOSITORY/tar.gz/COMMIT` using the repository URL and commit recorded in `source-provenance.json` alongside this record. Archive hashes below were calculated locally after the verified-TLS download; unlike the compiler digest, these are provenance records rather than independent expected digests.

| Package | Pinned commit | Archive SHA-256 |
| --- | --- | --- |
| cslib | `82db31eec215b6843be6df283304cc02e736ddef` | `f5d0f0eba997c00ccd76029522f748a942c2a6de0d0718db3490f30391045b67` |
| mathlib | `69552756cd8a2d2d48763cf7279fd814d6a1224d` | `c238805db23625a8f2bf12bf89508298741cc2a94e26b7de1c2be8c287b277f2` |
| plausible | `129d1ba9a16bc0660f46c79e9fb041ef5d5d80de` | `8273fd504a15f28e0c0eafce657549c09e061bebc553880ee53d0f706242ae7e` |
| LeanSearchClient | `c61286b7b63cbfd563b28e11e81d0a18233a044a` | `641cee1ebf781ea292c1570f522d449788465f30b047d0fb8bb3854cf9b47176` |
| importGraph | `b8cc5dd0a36233b88a6ed5a7dbf1207d09338c60` | `0e4a820fe07262275f7f589e5a6d8df41684cc6b84bf10c79fd827e9f6182875` |
| proofwidgets | `16259c0d07d61ee37d999d05b5cf96338b8daa11` | `98751e51c5a256ce52ea4a2757c24c075fa680100959aede20501605fb8839fc` |
| aesop | `7d11bfa88558f8d3d90afdf6bd877ed70001498d` | `d30a6255d0ae0a7dcd0b3d6224c658aafb1e3f02f3a0fe8fdbaef925bc790224` |
| Qq | `b0256621cb88178e9ad932a53633077b3029e621` | `289746302db6bc06be1aedea9e747900db1a5e5eb4a7edd308571acf37212aa4` |
| batteries | `d4c39b228d4a06f3b00748c2c445a7b9f056a6e3` | `35b25b14e9f915c1466164640e30f9915bf599e6c1061addf5e63a43cf50522a` |
| Cli | `c09cb1e4f1e6e1c231a1175a12b681b075054a1b` | `4f6ee4b7337502e88b98ecb5871b68f038e455a4cf0241c504f12281999fba6d` |

## Local dependency and cache setup

`lean/.lake/pinned-environment/lakefile.toml` declares local path dependencies into `lean/.lake/packages/`. Its separate manifest was generated with the pinned compiler's Lake. This avoids Git network access, which is unavailable in this execution environment. The original project's Git dependency manifest has not been converted to paths.

The trusted Mathlib `Cache` executable was built from those sources. `lean/.lake/pinned-environment/CachePlan.lean` uses Mathlib's own hash implementation to select required artifact names; `lean/.lake/pinned-environment/cache-plan.tsv` records module-to-artifact mappings. Downloads came only from `https://cache.mathlib.org/mathlib4-master/f/` and were unpacked with the compiler-bundled `leantar` via Mathlib's `cache unpack`. Upstream package artifacts emitted into this environment's `.lake/packages/` were copied beside their matching pinned source trees. Cache filenames use Mathlib's source/configuration hashing; they are not SHA-256 filenames.

The current expanded plan contains 3,856 trusted Mathlib/dependency cache artifacts, including the SubGaussian and Archimedean dependency closures. Lean core modules come from the compiler and are excluded from the Mathlib artifact plan. The original MachineContract-only plan contained 3,148 entries: 3,146 cache artifacts and two compiler-provided Lean core modules.

The CSLib target `Cslib.Computability.Machines.Turing.MultiTape.Deterministic` built successfully with the pinned compiler (1,815 Lake jobs, primarily restored cache dependencies). All **46 project modules**, including `MachineContract`, and the root `NtimeDspace.lean` aggregate now pass on the intended pinned stack. The independent audit reports all **468 theorem declarations** and only the standard axioms `Classical.choice`, `Quot.sound`, and `propext`. No theorem report is missing and no proof source changed during or after the recorded checks. The complete record is [`check.json`](check.json), with [`axioms.log`](axioms.log) and individual module logs alongside it.

## Checking project sources

From the repository root:

```sh
python3 scripts/check_pinned_module.py NtimeDspace/Counting.lean NtimeDspace/FormulaInput.lean NtimeDspace/MachineContract.lean
python3 scripts/validate_pinned.py
# Recheck an unchanged stack incrementally:
python3 scripts/validate_pinned.py --reuse-passed
```

The checker accepts only `lean/NtimeDspace/` sources and the explicit root aggregate `lean/NtimeDspace.lean` and verifies the compiler commit. Its output is isolated in `lean/.lake/pinned-check/`; it does not overwrite the Lean 4.23 compatibility artifacts in `lean/.offline-check/`.

The aggregate validator checks source imports in topological order, continues across independent failures, and skips dependents of failed modules. It generates an axiom report outside the proof-source directory and records source/output hashes and per-module logs under `lean/verification/pinned/`. By default it includes all project modules except the old generated `Audit` source, then checks the root `NtimeDspace.lean` aggregate and generates a fresh independent axiom report. Repeated `--exclude MODULE` flags can omit active modules and their dependents from an intermediate sweep; a complete successful record requires the root aggregate to pass. `--reuse-passed` reuses a preceding successful module check only when source/output hashes, every transitive dependency source hash, immediate dependency artifact hashes, and the recorded stack match.

The final successful record was written at `2026-11-01T05:38:11.210073+00:00`. It includes exact source and artifact hashes for every checked module, plus the aggregate, compiler revision, original manifest hash, dependency provenance hash, and validator source hashes.

These checks use the intended pinned dependency stack through a separate local path environment. They are **not a successful invocation of the original project's root `lake build`**, and compiling MachineContract only validates its proposition's definition; it does not prove the resource claim.
