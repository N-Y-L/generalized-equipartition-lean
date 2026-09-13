# Verification

The formalization uses Lean 4.28.0 and mathlib revision
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. These versions are pinned in
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## Checks

```sh
lake exe cache get
lake --wfail build
LEAN_NUM_THREADS=1 lake env leanchecker Equipartition
python3 -m unittest discover -s checks -p 'test_*.py'
LEAN_NUM_THREADS=1 python3 checks/check_proofs.py
```

The warning-free library build, bundled compiled-proof recheck, and eight
checker regression tests passed on 13 September 2026. The axiom audit covered
all 99 project declarations, including private and generated declarations,
with 69 named theorem reports. All 15 project Lean files were scanned.
Every library module is imported by the aggregate `Equipartition.lean`.
The only transitive axioms were `propext`, `Classical.choice`, and `Quot.sound`.
No unfinished proofs or new axioms occur in the library.

The build was also repeated in a fresh source copy with no project build
products. That copy reused the pinned dependency builds. Source and
configuration hashes and the status of hosted verification are recorded in
[`checks/results.json`](../checks/results.json).

## What the checks establish

`checks/Axioms.lean` selects declarations by their originating library module,
regardless of declaration namespace or visibility. It rejects unsafe project
declarations and recursively traverses declaration types and proof terms,
including imported dependencies. Any axiom outside the three standard
principles above fails the audit. The source scan is supplementary.

`checks/check_proofs.py` requires the aggregate library to import every
Lean module beneath `Equipartition/`. Missing imports fail the check.

The regression tests exercise rejection of placeholders, quoted placeholders,
unused custom axioms, private declarations, declarations outside the project
namespace, unsafe declarations, and omitted library imports. They also test
comment/string handling and acceptance of valid proofs.

Lean's bundled `leanchecker` rechecks compiled proofs using Lean's kernel;
it is not a separately implemented proof assistant. These checks establish
derivability of the encoded statements. Source reviews separately examined
the mathematical hypotheses, normalization, coordinate measures, slice
regularity, boundary terms, and the Gaussian, cusp, and confined examples.

The general theorem assumes the analytic conditions in the
[proof guide](proof-guide.md). The Gaussian and absolute-value examples prove
those conditions from parameter positivity. The uniform interval example proves
its domain hypotheses and verifies a nonzero boundary correction.

This report records local checks. Hosted verification is tracked in
[GitHub Actions](https://github.com/N-Y-L/generalized-equipartition-lean/actions).
