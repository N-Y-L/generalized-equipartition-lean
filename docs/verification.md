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
all 47 project declarations, including private and generated declarations,
with 32 named theorem reports. All eight project Lean files were scanned.
Every library module is imported by the aggregate `Equipartition.lean`.
The only transitive axioms were `propext`, `Classical.choice`, and `Quot.sound`.
No unfinished proofs or new axioms occur in the library.

The build was also repeated in a fresh source copy with no project build
products. That copy reused the pinned dependency builds. Source and
configuration hashes and the status of hosted verification are recorded in
[`checks/results.json`](../checks/results.json).

## Audit scope

`checks/Axioms.lean` selects declarations by their originating library module,
regardless of declaration namespace or visibility. It rejects unsafe project
declarations and recursively traverses declaration types and proof terms,
including imported dependencies. Any axiom outside the three standard
principles above fails the audit. The source scan is supplementary.

`checks/check_proofs.py` also requires the aggregate library to import every
Lean source module beneath `Equipartition/`. A missing import fails the check,
so a new library file cannot silently evade the dependency audit.

The regression tests exercise rejection of placeholders, quoted placeholders,
unused custom axioms, private declarations, declarations outside the project
namespace, unsafe declarations, and omitted library imports. They also test
comment/string handling and acceptance of valid proofs.

Lean's bundled `leanchecker` rechecks compiled proofs using Lean's kernel.
It is not a separately implemented proof assistant. Compilation and axiom
audits establish derivability of the encoded statements; they do not decide
whether the assumptions match a physical model. Two separate source reviews
checked the statement, normalization, coordinate measure, boundary terms,
and quadratic example. The identified normalizability omission in two
supporting statements was corrected before the final build.

The general theorem assumes differentiability and the stated integrability
and boundary conditions. The quadratic example proves its analytic
conditions from positivity of its two parameters. The prior-art search is
separate from proof verification and does not establish priority.
