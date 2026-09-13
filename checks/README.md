# Proof checks

Run `lake --wfail build` before `python3 checks/check_proofs.py`.
The script scans project Lean sources, checks that `Equipartition.lean`
imports every library module, and runs `Axioms.lean` to audit transitive axiom
dependencies of all project declarations. Run the regression suite with:

```sh
python3 -m unittest discover -s checks -p 'test_*.py'
```

`results.json` records the checked source hashes and verification results.
The source scan excludes dependency caches and Git metadata. The axiom audit
uses Lean's environment, including private and generated declarations.
See [verification](../docs/verification.md) for its scope and limitations.
