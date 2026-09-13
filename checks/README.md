# Proof checks

Run `lake --wfail build` before `python3 checks/check_proofs.py`.
The script scans project Lean sources, checks that the aggregate imports
every library module, and runs `Axioms.lean` to inspect all transitive axiom
dependencies. The regression suite is:

```sh
python3 -m unittest discover -s checks -p 'test_*.py'
```

`results.json` records the checked source hashes and verification results.
The source scan excludes dependency caches and Git metadata. The authoritative
axiom check uses Lean's environment, including private/generated declarations.
Its scope and limitations are described in
[the verification report](../docs/verification.md).
