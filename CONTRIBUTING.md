# Contributing

Use standard notation and compact prose. Preserve hypotheses, quantifiers,
citations, and scope limitations.

Reuse mathlib results. Prove analytic identities from their hypotheses;
do not assume the conclusion. Run the build, proof audit, and compiled-proof
recheck in [verification](docs/verification.md), and the regression tests
when changing the checker. Update the proof guide and [updates](UPDATES.md)
when the theorem's scope changes.

Keep dependency caches, compiler output, and machine-specific paths out of
Git. Contributions use the Apache 2.0 license.
