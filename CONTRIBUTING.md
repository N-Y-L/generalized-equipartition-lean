# Contributing

Use standard notation and compact prose. Retain hypotheses, quantifiers,
citations, and scope limitations. Avoid promotional language and repeated
assurances.

Keep Lean proofs readable and reuse mathlib results. Do not replace analytic
arguments with assumptions containing the conclusion. Run the warning-free
build, proof audit, and compiled-proof recheck described in docs/verification.md.
When changing the checker, run its regression tests. Update the proof guide
and UPDATES.md when the theorem’s scope changes.

Keep dependency caches, compiler output, and machine-specific paths out of
Git. Contributions use the Apache 2.0 license.
