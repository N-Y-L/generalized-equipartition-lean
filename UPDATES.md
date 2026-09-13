# Updates

## 2026-09-13

Added attribution identifying the project lead and the use of OpenAI Codex
for Lean formalization and mathematical drafting. Proof sources are unchanged.

### Documentation cleanup

Shortened the README, organized the proof guide, and removed internal guidance and development notes. All Lean sources, build files, and verification code are unchanged.

### Formalization

- Canonical coordinate and observable identities for arbitrary finite dimension and coupled Hamiltonians, with explicit integrability and boundary hypotheses.
- Almost-everywhere coordinate-slice regularity, permitting countably many derivative exceptions per continuous slice; Fréchet differentiability is an optional stronger hypothesis.
- General vector-field and canonical virial identities.
- Variable finite coordinate domains with retained one-sided boundary traces, plus arbitrary open domains for supported observables.
- Gibbs probability measure, temperature formula, quadratic-coordinate consequence, and a positive quadratic example with all analytic hypotheses proved.
- Nonsmooth $H(x)=|x|$ example with all analytic hypotheses proved, plus a uniform interval example verifying the nonzero boundary correction.
- Pinned dependencies, compiled-proof recheck, transitive axiom audit, checker regression tests, and GitHub Actions workflow.
- Proof guide, module map, and verification report.

See [verification](docs/verification.md) for completed checks.
