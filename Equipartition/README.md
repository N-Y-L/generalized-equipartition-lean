# Module map

Import `Equipartition`. Public declarations use the `Equipartition` namespace.

| Module | Contents |
| --- | --- |
| [Canonical.lean](Canonical.lean) | Boltzmann weight, partition function, canonical expectation, and positivity. |
| [GibbsMeasure.lean](GibbsMeasure.lean) | Gibbs probability measure and its expectation formula. |
| [IntegrationByParts.lean](IntegrationByParts.lean) | One-dimensional identities with finite or infinite endpoint corrections. |
| [Multivariate.lean](Multivariate.lean) | Coordinate splitting, Fubini, and observable identities with Fréchet derivatives. |
| [Slices.lean](Slices.lean) | Coordinate and observable identities with almost-everywhere slice regularity and countable derivative exceptions. |
| [MainTheorem.lean](MainTheorem.lean) | Coordinate law with Fréchet derivatives, temperature and Gibbs forms, and quadratic-coordinate consequence. |
| [VectorField.lean](VectorField.lean) | General vector-field identity under slice or Fréchet regularity; canonical virial identity. |
| [Boundary.lean](Boundary.lean) | Variable finite coordinate domains, one-sided traces, and boundary correction from FTC and Fubini. |
| [DomainTheorem.lean](DomainTheorem.lean) | Normalized domain identity and coordinate law with retained flux. |
| [Domains.lean](Domains.lean) | Arbitrary open domains with supported observables; local C¹ compact-support corollary. |
| [BoundaryExample.lean](BoundaryExample.lean) | Uniform measure on $(0,1)$, with nonzero boundary correction and analytic hypotheses proved. |
| [LaplaceExample.lean](LaplaceExample.lean) | Nonsmooth $H(x)=\lvert x\rvert$ on $\mathbb R$: integrability, partition function, and mean energy. |
| [Examples.lean](Examples.lean) | Positive quadratic Hamiltonian on $\mathbb R$, with every analytic hypothesis proved. |

For the weakest whole-space coordinate hypotheses in this library, use `generalized_equipartition_slices` or `_slices_of_integrable`. The `canonical_slice_identity` variants handle general scalar observables; `canonical_vector_identity_slices` sums their coordinate contributions. The [proof guide](../docs/proof-guide.md) states the assumptions and domain limits.
