# Module map

Import `Equipartition`. Public declarations use the `Equipartition` namespace.

| Module | Contents |
| --- | --- |
| [Canonical.lean](Canonical.lean) | Boltzmann weight, partition function, canonical expectation, and partition-function positivity under weight integrability. |
| [GibbsMeasure.lean](GibbsMeasure.lean) | Gibbs measure, normalization, and equality of its integral with canonical expectation. |
| [IntegrationByParts.lean](IntegrationByParts.lean) | One-dimensional identities with boundary limits, integrability of the weighted observable, or finite interval endpoints. |
| [Multivariate.lean](Multivariate.lean) | Coordinate derivatives, measure-preserving coordinate splitting, Fubini, and weighted and normalized observable identities. |
| [MainTheorem.lean](MainTheorem.lean) | Equipartition for coordinate pairs, alternative integrability hypotheses, temperature formula, Gibbs integral, and quadratic-coordinate consequence. |
| [Examples.lean](Examples.lean) | Positive quadratic Hamiltonian on $\mathbb R$, with analytic hypotheses proved and partition function evaluated. |

`generalized_equipartition` and `generalized_equipartition_of_integrable` treat differentiable Hamiltonians on `Fin (n + 1) → ℝ` with integrable Boltzmann weight and weighted coordinate derivative. The former assumes almost-everywhere vanishing slice limits; the latter assumes integrability of the weighted coordinate.

For general observables, use `canonical_partial_identity` or `canonical_partial_identity_of_integrable`; their unnormalized counterparts are `weighted_partial_identity` and `weighted_partial_identity_of_integrable`. See the [proof guide](../docs/proof-guide.md) for assumptions.
