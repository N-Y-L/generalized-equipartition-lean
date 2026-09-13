# Module map

Import `Equipartition` to use the complete library. Public declarations are in the `Equipartition` namespace.

| Module | Contents |
| --- | --- |
| [Canonical.lean](Canonical.lean) | Boltzmann weight, partition function, canonical expectation, and positivity of the partition function under weight integrability. |
| [GibbsMeasure.lean](GibbsMeasure.lean) | The normalized Gibbs measure, its probability property, and equality of its integral with canonical expectation. |
| [IntegrationByParts.lean](IntegrationByParts.lean) | The one-dimensional product derivative and canonical identities with explicit boundary terms, vanishing limits, weighted-observable integrability, or finite interval endpoints. |
| [Multivariate.lean](Multivariate.lean) | Coordinate derivatives, measure-preserving coordinate splitting, Fubini reduction, and weighted and normalized identities for general differentiable observables. |
| [MainTheorem.lean](MainTheorem.lean) | Generalized equipartition for arbitrary coordinate pairs, alternative integrability hypotheses, the temperature formula, and coordinate-energy consequences. |
| [Examples.lean](Examples.lean) | The positive quadratic Hamiltonian on the real line, with all analytic hypotheses discharged and its partition function evaluated. |

The main entry points are `generalized_equipartition` and `generalized_equipartition_of_integrable`. Both accept arbitrary differentiable Hamiltonians on `Fin (n + 1) → ℝ`. The former takes almost-everywhere boundary limits; the latter takes integrability of the weighted coordinate instead.

For a general observable, use `canonical_partial_identity` or `canonical_partial_identity_of_integrable`. Their unnormalized counterparts are `weighted_partial_identity` and `weighted_partial_identity_of_integrable`. The [proof guide](../docs/proof-guide.md) explains their assumptions and relationship.
