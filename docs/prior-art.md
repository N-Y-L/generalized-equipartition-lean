# Prior-art review: generalized equipartition

The search completed on 13 September 2026 did not locate an existing public, inspectable formalization of the general canonical identity

$$
\frac{\int_{\mathbb R^n}x_i\,\partial_jH(x)\,e^{-\beta H(x)}\,dx}
{\int_{\mathbb R^n}e^{-\beta H(x)}\,dx}
=\frac{\delta_{ij}}\beta
$$

for general differentiable Hamiltonians under explicit integrability and boundary hypotheses. The search does not establish that no earlier formalization exists. Generic integration by parts is already formalized in Mathlib, and Gaussian Stein identities are already present in a public Lean repository. This repository formalizes a classical result and makes no priority claim.

## Target and mathematical scope

The target is the canonical ensemble expectation with a genuine finite, nonzero partition function, using Lebesgue measure on Cartesian phase-space coordinates. It is distinct from a statement about dynamical time averages, a microcanonical ensemble, quantum energy averages, information-theoretic asymptotic equipartition, or finite symmetry forcing equal shares. Chen, He and Zhao state exactly the target in equation (5), explicitly distinguish canonical from time averages, and discuss failure of normalizability in their example. Their paper is ordinary mathematical physics, not a proof-assistant formalization. [1]

A general mathematical route is to integrate the derivative of $x_i e^{-\beta H(x)}$ in coordinate $j$, justify the iterated integrals, retain or eliminate the boundary term, and divide by the partition function. The proof derives this identity from differentiation, Fubini’s theorem, and the fundamental theorem of calculus. Classical homogeneity variants and their convergence qualifications are discussed by Lima and Plastino. [2]

## Inspected formalization sources

| Source and inspected version | Finding | Relation to this project |
|---|---|---|
| **PhysLean / Physlib**, public master snapshot `c76e3ccab04eacb69a126ca5c021b0788d513292` | `HEPLean/PhysLean` redirects to `leanprover-community/physlib`. Whole-tree searches found no `equipartition` or `virial` occurrence. Canonical ensemble and ideal-gas source files were inspected. | Strongest relevant physics-library check; no exact target located. [3–5] |
| **Mathlib**, current master snapshot `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`; additionally pinned snapshot `8f9d9cff6bd728b17a24e163c9402775d9e6a365` | `equipartition` matches were finite combinatorial partitions, not energy equipartition. General improper integration by parts is implemented. | Existing analytic foundation must be credited; formalizing a physics specialization remains useful but is not a new integration-by-parts theorem. [6–7] |
| **Statlean**, snapshot `dd2c4bbc72b7c643e62985d77c84755b31aec9f5` | `stein_identity` proves $E_\gamma[xh]=E_\gamma[h']$ for differentiable functions satisfying stated Gaussian $L^2$ conditions. `gaussian_ibp_coord` proves a coordinatewise identity for a standard product Gaussian and Lipschitz observables. | Genuine analytic near match: Gaussian/quadratic specialization, not a theorem for arbitrary Gibbs Hamiltonians. Source proof inspected; not independently built in this review. [8] |
| **Goodman, Veselov and Cahill**, May 2026 technical report | Theorem 5.3 describes equal expected closure-energy shares among finite Boolean forced coordinates, derived from coordinate-swap symmetry. The report claims Lean verification and explicitly uses rational Padé weights instead of an exact real exponential. | Different theorem. The report provides no `github` URL in its accessible text; its machine-checking claim was not independently reproduced. [9] |
| **Recognition Physics** displayed Lean theorem | `uniformSiteMeaningLoad_of_supportRHatTransitive` derives equal occupied-site loads from a transitive load-preserving action. | Discrete symmetry statement, with neither Gibbs integration nor derivatives; different theorem. Displayed source inspected, not built. [10] |
| **HOL and Coq information-theory work** | Published formalizations prove the asymptotic equipartition property for typical sequences and source coding. | Unrelated use of “equipartition”; not classical thermal energy partition. [11–12] |

### Physlib details

`Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean` defines Boltzmann weights, partition functions, normalized measures and mean energy. `Lemmas.lean` includes `meanEnergy_eq_ratio_of_integrals` and thermodynamic identities. The temperature/partition-function differentiation lemmas are not coordinatewise integration by parts. `MicroCanonicalEnsemble/IdealGas.lean` computes the Gaussian ideal-gas partition function and derives the ideal-gas law. These are useful adjacent developments, but no arbitrary-Hamiltonian coordinate identity was found. The public GitHub issue/PR search for `equipartition repo:leanprover-community/physlib` returned `total_count: 0`, with `incomplete_results: false`, on the search date. This does not check unnamed ongoing work or all branches. [3–5,13]

### Mathlib and Statlean details

Mathlib's `MeasureTheory.integral_mul_deriv_eq_deriv_mul` and `integral_mul_deriv_eq_deriv_mul_of_integrable` already establish whole-line integration by parts. The former carries explicit endpoint limits; the latter derives the zero-boundary form from product integrability. This is very close to the analytic engine needed for a one-dimensional Gibbs identity. Mathlib also contains Gaussian integrability, moment and normalization results. [6–7]

Statlean's `Gaussian/Stein.lean` directly applies Mathlib's integration-by-parts theorem to the standard Gaussian density. Its multidimensional result uses a coordinate decomposition and Fubini. The existing Gaussian identity should therefore be discussed as prior art, and this theorem's arbitrary-Hamiltonian scope and explicit hypotheses should be clear. `Statlean/ScoreMatching/Basic.lean` was also inspected: it defines scores and losses but does not establish the general Gibbs integration-by-parts identity. [8,14]

## Dated search record

All searches and source inspections below were performed on **2026-09-13**. Search results were treated as leads, with the substantive near matches opened or inspected in source.

| Search surface | Representative exact queries | Result |
|---|---|---|
| General web search | `"equipartition" Lean theorem formalization`; `"generalized equipartition theorem" formal proof Lean`; `"generalized equipartition" "Lean 4"`; `"generalized equipartition" theorem proof assistant` | No exact general canonical formalization located. |
| Alternate proof assistants | `"equipartition" "theorem" "Isabelle"`; `"equipartition" "theorem" "Coq"`; `"equipartition" "theorem" "HOL Light"`; `"equipartition" "Rocq"`; `"equipartition" "Mizar"`; `"equipartition" "Agda"` | No exact target located; information-theoretic AEP was a recurring distinct result. |
| Domain-restricted search | `site:github.com/HEPLean/PhysLean equipartition`; `site:physlean.com equipartition`; `site:github.com Physlib equipartition`; `"equipartition" site:isa-afp.org`; `"equipartition" site:github.com "Isabelle"`; `"equipartition" site:github.com "Coq"` | No exact target located. The old PhysLean site was blocked; the actual repository was checked directly. |
| Alternate terminology | `"Stein identity" "Lean"`; `"equipartition" "formalization" -"asymptotic" -"regularity" -"Shannon"`; `"equipartition" "formalisation" -"asymptotic" -"regularity" -"Shannon"` | Located Statlean Gaussian Stein identities and the finite-symmetry technical report. |
| Local source inspection | Case-insensitive whole-tree patterns `equipartition`, `virial`, `Stein`/`Stein's identity`, `conjugate variable`, with `Boltzmann`/`Gibbs` in Mathlib; inspection of relevant integral, statistical-mechanics, Gaussian and score-matching files | No arbitrary-Hamiltonian canonical equipartition declaration identified in the checked snapshots. |
| Public issue/PR metadata | GitHub Search API, `equipartition repo:leanprover-community/physlib` | Zero matches at query time. |
| Physics project inventory | `lean-phys-community/ITPsInPhysicsArchive` and its linked AFP search | Located relevant libraries but no exact target; the inventory is explicitly incomplete and the AFP search page did not expose a complete corpus result set. [15] |

## Limits

Negative searches are incomplete: code can use other names; search indexes can lag; private work and unmerged branches may be invisible; no exhaustive semantic search or build of all proof-assistant libraries was performed. Current public Mathlib, Physlib and Statlean snapshots were downloaded for text/source inspection, not for reproducing every theorem's build. The finite-symmetry report's advertised verification was not independently confirmed.

## Sources

1. Kai Chen, Dahai He and Hong Zhao. “Violation of the virial theorem and generalized equipartition theorem for logarithmic oscillators serving as a thermostat.” *Scientific Reports* 7, 3460 (14 June 2017), equation (5), discussion of canonical averages, and Methods. [source](https://www.nature.com/articles/s41598-017-03694-w)
2. J. A. S. Lima and A. R. Plastino. “On the classical energy equipartition theorem.” *Brazilian Journal of Physics* 30(1), March 2000. [source](https://www.scielo.br/j/bjp/a/VkxF5CrJpqbVqfmFNkXcGJp/?lang=en) ; DOI [source](https://doi.org/10.1590/S0103-97332000000100019)
3. Physlib community. Repository and rename/merge description, inspected snapshot. [source](https://github.com/leanprover-community/physlib/tree/c76e3ccab04eacb69a126ca5c021b0788d513292)
4. Physlib community. Canonical ensemble definitions. [source](https://github.com/leanprover-community/physlib/blob/c76e3ccab04eacb69a126ca5c021b0788d513292/Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean) ; companion identities [source](https://github.com/leanprover-community/physlib/blob/c76e3ccab04eacb69a126ca5c021b0788d513292/Physlib/StatisticalMechanics/CanonicalEnsemble/Lemmas.lean)
5. Physlib community. Ideal-gas partition function and equation of state. [source](https://github.com/leanprover-community/physlib/blob/c76e3ccab04eacb69a126ca5c021b0788d513292/Physlib/StatisticalMechanics/MicroCanonicalEnsemble/IdealGas.lean)
6. Mathlib community. Improper integration and integration by parts. [source](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean)
7. Mathlib community. Finite combinatorial equipartitions. [source](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Partition/Equipartition.html) ; Gaussian source [source](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/Probability/Distributions/Gaussian/Real.lean)
8. Statlean contributors. Gaussian Stein identities, inspected source at lines 23 and 426. [source](https://github.com/statopia/statlean4/blob/dd2c4bbc72b7c643e62985d77c84755b31aec9f5/Statlean/Gaussian/Stein.lean)
9. Richard Goodman, Vladimir Veselov and Jay Cahill / Apoth3osis Labs. “Statistical Mechanics from a Closure Operator: A Generative Algebraic Substrate.” Author-uploaded technical report, May 2026, §5.3 and §7. [source](https://www.researchgate.net/publication/404361367_Statistical_Mechanics_from_a_Closure_Operator_A_Generative_Algebraic_Substrate) ; DOI [source](https://doi.org/10.13140/RG.2.2.33901.96483)
10. Recognition Encyclopedia. “Masses Mass Genesis Support Symmetry Support Averaged Factorized Load Of Support,” displayed theorem `uniformSiteMeaningLoad_of_supportRHatTransitive`. [source](https://recognitionphysics.org/encyclopedia/masses-mass-genesis-support-symmetry-support-averaged-factorized-load-of-support/)
11. Tarek Mhamdi, Osman Hasan and Sofiène Tahar. “Formalization of Entropy Measures in HOL,” ITP 2011, authors' institutional copy. [source](https://hvg.ece.concordia.ca/Publications/Conferences/ITP2011.pdf)
12. Reynald Affeldt et al. “Formalization of Shannon's Theorems,” ITP 2012 preprint, §3. [source](https://staff.aist.go.jp/reynald.affeldt/documents/affeldt-itp2012-preprint.pdf)
13. GitHub public issue/PR search endpoint, accessed 13 September 2026. [source](https://api.github.com/search/issues?q=equipartition%20repo%3Aleanprover-community%2Fphyslib)
14. Statlean contributors. Score-matching definitions. [source](https://github.com/statopia/statlean4/blob/dd2c4bbc72b7c643e62985d77c84755b31aec9f5/Statlean/ScoreMatching/Basic.lean)
15. Lean physics community. “Physics projects in ITPs.” [source](https://github.com/lean-phys-community/ITPsInPhysicsArchive) ; linked AFP physics search [source](https://www.isa-afp.org/search/?s=physics)
