# Prior-art review: generalized equipartition

The search completed on 13 September 2026 found no public, inspectable formalization of the general canonical identity

$$
\frac{\int_{\mathbb R^n}x_i\,\partial_jH(x)\,e^{-\beta H(x)}\,dx}
{\int_{\mathbb R^n}e^{-\beta H(x)}\,dx}
=\frac{\delta_{ij}}\beta
$$

for general differentiable Hamiltonians under explicit integrability and boundary hypotheses. Mathlib formalizes integration by parts; Statlean formalizes Gaussian Stein identities. The negative search does not establish absence of prior work. This repository formalizes a classical result and makes no priority claim.

## Target and mathematical scope

The target uses Lebesgue measure on Cartesian phase space and a finite, nonzero partition function. It concerns canonical expectations, not dynamical time averages, microcanonical or quantum ensembles, information-theoretic asymptotic equipartition, or equal shares imposed by finite symmetry. Chen, He and Zhao state the identity in equation (5), distinguish canonical from time averages, and discuss failure of normalizability. The paper does not provide a proof-assistant formalization. [1]

The proof integrates $\partial_j(x_i e^{-\beta H(x)})$, justifies the iterated integrals and boundary limits, and divides by the partition function. Its analytic ingredients are differentiation, Fubini’s theorem, and the fundamental theorem of calculus. Lima and Plastino discuss classical homogeneity variants and convergence conditions. [2]

## Inspected formalization sources

| Source and inspected version | Finding | Relation to this project |
|---|---|---|
| **PhysLean / Physlib**, public master snapshot `c76e3ccab04eacb69a126ca5c021b0788d513292` | `HEPLean/PhysLean` redirects to `leanprover-community/physlib`. Whole-tree searches found no `equipartition` or `virial` occurrence. Canonical-ensemble and ideal-gas sources were inspected. | Adjacent statistical-mechanics results; no exact target found. [3–5] |
| **Mathlib**, master snapshot `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`; also pinned snapshot `8f9d9cff6bd728b17a24e163c9402775d9e6a365` | `equipartition` matches concern finite combinatorial partitions. General improper integration by parts is implemented. | Existing analytic foundation for the Gibbs specialization. [6–7] |
| **Statlean**, snapshot `dd2c4bbc72b7c643e62985d77c84755b31aec9f5` | `stein_identity` proves $E_\gamma[xh]=E_\gamma[h']$ under differentiability and Gaussian $L^2$ conditions. `gaussian_ibp_coord` gives a coordinatewise identity for a standard product Gaussian and Lipschitz observables. | Analytic near match restricted to Gaussian/quadratic Hamiltonians. [8] |
| **Goodman, Veselov and Cahill**, May 2026 technical report | Theorem 5.3 gives equal expected closure-energy shares among finite Boolean forced coordinates by coordinate-swap symmetry. The report claims Lean verification and uses rational Padé weights. | Finite symmetry theorem, without an exact real exponential. No `github` URL appears in the accessible report text. [9] |
| **Recognition Physics**, displayed Lean theorem | `uniformSiteMeaningLoad_of_supportRHatTransitive` derives equal occupied-site loads from a transitive load-preserving action. | Discrete symmetry theorem, without Gibbs integration or derivatives. [10] |
| **HOL and Coq information-theory work** | Formalizations of the asymptotic equipartition property for typical sequences and source coding. | A different meaning of “equipartition.” [11–12] |

### Physlib details

`Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean` defines Boltzmann weights, partition functions, normalized measures and mean energy. `Lemmas.lean` includes `meanEnergy_eq_ratio_of_integrals` and temperature/partition-function differentiation identities, but no coordinatewise integration-by-parts identity was found. `MicroCanonicalEnsemble/IdealGas.lean` computes the Gaussian ideal-gas partition function and derives the ideal-gas law. The public GitHub issue/PR query `equipartition repo:leanprover-community/physlib` returned `total_count: 0` and `incomplete_results: false` on the search date; it does not cover unnamed ongoing work or all branches. [3–5,13]

### Mathlib and Statlean details

Mathlib's `MeasureTheory.integral_mul_deriv_eq_deriv_mul` establishes whole-line integration by parts with explicit endpoint limits. `integral_mul_deriv_eq_deriv_mul_of_integrable` derives the zero-boundary form from product integrability. Mathlib also contains Gaussian integrability, moment and normalization results. [6–7]

Statlean's `Gaussian/Stein.lean` applies Mathlib's integration-by-parts theorem to the standard Gaussian density; its multidimensional result uses coordinate decomposition and Fubini. The inspected `Statlean/ScoreMatching/Basic.lean` defines scores and losses but does not establish the general Gibbs integration-by-parts identity. [8,14]

## Dated search record

All searches and source inspections below were performed on **2026-09-13**. Substantive near matches were opened or inspected in source.

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

Code may use other names; indexes may lag; private work and unmerged branches may be invisible. No exhaustive semantic search or build of all proof-assistant libraries was performed. The Mathlib, Physlib and Statlean snapshots were downloaded for source inspection; their builds were not reproduced in this review. Recognition Physics's displayed source was inspected but not built. The finite-symmetry report's claimed Lean verification was not independently confirmed.

## Sources

1. Kai Chen, Dahai He and Hong Zhao. [“Violation of the virial theorem and generalized equipartition theorem for logarithmic oscillators serving as a thermostat.”](https://www.nature.com/articles/s41598-017-03694-w) *Scientific Reports* 7, 3460 (14 June 2017), equation (5) and Methods.
2. J. A. S. Lima and A. R. Plastino. [“On the classical energy equipartition theorem.”](https://www.scielo.br/j/bjp/a/VkxF5CrJpqbVqfmFNkXcGJp/?lang=en) *Brazilian Journal of Physics* 30(1), March 2000. [DOI](https://doi.org/10.1590/S0103-97332000000100019).
3. Physlib community. [Repository and rename/merge description, inspected snapshot](https://github.com/leanprover-community/physlib/tree/c76e3ccab04eacb69a126ca5c021b0788d513292).
4. Physlib community. [Canonical-ensemble definitions](https://github.com/leanprover-community/physlib/blob/c76e3ccab04eacb69a126ca5c021b0788d513292/Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean) and [identities](https://github.com/leanprover-community/physlib/blob/c76e3ccab04eacb69a126ca5c021b0788d513292/Physlib/StatisticalMechanics/CanonicalEnsemble/Lemmas.lean).
5. Physlib community. [Ideal-gas partition function and equation of state](https://github.com/leanprover-community/physlib/blob/c76e3ccab04eacb69a126ca5c021b0788d513292/Physlib/StatisticalMechanics/MicroCanonicalEnsemble/IdealGas.lean).
6. Mathlib community. [Improper integration and integration by parts](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean).
7. Mathlib community. [Finite combinatorial equipartitions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Partition/Equipartition.html) and [Gaussian integrals](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/Probability/Distributions/Gaussian/Real.lean).
8. Statlean contributors. [Gaussian Stein identities](https://github.com/statopia/statlean4/blob/dd2c4bbc72b7c643e62985d77c84755b31aec9f5/Statlean/Gaussian/Stein.lean), lines 23 and 426.
9. Richard Goodman, Vladimir Veselov and Jay Cahill / Apoth3osis Labs. [“Statistical Mechanics from a Closure Operator: A Generative Algebraic Substrate.”](https://www.researchgate.net/publication/404361367_Statistical_Mechanics_from_a_Closure_Operator_A_Generative_Algebraic_Substrate) Author-uploaded technical report, May 2026, §5.3 and §7. [DOI](https://doi.org/10.13140/RG.2.2.33901.96483).
10. Recognition Encyclopedia. [“Masses Mass Genesis Support Symmetry Support Averaged Factorized Load Of Support,”](https://recognitionphysics.org/encyclopedia/masses-mass-genesis-support-symmetry-support-averaged-factorized-load-of-support/) displayed theorem `uniformSiteMeaningLoad_of_supportRHatTransitive`.
11. Tarek Mhamdi, Osman Hasan and Sofiène Tahar. [“Formalization of Entropy Measures in HOL.”](https://hvg.ece.concordia.ca/Publications/Conferences/ITP2011.pdf) ITP 2011, authors' institutional copy.
12. Reynald Affeldt et al. [“Formalization of Shannon's Theorems.”](https://staff.aist.go.jp/reynald.affeldt/documents/affeldt-itp2012-preprint.pdf) ITP 2012 preprint, §3.
13. GitHub. [Public Physlib issue/PR search for `equipartition`](https://api.github.com/search/issues?q=equipartition%20repo%3Aleanprover-community%2Fphyslib), accessed 13 September 2026.
14. Statlean contributors. [Score-matching definitions](https://github.com/statopia/statlean4/blob/dd2c4bbc72b7c643e62985d77c84755b31aec9f5/Statlean/ScoreMatching/Basic.lean).
15. Lean physics community. [“Physics projects in ITPs”](https://github.com/lean-phys-community/ITPsInPhysicsArchive) and its linked [AFP physics search](https://www.isa-afp.org/search/?s=physics).
