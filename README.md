# Generalized equipartition in Lean

A Lean 4 formalization of the classical canonical identity

$$
\left\langle x_i\,\partial_j H\right\rangle_\beta
=\frac{\delta_{ij}}{\beta}
=k_B T\,\delta_{ij},
\qquad \beta=(k_BT)^{-1}.
$$

The Hamiltonian may couple coordinates and need not be quadratic. The result describes an equilibrium average: a coordinate multiplied by the corresponding energy derivative has mean $k_BT$; the mixed-coordinate averages are zero. A quadratic energy contribution consequently has mean $k_BT/2$ when the stated analytic conditions hold.

## Statement and assumptions

The phase space is $\mathbb R^d$, represented by `Fin (n + 1) → ℝ`, with $d=n+1\geq1$. For Lebesgue measure, define

$$
w_\beta(x)=e^{-\beta H(x)},\qquad
Z_\beta=\int_{\mathbb R^d}w_\beta(x)\,dx,\qquad
\langle A\rangle_\beta=\frac{\int A(x)w_\beta(x)\,dx}{Z_\beta}.
$$

`generalized_equipartition` assumes:

- $\beta>0$ and an everywhere Fréchet differentiable $H:\mathbb R^d\to\mathbb R$; continuity of its derivative is not required.
- Integrability of $w_\beta$ and $x_i\partial_jH\,w_\beta$.
- $x_iw_\beta\to0$ at both ends of almost every line parallel to coordinate $j$, with respect to Lebesgue measure on the remaining coordinates.

`generalized_equipartition_of_integrable` replaces the last condition with integrability of $x_iw_\beta$. These conditions are hypotheses of the general theorem; the library does not infer them from an arbitrary Hamiltonian. Integrability always means absolute Lebesgue integrability.

Positivity of $Z_\beta$ is proved from integrability of the positive weight. The normalized density defines a Gibbs probability measure, and its integral agrees with `canonicalExpectation`.

## Included results

- The general observable identity $\beta\langle A\partial_jH\rangle_\beta=\langle\partial_jA\rangle_\beta$, with differentiability, weighted integrability, and either boundary or integrability hypotheses.
- Coordinate, temperature, and quadratic-coordinate identities, including an integral formulation against a proved Gibbs probability measure.
- One-dimensional integration by parts with explicit endpoint corrections, on the whole line and finite oriented intervals.
- A complete example $H(x)=cx^2$: for every $\beta,c>0$, all analytic hypotheses are proved and $\langle H\rangle_\beta=1/(2\beta)$. Its partition function is also evaluated.

The proof derives the expectation identities from differentiation, the fundamental theorem of calculus, and Fubini's theorem. It does not assume an integration-by-parts conclusion. This repository treats classical canonical equilibrium on real coordinate spaces; it does not formalize quantum or microcanonical equipartition.

## Build and verify

The project pins Lean **4.28.0** and mathlib commit **`8f9d9cff6bd728b17a24e163c9402775d9e6a365`**. With Lean's `elan` toolchain manager and Python 3 available, run:

```sh
lake exe cache get
lake --wfail build
python3 -m unittest discover -s checks -p 'test_*.py'
LEAN_NUM_THREADS=1 python3 checks/check_proofs.py
LEAN_NUM_THREADS=1 lake env leanchecker Equipartition
```

The GitHub Actions workflow runs a warning-free build, compiled-proof recheck, checker regression tests, and a transitive proof-dependency audit. See the [verification report](docs/verification.md) for the recorded results and exact scope of these checks.

Read the [proof guide](docs/proof-guide.md), [module map](Equipartition/README.md), and [prior-art search](docs/prior-art.md). The search records what was checked; it is not a claim of priority.

Licensed under [Apache 2.0](LICENSE); dependency and checker attribution appears in [NOTICE](NOTICE).
