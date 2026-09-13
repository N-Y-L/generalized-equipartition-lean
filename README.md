# Generalized equipartition in Lean

A Lean 4 formalization of the classical canonical identity

$$
\left\langle x_i\,\partial_j H\right\rangle_\beta
=\frac{\delta_{ij}}{\beta}
=k_B T\,\delta_{ij},
\qquad \beta=(k_BT)^{-1}.
$$

The Hamiltonian may couple coordinates and need not be quadratic. Under the hypotheses below, $x_i\partial_iH$ has equilibrium mean $k_BT$, and $x_i\partial_jH$ has mean zero for $i\ne j$.

## Statement and assumptions

The phase space is $\mathbb R^d$, represented by `Fin (n + 1) → ℝ`, with $d=n+1\geq1$. For Lebesgue measure, define

$$
w_\beta(x)=e^{-\beta H(x)},\qquad
Z_\beta=\int_{\mathbb R^d}w_\beta(x)\,dx,\qquad
\langle A\rangle_\beta=\frac{\int A(x)w_\beta(x)\,dx}{Z_\beta}.
$$

For a fixed coordinate pair $i,j$, `generalized_equipartition` assumes:

- $\beta>0$ and an everywhere Fréchet differentiable $H:\mathbb R^d\to\mathbb R$; continuity of its derivative is not required.
- Integrability of $w_\beta$ and $x_i\partial_jH\,w_\beta$.
- $x_iw_\beta\to0$ at both ends of almost every line parallel to coordinate $j$, with respect to Lebesgue measure on the remaining coordinates.

`generalized_equipartition_of_integrable` replaces the boundary condition with integrability of $x_iw_\beta$. All integrability hypotheses mean absolute Lebesgue integrability and must be verified for the chosen Hamiltonian.

Integrability of the positive weight implies $Z_\beta>0$. The density $w_\beta/Z_\beta$ defines a Gibbs probability measure whose integral equals `canonicalExpectation`.

## Included results

- The observable identity $\beta\langle A\partial_jH\rangle_\beta=\langle\partial_jA\rangle_\beta$, under differentiability, weighted integrability, and either vanishing boundary limits or integrability of $Aw_\beta$.
- Formulations in terms of temperature and the Gibbs measure. If $\partial_iH=2cx_i$, then $\langle cx_i^2\rangle_\beta=1/(2\beta)$ under the coordinate integrability hypotheses.
- One-dimensional integration by parts with explicit endpoint corrections, on the whole line and finite oriented intervals.
- For $H(x)=cx^2$ on $\mathbb R$ and every $\beta,c>0$, all analytic hypotheses are proved, $\langle H\rangle_\beta=1/(2\beta)$, and $Z_\beta=\sqrt{\pi/(\beta c)}$.

The proof uses differentiation, the fundamental theorem of calculus, and Fubini's theorem. Its scope is classical canonical equilibrium on full real coordinate spaces; quantum and microcanonical equipartition are excluded.

## Build and verify

The project pins Lean **4.28.0** and mathlib commit **`8f9d9cff6bd728b17a24e163c9402775d9e6a365`**. With Lean's `elan` toolchain manager and Python 3 available, run:

```sh
lake exe cache get
lake --wfail build
python3 -m unittest discover -s checks -p 'test_*.py'
LEAN_NUM_THREADS=1 python3 checks/check_proofs.py
LEAN_NUM_THREADS=1 lake env leanchecker Equipartition
```

The GitHub Actions workflow specifies the same checks. The [verification report](docs/verification.md) records local results and the scope of verification.

See the [proof guide](docs/proof-guide.md), [module map](Equipartition/README.md), and [prior-art search](docs/prior-art.md). The search does not establish priority.

Author: **Neil Yuanting Li**. Citation metadata: [CITATION.cff](CITATION.cff). Licensed under [Apache 2.0](LICENSE); dependency and checker attribution: [NOTICE](NOTICE).
