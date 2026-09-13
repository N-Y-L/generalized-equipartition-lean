# Generalized equipartition in Lean

A Lean 4 formalization of classical canonical equipartition in arbitrary finite dimension, including coupled and nonquadratic Hamiltonians:

$$
\beta\langle A\,\partial_jH\rangle=\langle\partial_jA\rangle,
\qquad
\langle x_i\,\partial_jH\rangle=\frac{\delta_{ij}}{\beta}.
$$

Each identity requires regularity, integrability, and boundary conditions. For $\beta=(k_BT)^{-1}>0$, the coordinate identity gives $k_BT\delta_{ij}$.

## Whole-space theorem

On $\mathbb R^d$, $d\ge1$, write

$$
w(x)=e^{-\beta H(x)},\qquad Z=\int w(x)\,dx,
\qquad\langle A\rangle=Z^{-1}\int A(x)w(x)\,dx.
$$

`generalized_equipartition_slices` assumes, for the chosen coordinate pair $i,j$:

- $\beta\ne0$; $H$ is continuous on almost every coordinate-$j$ line and has the supplied derivative $H_j$ outside a countable set on each such line.
- Absolute integrability of $w$ and $x_iH_jw$.
- $x_iw\to0$ at both ends of almost every such line.

It proves $\langle x_iH_j\rangle=\delta_{ij}/\beta$. The `_of_integrable` variant replaces the last assumption with integrability of $x_iw$. No transverse differentiability, separability, or polynomial form is required. The simpler `generalized_equipartition` variants use an everywhere Fréchet differentiable $H$ and $\beta>0$.

Integrability of the positive weight gives $Z>0$. The density $w/Z$ defines a Gibbs probability measure, whose integral agrees with `canonicalExpectation`.

## Further results

The library also proves observable, vector-field, and virial identities; boundary corrections for variable finite coordinate intervals; and identities on arbitrary open domains for supported observables. The [proof guide](docs/proof-guide.md) gives each statement and its assumptions.

Examples prove all analytic hypotheses for $H(x)=cx^2$ with $\beta,c>0$ and $H(x)=\lvert x\rvert$ with $\beta>0$. A uniform interval example verifies a nonzero boundary correction. General Hamiltonians require separate proofs of the analytic hypotheses.

## Build and verify

Pinned versions: Lean **4.28.0**, mathlib **`8f9d9cff6bd728b17a24e163c9402775d9e6a365`**. With `elan` and Python 3:

```sh
lake exe cache get
lake --wfail build
python3 -m unittest discover -s checks -p 'test_*.py'
LEAN_NUM_THREADS=1 python3 checks/check_proofs.py
LEAN_NUM_THREADS=1 lake env leanchecker Equipartition
```

The [verification report](docs/verification.md) records the checks and their limitations. The [module map](Equipartition/README.md) lists source files and theorems; the [documentation index](docs/README.md) links the remaining documentation.

Citation: [CITATION.cff](CITATION.cff). License: [Apache 2.0](LICENSE). Dependency and checker attribution: [NOTICE](NOTICE).
