# Generalized equipartition in Lean

A Lean 4 formalization of classical canonical equipartition, for arbitrary finite dimension and coupled, nonquadratic Hamiltonians:

$$
\beta\langle A\,\partial_jH\rangle=\langle\partial_jA\rangle,
\qquad
\langle x_i\,\partial_jH\rangle=\frac{\delta_{ij}}{\beta}.
$$

For $\beta=(k_BT)^{-1}>0$, the coordinate identity gives $k_BT\delta_{ij}$. Boundary corrections, weaker coordinate regularity, and the vector-field form are included.

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

Integrability of the positive weight gives $Z>0$. The density $w/Z$ defines a Gibbs probability measure, and its integral equals `canonicalExpectation`. Analytic hypotheses must be checked for the chosen Hamiltonian.

## Observables, domains, and consequences

| Result | Proven scope |
| --- | --- |
| Observable identity | The same slice regularity for $H,A$, integrable $AH_jw,A_jw$, and either vanishing weighted traces or integrable $Aw$. |
| Vector-field identity | $\beta\langle X\cdot\nabla H\rangle=\langle\operatorname{div}X\rangle$, with coordinate regularity and absolute integrability of each weighted component and product-rule term. |
| Virial identity | $\langle\sum_jx_j\partial_jH\rangle=d/\beta$, under the coordinate integrability hypotheses. |
| Variable coordinate boundaries | A measurable transverse set with one finite open interval $(a(y),b(y))$ per slice. Interior coordinate derivatives and one-sided traces give $\beta\langle AH_j\rangle_\Omega=\langle A_j\rangle_\Omega-Z_\Omega^{-1}\int(R-L)\,dy$. Endpoints may depend on all transverse coordinates. |
| Arbitrary open domains | Locally differentiable $H,A$, with the closed support of $A$ inside the domain and weighted integrability. Local C¹ regularity and compact support imply the integrability conditions for the unnormalized identity. |
| Cusp example | For $H(x)=|x|$ on $\mathbb R$ and every $\beta>0$, $Z=2/\beta$ and $\langle H\rangle=1/\beta$, with all analytic hypotheses proved. |
| Quadratic energy | If $\partial_iH=2cx_i$, then $\langle cx_i^2\rangle=1/(2\beta)$ under the coordinate hypotheses. For $H(x)=cx^2$ on $\mathbb R$, every analytic condition and $Z=\sqrt{\pi/(\beta c)}$ are proved from $\beta,c>0$. |

Restricted canonical measures require a domain of nonzero measure and an integrable weight. Boundary terms cannot in general be discarded: `BoundaryExample.lean` proves that $H=0$ on $(0,1)$ has $\langle xH'\rangle=0$.

These results concern classical canonical ensembles with Lebesgue measure. General boundary flux on arbitrary domains, manifold or constrained phase-space measures, microcanonical ensembles, quantum systems, and dynamical time averages are outside the formalized scope.

## Build and verify

Pinned versions: Lean **4.28.0**, mathlib **`8f9d9cff6bd728b17a24e163c9402775d9e6a365`**. With `elan` and Python 3:

```sh
lake exe cache get
lake --wfail build
python3 -m unittest discover -s checks -p 'test_*.py'
LEAN_NUM_THREADS=1 python3 checks/check_proofs.py
LEAN_NUM_THREADS=1 lake env leanchecker Equipartition
```

The [verification report](docs/verification.md) records the checks. See the [proof guide](docs/proof-guide.md), [module map](Equipartition/README.md), and [prior-art search](docs/prior-art.md). The search does not establish priority.

Author: **Neil Yuanting Li**. Citation: [CITATION.cff](CITATION.cff). License: [Apache 2.0](LICENSE). Dependency and checker attribution: [NOTICE](NOTICE).
