# Proof guide

## Canonical equilibrium and the theorem

Let $d\geq1$, let $H:\mathbb R^d\to\mathbb R$ be everywhere Fréchet differentiable, and let $\beta>0$. Write

$$
w(x)=e^{-\beta H(x)},\qquad Z=\int w(x)\,dx,
\qquad \langle A\rangle=Z^{-1}\int A(x)w(x)\,dx.
$$

All integrals in the multivariate results use Lebesgue measure. If $w$ is integrable, then $Z>0$: the exponential is strictly positive everywhere and Lebesgue measure is nonzero. Thus $w/Z$ defines a probability density. `gibbsMeasure_isProbabilityMeasure` proves normalization, and `integral_gibbsMeasure` identifies its integral with `canonicalExpectation`.

The main theorem is

$$
\langle x_i\partial_jH\rangle=\delta_{ij}/\beta.
$$

Besides differentiability and integrability of $w$, it requires integrability of $x_i\partial_jH\,w$ and a condition eliminating the boundary term. There are two sufficient alternatives: vanishing of $x_iw$ at both ends of almost every coordinate-$j$ line, or integrability of $x_iw$ on the whole space. All these integrability requirements are absolute. No assumption of coordinate independence, a separable Hamiltonian, or quadratic energy is used.

The Lean domain `Fin (n + 1) → ℝ` represents every positive finite dimension. `partialDeriv j H x` is the Fréchet derivative of $H$ at $x$ applied to the coordinate unit vector $e_j$, rather than an independently supplied function.

## The observable identity

The proof first treats a general differentiable observable $A$. The product and chain rules give

$$
\partial_j(Aw)=(\partial_jA)w-\beta A(\partial_jH)w.
$$

Assume both terms on the right are integrable. Then $\partial_j(Aw)$ is integrable. The crucial analytic step is to prove its integral is zero under either boundary condition. Integrating and rearranging yields

$$
\beta\int A(\partial_jH)w=\int(\partial_jA)w.
$$

This is `weighted_partial_identity`, or `weighted_partial_identity_of_integrable`. Neither unnormalized identity requires $\beta>0$: the sign restriction belongs to the physical equipartition statement. Normalization additionally requires integrability of the weight. Dividing by the positive partition function gives the corresponding `canonical_partial_identity` variants.

## Why the derivative integrates to zero

For a chosen coordinate $j$, `Fin.insertNth` forms $x(t,y)$ by inserting $t\in\mathbb R$ into the transverse coordinate vector $y\in\mathbb R^{d-1}$. Its derivative with respect to $t$ is $e_j$. Composing with the Fréchet derivative therefore proves

$$
\frac{d}{dt}(Aw)(x(t,y))=\partial_j(Aw)(x(t,y)).
$$

Mathlib's measure-preserving coordinate equivalence identifies $\mathbb R^d$ with $\mathbb R\times\mathbb R^{d-1}$. Fubini supplies integrability of the derivative on almost every slice and exchanges the full integral for an iterated integral.

Under the explicit boundary hypothesis, the whole-line fundamental theorem of calculus gives

$$
\int_{\mathbb R}\partial_j(Aw)(x(t,y))\,dt=0-0=0
$$

for almost every $y$. The exceptional sets from slice integrability and the two limits remain null when combined. Integrating these zero slice integrals proves the required full-space identity.

Alternatively, if $Aw$ is integrable globally, Fubini also supplies its integrability on almost every slice. Mathlib's whole-line theorem for an integrable function with integrable derivative proves that each such derivative integral is zero. This establishes the integrability variant without a separate boundary assumption. These arguments are implemented in `integral_eq_zero_of_slice_derivative` and its `_of_integrable` variant.

## Coordinate and energy consequences

Set $A(x)=x_i$. Its derivative is $\partial_jA=\delta_{ij}$, so the observable identity becomes $\beta\int x_i\partial_jH\,w=\delta_{ij}Z$. Dividing by $\beta Z$ proves generalized equipartition. Substituting $\beta=(k_BT)^{-1}$ gives $k_BT\delta_{ij}$.

`generalized_equipartition_gibbs` states the coordinate identity directly as an integral against the Gibbs measure and includes its probability property in the conclusion. If $\partial_iH=2cx_i$, then `quadratic_coordinate_equipartition` proves that the energy contribution $cx_i^2$ has mean $1/(2\beta)$, while the other coordinates may have nonquadratic energy. Its analytic hypotheses remain explicit.

The separate one-dimensional example $H(x)=cx^2$ discharges all derivatives and integrability conditions for $\beta,c>0$ using Gaussian integrability. Integration by parts proves the energy expectation. The Gaussian integral supplies the separate formula $Z=\sqrt{\pi/(\beta c)}$.

## Boundary corrections and verification

On an oriented finite interval, the exact identity retains the boundary term:

$$
\beta\int_a^b AH'w=\int_a^b A'w-\bigl(A(b)w(b)-A(a)w(a)\bigr).
$$

`canonical_interval_identity` assumes the stated derivatives on the closed interval between the endpoints and integrability of both displayed integrands. The whole-line boundary theorem likewise permits finite, nonzero limits at infinity. These results explain precisely where the zero-boundary equipartition formula applies.

See [verification](verification.md) for compilation, proof rechecking, and the audit of transitive axiom dependencies. See the [prior-art search](prior-art.md) for the separate search record and its limitations.
