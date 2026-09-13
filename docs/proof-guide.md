# Proof guide

## Statement

Let $d\geq1$, let $H:\mathbb R^d\to\mathbb R$ be everywhere Fréchet differentiable, and let $\beta>0$. Write

$$
w(x)=e^{-\beta H(x)},\qquad Z=\int w(x)\,dx,
\qquad \langle A\rangle=Z^{-1}\int A(x)w(x)\,dx.
$$

All integrals use Lebesgue measure. Integrability of $w$ implies $Z>0$, since $w$ is everywhere positive and Lebesgue measure is nonzero. The density $w/Z$ defines a probability measure (`gibbsMeasure_isProbabilityMeasure`), whose integral equals `canonicalExpectation` (`integral_gibbsMeasure`).

The main theorem is

$$
\langle x_i\partial_jH\rangle=\delta_{ij}/\beta.
$$

For each pair $i,j$, assume integrability of $w$ and $x_i\partial_jH\,w$, together with either:

- $x_iw\to0$ at both ends of almost every coordinate-$j$ line, with respect to Lebesgue measure on the transverse coordinates; or
- integrability of $x_iw$ on the whole space.

All integrability requirements are absolute. The Hamiltonian may couple coordinates and need not be quadratic; its derivative need not be continuous.

The Lean domain `Fin (n + 1) → ℝ` represents $\mathbb R^{n+1}$. `partialDeriv j H x` is the Fréchet derivative of $H$ at $x$ applied to the coordinate unit vector $e_j$.

## The observable identity

For an everywhere Fréchet differentiable observable $A$, the product and chain rules give

$$
\partial_j(Aw)=(\partial_jA)w-\beta A(\partial_jH)w.
$$

Assume $(\partial_jA)w$ and $A(\partial_jH)w$ are integrable, and that $Aw$ either vanishes at both ends of almost every coordinate-$j$ line or is integrable globally. The derivative above is integrable and has integral zero, giving

$$
\beta\int A(\partial_jH)w=\int(\partial_jA)w.
$$

These are `weighted_partial_identity` and `weighted_partial_identity_of_integrable`, valid for any $\beta\in\mathbb R$. If $w$ is integrable, division by $Z>0$ gives the `canonical_partial_identity` variants:

$$
\beta\langle A\partial_jH\rangle=\langle\partial_jA\rangle.
$$

## Why the derivative integrates to zero

`Fin.insertNth` forms $x(t,y)$ by inserting $t\in\mathbb R$ into coordinate $j$ of $y\in\mathbb R^{d-1}$. Its derivative in $t$ is $e_j$, so

$$
\frac{d}{dt}(Aw)(x(t,y))=\partial_j(Aw)(x(t,y)).
$$

Mathlib's measure-preserving coordinate equivalence identifies $\mathbb R^d$ with $\mathbb R\times\mathbb R^{d-1}$. Fubini gives integrability of the derivative on almost every slice and expresses the full integral as an iterated integral.

Under the explicit boundary hypothesis, the whole-line fundamental theorem of calculus gives

$$
\int_{\mathbb R}\partial_j(Aw)(x(t,y))\,dt=0-0=0
$$

for almost every $y$. The union of the exceptional null sets for integrability and the two limits is null; integrating the slice identities gives the result.

If $Aw$ is integrable globally, Fubini also gives its integrability on almost every slice. Mathlib's whole-line theorem for an integrable function with integrable derivative makes each derivative integral zero. The two arguments are `integral_eq_zero_of_slice_derivative` and its `_of_integrable` variant.

## Coordinate and energy consequences

Set $A(x)=x_i$, with $\partial_jA=\delta_{ij}$. Then $\beta\int x_i\partial_jH\,w=\delta_{ij}Z$. Division by $\beta Z>0$ proves generalized equipartition. For $k_B,T>0$, substitution of $\beta=(k_BT)^{-1}$ gives $k_BT\delta_{ij}$.

`generalized_equipartition_gibbs` gives the coordinate identity as a Gibbs integral and asserts that the measure is a probability measure. It uses the coordinate integrability hypothesis. Under that same hypothesis, if $\partial_iH=2cx_i$ everywhere, `quadratic_coordinate_equipartition` gives $\langle cx_i^2\rangle=1/(2\beta)$.

For $H(x)=cx^2$ on $\mathbb R$ and $\beta,c>0$, Gaussian integrability proves all analytic hypotheses. Integration by parts gives $\langle H\rangle=1/(2\beta)$; the Gaussian integral gives $Z=\sqrt{\pi/(\beta c)}$.

## Boundary corrections

On an oriented finite interval, the exact identity retains the boundary term:

$$
\beta\int_a^b AH'w=\int_a^b A'w-\bigl(A(b)w(b)-A(a)w(a)\bigr).
$$

`canonical_interval_identity` assumes ordinary derivatives at every point of the closed interval between the endpoints and absolute integrability of both integrands there. The whole-line theorem `canonical_identity_with_boundary` instead assumes finite limits $\ell_\pm=\lim_{x\to\pm\infty}A(x)w(x)$ and subtracts $\ell_+-\ell_-$.

See [verification](verification.md) for the proof checks and [prior art](prior-art.md) for the search record.
