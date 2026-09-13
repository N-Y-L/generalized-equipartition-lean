# Proof guide

The derivative identities concern classical canonical ensembles with Lebesgue measure. They do not cover constrained or manifold phase-space measures, microcanonical or quantum ensembles, or dynamical time averages.

## Ensemble and regularity

For $d\ge1$ and $H:\mathbb R^d\to\mathbb R$, define

$$
w=e^{-\beta H},\qquad Z_\Omega=\int_\Omega w\,dx,
\qquad\langle A\rangle_\Omega=Z_\Omega^{-1}\int_\Omega Aw\,dx.
$$

All integrability assumptions mean absolute Lebesgue integrability. On a domain of nonzero measure, integrability of the everywhere positive weight implies $Z_\Omega>0$. `gibbsMeasure_isProbabilityMeasure` and `integral_gibbsMeasure` construct the probability measure and identify its integrals with these expectations. The normalization lemmas accept any nonzero base measure; the derivative theorems use Lebesgue measure.

`Fin (n + 1) → ℝ` represents $\mathbb R^{n+1}$. For a selected coordinate $j$, `Fin.insertNth` forms $x(t,y)$ by inserting $t$ into the transverse coordinates $y$. `HasAESliceDeriv j H H_j` means that for almost every $y$, $t\mapsto H(x(t,y))$ is continuous and has derivative $H_j(x(t,y))$ outside a countable set, which may depend on $y$.

The supplied derivative satisfies `HasDerivAt` on these slices. No transverse derivative is required. Continuity and the countable exceptional set are essential: arbitrary almost-everywhere differentiability alone would not justify the fundamental theorem of calculus. The absolute-value example below uses this weaker regularity.

Everywhere Fréchet differentiability implies this slice condition. In that case `partialDeriv j H x` is the Fréchet derivative applied to the coordinate vector $e_j$; no continuity of the derivative is assumed.

## Whole-space integration by parts

Assume $H,A$ satisfy the slice condition in coordinate $j$, with supplied derivatives $H_j,A_j$. Product and chain rules give

$$
\frac{d}{dt}(Aw)(x(t,y))=(A_jw-\beta AH_jw)(x(t,y))
$$

outside the union of the two countable exceptional sets. Suppose $A_jw$ and $AH_jw$ are integrable. Fubini's theorem, through Mathlib's measure-preserving coordinate equivalence, supplies integrability of their difference on almost every slice.

If $Aw$ vanishes at both ends of almost every slice, the whole-line fundamental theorem of calculus gives integral zero. For continuous functions with countably many derivative exceptions, the proof first applies the finite-interval theorem and then takes improper limits.

Alternatively, integrability of $Aw$ supplies integrable slices. The finite-interval fundamental theorem of calculus (FTC) and integrability of the derivative establish finite limits at both infinities; integrability of the function forces both limits to zero. Integrating the slice identities gives

$$
\beta\int AH_jw=\int A_jw.
$$

These are `weighted_slice_identity` and its `_of_integrable` variant. With integrable $w$, their `canonical_slice_identity` counterparts divide by $Z$:

$$
\beta\langle AH_j\rangle=\langle A_j\rangle.
$$

The `weighted_partial_identity` and `canonical_partial_identity` variants use everywhere Fréchet derivatives. The unnormalized and observable identities are algebraically valid for any real $\beta$ whenever their analytic hypotheses hold.

## Coordinate and vector-field identities

For $A(x)=x_i$, the slice derivative is $\delta_{ij}$. Thus, for $\beta\ne0$,

$$
\langle x_iH_j\rangle=\delta_{ij}/\beta.
$$

This is `generalized_equipartition_slices`, or `_slices_of_integrable` with integrable $x_iw$. The `generalized_equipartition` variants use Fréchet derivatives and $\beta>0$. The temperature corollary substitutes $\beta=(k_BT)^{-1}$ for $k_B,T>0$; the Gibbs corollary states the result as an integral against a probability measure.

Apply the observable identity with $A=X_j$ and sum over $j$:

$$
\beta\langle X\cdot\nabla H\rangle=\langle\nabla\cdot X\rangle.
$$

`canonical_vector_identity_slices` uses supplied coordinate derivatives of $H$ and $X_j$; `canonical_vector_identity` uses Fréchet derivatives. Both assume integrability of $w$ and each $X_jw$, $X_jH_jw$, and $(\partial_jX_j)w$, so exchanging finite sums and integrals is justified. They do not require the vector field to be separable.

Summing the diagonal coordinate identities gives $\langle\sum_jx_j\partial_jH\rangle=d/\beta$. The theorem `canonical_virial_identity` assumes $\beta>0$, Fréchet differentiability of $H$, and integrability of $w$, $x_jw$, and $x_j(\partial_jH)w$ for every $j$.

If $\partial_iH=2cx_i$, the diagonal identity gives $\langle cx_i^2\rangle=1/(2\beta)$ under the same coordinate hypotheses. No separability or polynomial form is required for the general identities.

## Domains and boundary terms

### Variable coordinate boundaries

For a measurable transverse set $S$, let

$$
\Omega=\{x(t,y):y\in S,\ a(y)<t<b(y)\},\qquad a(y)<b(y).
$$

The endpoint functions may depend on all transverse coordinates; measurability of both endpoints implies measurability of $\Omega$. Assume the supplied derivatives of $H,A$ exist along the interior slices, the two weighted product-rule terms are integrable on $\Omega$, and the weighted observable has finite one-sided traces $L(y),R(y)$ almost everywhere on $S$.

The improper FTC on each finite interval, followed by Fubini, proves

$$
\beta\int_\Omega AH_jw=\int_\Omega A_jw-\int_S(R-L)\,dy.
$$

This is `weighted_coordinateDomain_identity`. Integrability of the trace difference follows from its equality to the integrable slice integral. Neither endpoint values nor endpoint differentiability are required, so the interior Hamiltonian may diverge towards the boundary.

With integrable $w$ and a nonzero restricted measure, `canonical_coordinateDomain_identity` divides by $Z_\Omega$. For $A=x_i$ and $\beta>0$, `generalized_equipartition_coordinateDomain_boundary` gives

$$
\langle x_iH_j\rangle_\Omega
=\frac{\delta_{ij}}{\beta}
-\frac{\int_S(R-L)\,dy}{\beta Z_\Omega}.
$$

The correction vanishes if the integrated trace difference is zero. This theorem covers one finite interval per selected-coordinate slice; it does not supply a general Gauss–Green theorem or a boundary formula for disconnected or unbounded fibers.

### Open domains

For any open $\Omega$, `weighted_partial_identity_on_open` assumes that $H,A$ are differentiable on $\Omega$, the closed support of $A$ lies in $\Omega$, and all three weighted terms are integrable. The weighted observable is locally zero outside its closed support. Extending its derivative by zero therefore reduces the domain identity to the whole-space proof, without boundary regularity assumptions. Local C¹ regularity and compact support derive the required integrability. The normalized theorem additionally requires integrable $w$ and a nonzero restricted measure. The support condition does not hold for arbitrary coordinate observables on bounded domains.

The one-dimensional library also contains explicit corrections on the whole line and on finite oriented closed intervals.

## Examples

Each example proves its analytic hypotheses from the stated parameters:

- For $H(x)=cx^2$ on $\mathbb R$ and $\beta,c>0$, Gaussian integrability proves the integrability hypotheses. Integration by parts gives $\langle H\rangle=1/(2\beta)$; the Gaussian integral gives $Z=\sqrt{\pi/(\beta c)}$.
- For $H(x)=|x|$ on $\mathbb R$ and $\beta>0$, `laplace_equipartition` gives $\langle H\rangle=1/\beta$ and `laplace_partitionFunction` gives $Z=2/\beta$. Exponential-tail estimates and reflection prove weight and moment integrability. The FTC permits the single derivative exception at zero.
- For $H=0$ on $(0,1)$, $Z=1$, $\langle xH'\rangle=0$, and the trace difference is one. This verifies a nonzero boundary correction.

See the [module map](../Equipartition/README.md) for source files and [verification](verification.md) for recorded checks.

## References

- Kai Chen, Dahai He and Hong Zhao. [“Violation of the virial theorem and generalized equipartition theorem for logarithmic oscillators serving as a thermostat.”](https://www.nature.com/articles/s41598-017-03694-w) *Scientific Reports* 7, 3460 (2017), equation (5) and Methods.
- J. A. S. Lima and A. R. Plastino. [“On the classical energy equipartition theorem.”](https://doi.org/10.1590/S0103-97332000000100019) *Brazilian Journal of Physics* 30(1) (2000).
- Owen G. Jepps, Gary Ayton and Denis J. Evans. [“Microscopic expressions for the thermodynamic temperature.”](https://arxiv.org/html/cond-mat/9906423v1) arXiv:cond-mat/9906423v1 (1999), §§II.3–II.4, equation (7).
- Rossend Rey. [“Generalized equipartition theorem and confining walls.”](https://upcommons.upc.edu/bitstream/handle/2117/28219/1.4903763.pdf) *American Journal of Physics* 83, 539–544 (2015), §§IV–V. DOI: 10.1119/1.4903763.
- Guido Magnano and Beniamino Valsesia. [“On the Generalised Equipartition Law.”](https://arxiv.org/html/2009.02518v2) arXiv:2009.02518v2, §§1–2 (microcanonical formulation).
