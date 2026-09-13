# Proof guide

## Ensemble and regularity

For $d\ge1$ and $H:\mathbb R^d\to\mathbb R$, define

$$
w=e^{-\beta H},\qquad Z_\Omega=\int_\Omega w\,dx,
\qquad\langle A\rangle_\Omega=Z_\Omega^{-1}\int_\Omega Aw\,dx.
$$

All integrability assumptions mean absolute Lebesgue integrability. On a domain of nonzero measure, integrability of the everywhere positive weight implies $Z_\Omega>0$. `gibbsMeasure_isProbabilityMeasure` and `integral_gibbsMeasure` construct the probability measure and identify its integrals with these expectations. The normalization lemmas accept any nonzero base measure; the derivative theorems use Lebesgue measure.

`Fin (n + 1) → ℝ` represents $\mathbb R^{n+1}$. For a selected coordinate $j$, `Fin.insertNth` forms $x(t,y)$ by inserting $t$ into the transverse coordinates $y$. `HasAESliceDeriv j H H_j` means that for almost every $y$, $t\mapsto H(x(t,y))$ is continuous and has derivative $H_j(x(t,y))$ outside a countable set, which may depend on $y$.

The supplied derivative is linked to actual `HasDerivAt` statements. No derivative in a transverse direction is required. Continuity and the countable exceptional set are substantive conditions: arbitrary almost-everywhere differentiability alone would not justify the fundamental theorem of calculus. The absolute-value function is an explicit cusp witness.

Everywhere Fréchet differentiability implies this slice condition. In that case `partialDeriv j H x` is the Fréchet derivative applied to the coordinate vector $e_j$; no continuity of the derivative is assumed.

## Whole-space integration by parts

Product and chain rules along a regular slice give

$$
\frac{d}{dt}(Aw)(x(t,y))=(A_jw-\beta AH_jw)(x(t,y))
$$

outside the union of the two countable exceptional sets. Suppose $A_jw$ and $AH_jw$ are integrable. Fubini's theorem, through Mathlib's measure-preserving coordinate equivalence, supplies integrability of their difference on almost every slice.

If $Aw$ vanishes at both ends of almost every slice, the whole-line fundamental theorem of calculus gives integral zero. For continuous functions with countably many derivative exceptions, the proof first applies the finite-interval theorem and then takes improper limits.

Alternatively, integrability of $Aw$ supplies integrable slices. Finite-interval FTC and integrability of the derivative establish finite limits at both infinities; integrability of the function forces both limits to zero. Integrating the slice identities gives

$$
\beta\int AH_jw=\int A_jw.
$$

These are `weighted_slice_identity` and its `_of_integrable` variant. With integrable $w$, their `canonical_slice_identity` counterparts divide by $Z$:

$$
\beta\langle AH_j\rangle=\langle A_j\rangle.
$$

The `weighted_partial_identity` and `canonical_partial_identity` variants use everywhere Fréchet derivatives. The unnormalized and observable identities are algebraically valid for any real $\beta$ whenever their analytic hypotheses hold.

## Coordinate and vector-field laws

For $A(x)=x_i$, the slice derivative is $\delta_{ij}$. Thus, for $\beta\ne0$,

$$
\langle x_iH_j\rangle=\delta_{ij}/\beta.
$$

This is `generalized_equipartition_slices`, or `_slices_of_integrable` with integrable $x_iw$. The original `generalized_equipartition` variants use Fréchet derivatives and $\beta>0$. The temperature corollary substitutes $\beta=(k_BT)^{-1}$ for $k_B,T>0$; the Gibbs corollary states the result as an integral against a probability measure.

Apply the observable identity with $A=X_j$ and sum over $j$:

$$
\beta\langle X\cdot\nabla H\rangle=\langle\nabla\cdot X\rangle.
$$

`canonical_vector_identity_slices` uses supplied coordinate derivatives of $H$ and $X_j$; `canonical_vector_identity` uses Fréchet derivatives. Both assume integrability of each $X_jw$, $X_jH_jw$, and $(\partial_jX_j)w$, so exchanging finite sums and integrals is justified. They do not require the vector field to be separable. Summing the diagonal coordinate identities gives the canonical virial identity $\langle\sum_jx_j\partial_jH\rangle=d/\beta$.

If $\partial_iH=2cx_i$, the diagonal law gives $\langle cx_i^2\rangle=1/(2\beta)$. For $H(x)=cx^2$ on $\mathbb R$ and $\beta,c>0$, Gaussian integrability discharges every analytic hypothesis; the Gaussian integral gives $Z=\sqrt{\pi/(\beta c)}$.

For the nonsmooth, nonquadratic Hamiltonian $H(x)=|x|$ and every $\beta>0$, `laplace_equipartition` proves $\langle H\rangle=1/\beta$ using the off-countable FTC. Exponential-tail estimates and reflection prove weight and moment integrability; `laplace_partitionFunction` gives $Z=2/\beta$. The only derivative exception is the cusp at zero.

## Domains and boundary terms

For a measurable transverse set $S$, let

$$
\Omega=\{x(t,y):y\in S,\ a(y)<t<b(y)\},\qquad a(y)<b(y).
$$

The endpoint functions may depend on all transverse coordinates; measurability of both endpoints implies measurability of $\Omega$. Assume the supplied derivatives of $H,A$ exist along the interior slices, the two weighted product-rule terms are integrable on $\Omega$, and the weighted observable has finite one-sided traces $L(y),R(y)$ almost everywhere on $S$.

The improper FTC on each finite interval, followed by Fubini, proves

$$
\beta\int_\Omega AH_jw=\int_\Omega A_jw-\int_S(R-L)\,dy.
$$

`weighted_coordinateDomain_identity` derives this flux; it does not assume an integration-by-parts identity. Integrability of the trace difference follows from its equality to the integrable slice integral. Neither endpoint values nor endpoint differentiability are required, so the interior Hamiltonian may diverge towards the boundary.

With integrable $w$ and a nonzero restricted measure, `canonical_coordinateDomain_identity` divides by $Z_\Omega$. For $A=x_i$ and $\beta>0$, `generalized_equipartition_coordinateDomain_boundary` gives

$$
\langle x_iH_j\rangle_\Omega
=\frac{\delta_{ij}}{\beta}
-\frac{\int_S(R-L)\,dy}{\beta Z_\Omega}.
$$

The zero-flux consequence requires only that the integrated trace difference vanish. This domain theorem covers one finite interval per selected-coordinate slice; it does not supply a general surface-integral theorem for disconnected or unbounded fibers.

For any open $\Omega$, `weighted_partial_identity_on_open` assumes that $H,A$ are differentiable on $\Omega$, the closed support of $A$ lies in $\Omega$, and all three weighted terms are integrable. The weighted observable is locally zero outside its closed support. Extending its derivative by zero therefore reduces the domain identity to the whole-space proof, without boundary regularity assumptions. Local C¹ regularity and compact support derive the required integrability. The normalized theorem additionally requires integrable $w$ and a nonzero restricted measure. The support condition does not hold for arbitrary coordinate observables on bounded domains.

The one-dimensional library also contains explicit corrections on the whole line and on finite oriented closed intervals. The Hamiltonian $H=0$ on $(0,1)$ illustrates the necessity of the correction: $Z=1$, the coordinate moment is zero, and the trace difference is one.

## Scope

The formalization covers classical canonical integration by parts with the preceding domain, regularity, integrability, and trace hypotheses. Couplings and nonquadratic energies are unrestricted within those hypotheses. It does not formalize general Gauss–Green boundary geometry, constrained or manifold phase-space measures, microcanonical or quantum equipartition, or equivalence of ensemble and dynamical time averages.

See [verification](verification.md) and the [prior-art review](prior-art.md).
