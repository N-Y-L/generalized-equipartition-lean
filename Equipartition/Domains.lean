import Equipartition.Multivariate
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Canonical integration by parts on open domains

The Hamiltonian and observable need be differentiable only in the domain.
The observable's closed support lies inside the domain; integrability permits
unbounded support. No regularity of the domain's boundary is required.
-/

open MeasureTheory Filter
open scoped Topology

namespace Equipartition

/-- A supported coordinate derivative has zero integral on a measurable domain.
The derivative is required only at points in the domain. -/
theorem integralOn_eq_zero_of_supported_slice_derivative {n : ℕ}
    (j : Fin (n+1)) (Ω : Set (Fin (n+1) → ℝ)) (hΩ : MeasurableSet Ω)
    (f g : (Fin (n+1) → ℝ) → ℝ)
    (hsupport : tsupport f ⊆ Ω)
    (hf : IntegrableOn f Ω) (hg : IntegrableOn g Ω)
    (hd : ∀ y t, j.insertNth t y ∈ Ω →
      HasDerivAt (fun s => f (j.insertNth s y)) (g (j.insertNth t y)) t) :
    ∫ x in Ω, g x = 0 := by
  have hfi : Integrable f :=
    (integrableOn_iff_integrable_of_support_subset
      ((subset_tsupport f).trans hsupport)).mp hf
  have hgi : Integrable (Ω.indicator g) := (integrable_indicator_iff hΩ).mpr hg
  have hdi : ∀ y t, HasDerivAt (fun s => f (j.insertNth s y))
      (Ω.indicator g (j.insertNth t y)) t := by
    intro y t
    by_cases hx : j.insertNth t y ∈ Ω
    · simpa only [Set.indicator_of_mem hx] using hd y t hx
    · have hzero := HasFDerivAt.of_notMem_tsupport ℝ
        (fun h => hx (hsupport h))
      simpa only [Set.indicator_of_notMem hx, ContinuousLinearMap.zero_apply]
        using hzero.comp_hasDerivAt t (hasDerivAt_insertNth j y t)
  have hz := integral_eq_zero_of_slice_derivative_of_integrable j f (Ω.indicator g)
    hfi hgi hdi
  rwa [integral_indicator hΩ] at hz

/-- Canonical integration by parts on an arbitrary open domain, with the
observable's closed support contained in the domain. -/
theorem weighted_partial_identity_on_open {n : ℕ} (j : Fin (n+1))
    (Ω : Set (Fin (n+1) → ℝ)) (hΩ : IsOpen Ω)
    (β : ℝ) (H A : (Fin (n+1) → ℝ) → ℝ)
    (hH : DifferentiableOn ℝ H Ω) (hA : DifferentiableOn ℝ A Ω)
    (hsupport : tsupport A ⊆ Ω)
    (hleft : IntegrableOn (fun x => A x * partialDeriv j H x * boltzmannWeight β H x) Ω)
    (hright : IntegrableOn (fun x => partialDeriv j A x * boltzmannWeight β H x) Ω)
    (hobs : IntegrableOn (fun x => A x * boltzmannWeight β H x) Ω) :
    β * (∫ x in Ω, A x * partialDeriv j H x * boltzmannWeight β H x) =
      ∫ x in Ω, partialDeriv j A x * boltzmannWeight β H x := by
  have hd : ∀ y t, j.insertNth t y ∈ Ω → HasDerivAt
      (fun s => A (j.insertNth s y) * boltzmannWeight β H (j.insertNth s y))
      (partialDeriv j A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y) -
        β * (A (j.insertNth t y) * partialDeriv j H (j.insertNth t y) *
          boltzmannWeight β H (j.insertNth t y))) t := by
    intro y t hx
    exact hasDerivAt_observable_boltzmann
      ((hH.differentiableAt (hΩ.mem_nhds hx)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_insertNth j y t))
      ((hA.differentiableAt (hΩ.mem_nhds hx)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_insertNth j y t))
  have hz := integralOn_eq_zero_of_supported_slice_derivative j Ω hΩ.measurableSet
    (fun x => A x * boltzmannWeight β H x)
    (fun x => partialDeriv j A x * boltzmannWeight β H x -
      β * (A x * partialDeriv j H x * boltzmannWeight β H x))
    (tsupport_mul_subset_left.trans hsupport) hobs (hright.sub (hleft.const_mul β)) hd
  rw [integral_sub hright (hleft.const_mul β), integral_const_mul] at hz
  linarith

/-- The normalized identity for a canonical ensemble restricted to an open domain. -/
theorem canonical_partial_identity_on_open {n : ℕ} (j : Fin (n+1))
    (Ω : Set (Fin (n+1) → ℝ)) (hΩ : IsOpen Ω)
    [NeZero (volume.restrict Ω)]
    (β : ℝ) (H A : (Fin (n+1) → ℝ) → ℝ)
    (hH : DifferentiableOn ℝ H Ω) (hA : DifferentiableOn ℝ A Ω)
    (hsupport : tsupport A ⊆ Ω)
    (_hweight : IntegrableOn (boltzmannWeight β H) Ω)
    (hleft : IntegrableOn (fun x => A x * partialDeriv j H x * boltzmannWeight β H x) Ω)
    (hright : IntegrableOn (fun x => partialDeriv j A x * boltzmannWeight β H x) Ω)
    (hobs : IntegrableOn (fun x => A x * boltzmannWeight β H x) Ω) :
    β * canonicalExpectation (volume.restrict Ω) β H (fun x => A x * partialDeriv j H x) =
      canonicalExpectation (volume.restrict Ω) β H (partialDeriv j A) := by
  unfold canonicalExpectation
  rw [← mul_div_assoc,
    weighted_partial_identity_on_open j Ω hΩ β H A hH hA hsupport hleft hright hobs]

/-- A continuous function on an open domain is integrable there when its
compact support is contained in the domain. -/
theorem integrableOn_of_continuousOn_of_supported {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω) (f : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f Ω) (hcompact : HasCompactSupport f) (hsupport : tsupport f ⊆ Ω) :
    IntegrableOn f Ω :=
  ((hf.continuous_of_tsupport_subset hΩ hsupport).integrable_of_hasCompactSupport
    hcompact).integrableOn

/-- For a compactly supported C¹ observable in an open domain, C¹ regularity
of the Hamiltonian inside the domain suffices for all weighted integrability
and boundary conditions in the unnormalized identity. -/
theorem weighted_partial_identity_on_open_of_hasCompactSupport {n : ℕ} (j : Fin (n+1))
    (Ω : Set (Fin (n+1) → ℝ)) (hΩ : IsOpen Ω)
    (β : ℝ) (H A : (Fin (n+1) → ℝ) → ℝ)
    (hH : ContDiffOn ℝ 1 H Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hcompact : HasCompactSupport A) (hsupport : tsupport A ⊆ Ω) :
    β * (∫ x in Ω, A x * partialDeriv j H x * boltzmannWeight β H x) =
      ∫ x in Ω, partialDeriv j A x * boltzmannWeight β H x := by
  have hw : ContinuousOn (boltzmannWeight β H) Ω :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hH.continuousOn)
  have hH' : ContinuousOn (partialDeriv j H) Ω :=
    (hH.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hA' : ContinuousOn (partialDeriv j A) Ω :=
    (hA.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hsA' : tsupport (partialDeriv j A) ⊆ tsupport A :=
    tsupport_fderiv_apply_subset ℝ _
  have hcA' : HasCompactSupport (partialDeriv j A) := hcompact.fderiv_apply ℝ _
  apply weighted_partial_identity_on_open j Ω hΩ β H A
    (hH.differentiableOn (by decide)) (hA.differentiableOn (by decide)) hsupport
  · exact integrableOn_of_continuousOn_of_supported Ω hΩ _
      ((hA.continuousOn.mul hH').mul hw) (hcompact.mul_right.mul_right)
      ((tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hsupport)
  · exact integrableOn_of_continuousOn_of_supported Ω hΩ _
      (hA'.mul hw) hcA'.mul_right
      ((tsupport_mul_subset_left.trans hsA').trans hsupport)
  · exact integrableOn_of_continuousOn_of_supported Ω hΩ _
      (hA.continuousOn.mul hw) hcompact.mul_right
      (tsupport_mul_subset_left.trans hsupport)

end Equipartition
