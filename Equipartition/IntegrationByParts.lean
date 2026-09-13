import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Canonical integration by parts

The derivative of `A x * exp (-β * H x)` gives the generalized equipartition
identity. The whole-line theorems state the required integrability and boundary
conditions explicitly. A finite-interval theorem retains the boundary term.
-/

open Filter MeasureTheory
open scoped Topology Interval

namespace Equipartition

/-- Product and chain rules for an observable multiplied by a Boltzmann weight. -/
theorem hasDerivAt_observable_boltzmann
    {H A : ℝ → ℝ} {H' A' β x : ℝ}
    (hH : HasDerivAt H H' x) (hA : HasDerivAt A A' x) :
    HasDerivAt (fun y => A y * Real.exp (-β * H y))
      (A' * Real.exp (-β * H x) - β * (A x * H' * Real.exp (-β * H x))) x := by
  convert hA.mul ((hH.const_mul (-β)).exp) using 1
  ring

/-- Canonical integration by parts with possibly nonzero limits at infinity. -/
theorem canonical_identity_with_boundary
    {H A H' A' : ℝ → ℝ} {β left right : ℝ}
    (hH : ∀ x, HasDerivAt H (H' x) x)
    (hA : ∀ x, HasDerivAt A (A' x) x)
    (hA' : Integrable (fun x => A' x * Real.exp (-β * H x)))
    (hAH' : Integrable (fun x => A x * H' x * Real.exp (-β * H x)))
    (hleft : Tendsto (fun x => A x * Real.exp (-β * H x)) atBot (𝓝 left))
    (hright : Tendsto (fun x => A x * Real.exp (-β * H x)) atTop (𝓝 right)) :
    β * (∫ x, A x * H' x * Real.exp (-β * H x)) =
      (∫ x, A' x * Real.exp (-β * H x)) - (right - left) := by
  have h := integral_of_hasDerivAt_of_tendsto
    (fun x => hasDerivAt_observable_boltzmann (hH x) (hA x))
    (hA'.sub (hAH'.const_mul β)) hleft hright
  rw [integral_sub hA' (hAH'.const_mul β), integral_const_mul] at h
  linarith

/-- Generalized equipartition for a differentiable observable with vanishing
weighted boundary values. No assumption on the sign of `β` is needed. -/
theorem canonical_identity_of_tendsto_zero
    {H A H' A' : ℝ → ℝ} {β : ℝ}
    (hH : ∀ x, HasDerivAt H (H' x) x)
    (hA : ∀ x, HasDerivAt A (A' x) x)
    (hA' : Integrable (fun x => A' x * Real.exp (-β * H x)))
    (hAH' : Integrable (fun x => A x * H' x * Real.exp (-β * H x)))
    (hleft : Tendsto (fun x => A x * Real.exp (-β * H x)) atBot (𝓝 0))
    (hright : Tendsto (fun x => A x * Real.exp (-β * H x)) atTop (𝓝 0)) :
    β * (∫ x, A x * H' x * Real.exp (-β * H x)) =
      ∫ x, A' x * Real.exp (-β * H x) := by
  simpa using canonical_identity_with_boundary hH hA hA' hAH' hleft hright

/-- Integrability of the weighted observable is an alternative sufficient
condition for the absence of boundary terms. -/
theorem canonical_identity_of_integrable
    {H A H' A' : ℝ → ℝ} {β : ℝ}
    (hH : ∀ x, HasDerivAt H (H' x) x)
    (hA : ∀ x, HasDerivAt A (A' x) x)
    (hA' : Integrable (fun x => A' x * Real.exp (-β * H x)))
    (hAH' : Integrable (fun x => A x * H' x * Real.exp (-β * H x)))
    (hAweight : Integrable (fun x => A x * Real.exp (-β * H x))) :
    β * (∫ x, A x * H' x * Real.exp (-β * H x)) =
      ∫ x, A' x * Real.exp (-β * H x) := by
  have h := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => hasDerivAt_observable_boltzmann (hH x) (hA x))
    (hA'.sub (hAH'.const_mul β)) hAweight
  rw [integral_sub hA' (hAH'.const_mul β), integral_const_mul] at h
  linarith

/-- The coordinate observable `A x = x` yields the unnormalized equipartition
identity. Normalizing by a nonzero partition function gives `β ⟨x H'⟩ = 1`. -/
theorem canonical_coordinate_identity
    {H H' : ℝ → ℝ} {β : ℝ}
    (hH : ∀ x, HasDerivAt H (H' x) x)
    (hweight : Integrable (fun x => Real.exp (-β * H x)))
    (hxH' : Integrable (fun x => x * H' x * Real.exp (-β * H x)))
    (hleft : Tendsto (fun x => x * Real.exp (-β * H x)) atBot (𝓝 0))
    (hright : Tendsto (fun x => x * Real.exp (-β * H x)) atTop (𝓝 0)) :
    β * (∫ x, x * H' x * Real.exp (-β * H x)) =
      ∫ x, Real.exp (-β * H x) := by
  simpa only [one_mul] using canonical_identity_of_tendsto_zero
    hH (fun x => hasDerivAt_id x) (by simpa only [one_mul] using hweight)
    hxH' hleft hright

/-- Canonical integration by parts on any oriented finite interval. The
weighted endpoint values give the exact boundary correction. -/
theorem canonical_interval_identity
    {H A H' A' : ℝ → ℝ} {β a b : ℝ}
    (hH : ∀ x ∈ Set.uIcc a b, HasDerivAt H (H' x) x)
    (hA : ∀ x ∈ Set.uIcc a b, HasDerivAt A (A' x) x)
    (hA' : IntervalIntegrable (fun x => A' x * Real.exp (-β * H x)) volume a b)
    (hAH' : IntervalIntegrable
      (fun x => A x * H' x * Real.exp (-β * H x)) volume a b) :
    β * (∫ x in a..b, A x * H' x * Real.exp (-β * H x)) =
      (∫ x in a..b, A' x * Real.exp (-β * H x)) -
        (A b * Real.exp (-β * H b) - A a * Real.exp (-β * H a)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_observable_boltzmann (hH x hx) (hA x hx))
    (hA'.sub (hAH'.const_mul β))
  rw [intervalIntegral.integral_sub hA' (hAH'.const_mul β),
    intervalIntegral.integral_const_mul] at h
  linarith

end Equipartition
