import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import Equipartition.Canonical
import Equipartition.IntegrationByParts
/-!
# Multivariate canonical integration by parts

Lebesgue measure on a finite dimensional coordinate space is split into the selected
coordinate and its complement by a measure-preserving equivalence. Fubini's theorem
then reduces integration by parts to the whole-line fundamental theorem of calculus.
No independence or additive decomposition of the Hamiltonian is assumed.

Boundary terms may be eliminated either by explicit almost-everywhere slice limits,
or by global integrability of the observable times the Boltzmann weight.
-/

open MeasureTheory Filter
open scoped Topology

namespace Equipartition

/-- Varying one coordinate has the corresponding coordinate unit vector as derivative. -/
theorem hasDerivAt_insertNth {n : ℕ} (j : Fin (n+1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => j.insertNth (α := fun _ => ℝ) s y) (Pi.single j 1) t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine j.succAboveCases ?_ (fun k => ?_) i
  · simpa using hasDerivAt_id t
  · simpa [Pi.single_apply, Fin.succAbove_ne] using hasDerivAt_const t (y k)

/-- Integrate a coordinate derivative using vanishing boundary terms on almost every slice. -/
theorem integral_eq_zero_of_slice_derivative {n : ℕ}
    (j : Fin (n+1)) (f g : (Fin (n+1) → ℝ) → ℝ)
    (hg : Integrable g)
    (hd : ∀ y t, HasDerivAt (fun s => f (j.insertNth s y)) (g (j.insertNth t y)) t)
    (hb : ∀ᵐ y : Fin n → ℝ, Tendsto (fun t => f (j.insertNth t y)) atBot (𝓝 0))
    (ht : ∀ᵐ y : Fin n → ℝ, Tendsto (fun t => f (j.insertNth t y)) atTop (𝓝 0)) :
    ∫ x, g x = 0 := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j).symm
  have he : MeasurePreserving e := (volume_preserving_piFinSuccAbove _ j).symm
  have hge : Integrable (fun p : ℝ × (Fin n → ℝ) => g (e p)) :=
    he.integrable_comp_of_integrable hg
  rw [← he.integral_comp' g]
  change (∫ p, g (e p) ∂(volume.prod volume)) = 0
  rw [integral_prod_symm _ hge]
  have hz : ∀ᵐ y : Fin n → ℝ, ∫ t : ℝ, g (e (t, y)) = 0 := by
    filter_upwards [hge.prod_left_ae, hb, ht] with y hy hby hty
    exact (integral_of_hasDerivAt_of_tendsto (hd y) hy hby hty).trans (sub_self _)
  simpa using integral_congr_ae hz

/-- An integrable function with integrable coordinate derivative has zero derivative integral.
Fubini supplies integrability on almost every slice, so no separate boundary hypothesis is needed. -/
theorem integral_eq_zero_of_slice_derivative_of_integrable {n : ℕ}
    (j : Fin (n+1)) (f g : (Fin (n+1) → ℝ) → ℝ)
    (hf : Integrable f) (hg : Integrable g)
    (hd : ∀ y t, HasDerivAt (fun s => f (j.insertNth s y)) (g (j.insertNth t y)) t) :
    ∫ x, g x = 0 := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j).symm
  have he : MeasurePreserving e := (volume_preserving_piFinSuccAbove _ j).symm
  have hfe : Integrable (fun p : ℝ × (Fin n → ℝ) => f (e p)) :=
    he.integrable_comp_of_integrable hf
  have hge : Integrable (fun p : ℝ × (Fin n → ℝ) => g (e p)) :=
    he.integrable_comp_of_integrable hg
  rw [← he.integral_comp' g]
  change (∫ p, g (e p) ∂(volume.prod volume)) = 0
  rw [integral_prod_symm _ hge]
  have hz : ∀ᵐ y : Fin n → ℝ, ∫ t : ℝ, g (e (t, y)) = 0 := by
    filter_upwards [hge.prod_left_ae, hfe.prod_left_ae] with y hgy hfy
    exact integral_eq_zero_of_hasDerivAt_of_integrable (hd y) hgy hfy
  simpa using integral_congr_ae hz

/-- The coordinate partial derivative, defined from the genuine Fréchet derivative. -/
noncomputable def partialDeriv {n : ℕ} (j : Fin n) (H : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ := fderiv ℝ H x (Pi.single j 1)

theorem hasDerivAt_slice {n : ℕ} (j : Fin (n+1)) (H : (Fin (n+1) → ℝ) → ℝ)
    (hH : Differentiable ℝ H) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => H (j.insertNth s y)) (partialDeriv j H (j.insertNth t y)) t := by
  exact (hH _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth j y t)

/-- A coordinate integration-by-parts identity for a nonseparable Hamiltonian.
The two boundary limits need hold only for almost every transverse slice. -/
theorem weighted_partial_identity {n : ℕ} (j : Fin (n+1))
    (β : ℝ) (H A : (Fin (n+1) → ℝ) → ℝ)
    (hH : Differentiable ℝ H) (hA : Differentiable ℝ A)
    (hleft : Integrable (fun x => A x * partialDeriv j H x * boltzmannWeight β H x))
    (hright : Integrable (fun x => partialDeriv j A x * boltzmannWeight β H x))
    (hbot : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y)) atBot (𝓝 0))
    (htop : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y)) atTop (𝓝 0)) :
    β * (∫ x, A x * partialDeriv j H x * boltzmannWeight β H x) =
      ∫ x, partialDeriv j A x * boltzmannWeight β H x := by
  have hd : ∀ y t, HasDerivAt
      (fun s => A (j.insertNth s y) * boltzmannWeight β H (j.insertNth s y))
      (partialDeriv j A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y) -
        β * (A (j.insertNth t y) * partialDeriv j H (j.insertNth t y) *
          boltzmannWeight β H (j.insertNth t y))) t := by
    intro y t
    exact hasDerivAt_observable_boltzmann (hasDerivAt_slice j H hH y t)
      (hasDerivAt_slice j A hA y t)
  have hz := integral_eq_zero_of_slice_derivative j
    (fun x => A x * boltzmannWeight β H x)
    (fun x => partialDeriv j A x * boltzmannWeight β H x -
      β * (A x * partialDeriv j H x * boltzmannWeight β H x))
    (hright.sub (hleft.const_mul β)) hd hbot htop
  rw [integral_sub hright (hleft.const_mul β), integral_const_mul] at hz
  linarith

/-- The weighted coordinate identity with global integrability in place of slice limits. -/
theorem weighted_partial_identity_of_integrable {n : ℕ} (j : Fin (n+1))
    (β : ℝ) (H A : (Fin (n+1) → ℝ) → ℝ)
    (hH : Differentiable ℝ H) (hA : Differentiable ℝ A)
    (hleft : Integrable (fun x => A x * partialDeriv j H x * boltzmannWeight β H x))
    (hright : Integrable (fun x => partialDeriv j A x * boltzmannWeight β H x))
    (hobs : Integrable (fun x => A x * boltzmannWeight β H x)) :
    β * (∫ x, A x * partialDeriv j H x * boltzmannWeight β H x) =
      ∫ x, partialDeriv j A x * boltzmannWeight β H x := by
  have hd : ∀ y t, HasDerivAt
      (fun s => A (j.insertNth s y) * boltzmannWeight β H (j.insertNth s y))
      (partialDeriv j A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y) -
        β * (A (j.insertNth t y) * partialDeriv j H (j.insertNth t y) *
          boltzmannWeight β H (j.insertNth t y))) t := by
    intro y t
    exact hasDerivAt_observable_boltzmann (hasDerivAt_slice j H hH y t)
      (hasDerivAt_slice j A hA y t)
  have hz := integral_eq_zero_of_slice_derivative_of_integrable j
    (fun x => A x * boltzmannWeight β H x)
    (fun x => partialDeriv j A x * boltzmannWeight β H x -
      β * (A x * partialDeriv j H x * boltzmannWeight β H x))
    hobs (hright.sub (hleft.const_mul β)) hd
  rw [integral_sub hright (hleft.const_mul β), integral_const_mul] at hz
  linarith

/-- The normalized coordinate integration-by-parts (canonical Stein) identity. -/
theorem canonical_partial_identity {n : ℕ} (j : Fin (n+1))
    (β : ℝ) (H A : (Fin (n+1) → ℝ) → ℝ)
    (hH : Differentiable ℝ H) (hA : Differentiable ℝ A)
    (_hweight : Integrable (boltzmannWeight β H))
    (hleft : Integrable (fun x => A x * partialDeriv j H x * boltzmannWeight β H x))
    (hright : Integrable (fun x => partialDeriv j A x * boltzmannWeight β H x))
    (hbot : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y)) atBot (𝓝 0))
    (htop : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y)) atTop (𝓝 0)) :
    β * canonicalExpectation volume β H (fun x => A x * partialDeriv j H x) =
      canonicalExpectation volume β H (partialDeriv j A) := by
  unfold canonicalExpectation
  rw [← mul_div_assoc, weighted_partial_identity j β H A hH hA hleft hright hbot htop]

/-- The normalized identity under integrability of the weighted observable. -/
theorem canonical_partial_identity_of_integrable {n : ℕ} (j : Fin (n+1))
    (β : ℝ) (H A : (Fin (n+1) → ℝ) → ℝ)
    (hH : Differentiable ℝ H) (hA : Differentiable ℝ A)
    (_hweight : Integrable (boltzmannWeight β H))
    (hleft : Integrable (fun x => A x * partialDeriv j H x * boltzmannWeight β H x))
    (hright : Integrable (fun x => partialDeriv j A x * boltzmannWeight β H x))
    (hobs : Integrable (fun x => A x * boltzmannWeight β H x)) :
    β * canonicalExpectation volume β H (fun x => A x * partialDeriv j H x) =
      canonicalExpectation volume β H (partialDeriv j A) := by
  unfold canonicalExpectation
  rw [← mul_div_assoc,
    weighted_partial_identity_of_integrable j β H A hH hA hleft hright hobs]

end Equipartition
