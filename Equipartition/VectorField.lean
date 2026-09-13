import Equipartition.MainTheorem
import Equipartition.Slices

/-!
# Vector-field equipartition and the canonical virial identity

Summing coordinate integration by parts gives
`β ⟨X · ∇H⟩ = ⟨div X⟩`. The vector field may depend on every coordinate.
-/

open MeasureTheory

namespace Equipartition

/-- The change of energy in the direction of a vector field. -/
noncomputable def energyDerivative {n : ℕ}
    (H : (Fin n → ℝ) → ℝ) (X : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) : ℝ := ∑ j, X x j * partialDeriv j H x

/-- The divergence in Cartesian coordinates. -/
noncomputable def divergence {n : ℕ} (X : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) : ℝ := ∑ j, partialDeriv j (fun y => X y j) x

/-- The vector-field identity with supplied coordinate derivatives. Slice regularity
allows countably many cusps on almost every line and requires only the coordinate
derivatives appearing in the formula. -/
theorem canonical_vector_identity_slices {n : ℕ}
    (β : ℝ) (H : (Fin (n + 1) → ℝ) → ℝ)
    (X G D : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (hH : ∀ j, HasAESliceDeriv j H (fun x => G x j))
    (hX : ∀ j, HasAESliceDeriv j (fun x => X x j) (fun x => D x j))
    (_hweight : Integrable (boltzmannWeight β H))
    (henergy : ∀ j, Integrable (fun x => X x j * G x j * boltzmannWeight β H x))
    (hdiv : ∀ j, Integrable (fun x => D x j * boltzmannWeight β H x))
    (hcomponent : ∀ j, Integrable (fun x => X x j * boltzmannWeight β H x)) :
    β * canonicalExpectation volume β H (fun x => ∑ j, X x j * G x j) =
      canonicalExpectation volume β H (fun x => ∑ j, D x j) := by
  have hsum :
      β * (∫ x, (∑ j, X x j * G x j) * boltzmannWeight β H x) =
        ∫ x, (∑ j, D x j) * boltzmannWeight β H x := by
    simp only [Finset.sum_mul]
    rw [integral_finset_sum _ (fun j _ => henergy j),
      integral_finset_sum _ (fun j _ => hdiv j), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact weighted_slice_identity_of_integrable j β H (fun x => X x j)
      (fun x => G x j) (fun x => D x j) (hH j) (hX j)
      (henergy j) (hdiv j) (hcomponent j)
  unfold canonicalExpectation
  rw [← mul_div_assoc, hsum]

/-- The vector-field identity under absolute integrability of each weighted component
and of the two terms in its coordinate product rule. -/
theorem canonical_vector_identity {n : ℕ}
    (β : ℝ) (H : (Fin (n + 1) → ℝ) → ℝ)
    (X : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (hH : Differentiable ℝ H) (hX : ∀ j, Differentiable ℝ (fun x => X x j))
    (_hweight : Integrable (boltzmannWeight β H))
    (henergy : ∀ j, Integrable (fun x => X x j * partialDeriv j H x * boltzmannWeight β H x))
    (hdiv : ∀ j, Integrable (fun x =>
      partialDeriv j (fun y => X y j) x * boltzmannWeight β H x))
    (hcomponent : ∀ j, Integrable (fun x => X x j * boltzmannWeight β H x)) :
    β * canonicalExpectation volume β H (energyDerivative H X) =
      canonicalExpectation volume β H (divergence X) := by
  have hsum :
      β * (∫ x, energyDerivative H X x * boltzmannWeight β H x) =
        ∫ x, divergence X x * boltzmannWeight β H x := by
    simp only [energyDerivative, divergence, Finset.sum_mul]
    rw [integral_finset_sum _ (fun j _ => henergy j),
      integral_finset_sum _ (fun j _ => hdiv j), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact weighted_partial_identity_of_integrable j β H (fun x => X x j)
      hH (hX j) (henergy j) (hdiv j) (hcomponent j)
  unfold canonicalExpectation
  rw [← mul_div_assoc, hsum]

/-- The canonical virial identity. It is an ensemble average, without a claim about
dynamical time averages. -/
theorem canonical_virial_identity {n : ℕ}
    (β : ℝ) (H : (Fin (n + 1) → ℝ) → ℝ)
    (hβ : 0 < β) (hH : Differentiable ℝ H)
    (hweight : Integrable (boltzmannWeight β H))
    (hmoment : ∀ j, Integrable (fun x => x j * partialDeriv j H x * boltzmannWeight β H x))
    (hcoordinate : ∀ j, Integrable (fun x => x j * boltzmannWeight β H x)) :
    canonicalExpectation volume β H (fun x => ∑ j, x j * partialDeriv j H x) =
      (n + 1 : ℝ) / β := by
  have hsum :
      canonicalExpectation volume β H (fun x => ∑ j, x j * partialDeriv j H x) =
        ∑ j, canonicalExpectation volume β H (fun x => x j * partialDeriv j H x) := by
    simp only [canonicalExpectation, Finset.sum_mul]
    rw [integral_finset_sum _ (fun j _ => hmoment j), Finset.sum_div]
  rw [hsum]
  simp only [generalized_equipartition_of_integrable _ _ β H hβ hH hweight
    (hmoment _) (hcoordinate _), ite_true]
  simp [div_eq_mul_inv]

end Equipartition
