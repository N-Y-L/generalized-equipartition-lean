import Equipartition.Multivariate
import Equipartition.GibbsMeasure

/-!
# Generalized equipartition

For `β > 0` and a differentiable Hamiltonian on a finite-dimensional real phase space,
the canonical expectation of `xᵢ ∂ⱼH` is `δᵢⱼ / β`. The Boltzmann weight and
weighted observable must be integrable, and the coordinate-weight product
must vanish at both ends of almost every line parallel to coordinate `j`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Equipartition

theorem partialDeriv_coordinate {n : ℕ} (i j : Fin n) (x : Fin n → ℝ) :
    partialDeriv j (fun y => y i) x = if i = j then 1 else 0 := by
  rw [partialDeriv, (hasFDerivAt_apply i x).fderiv]
  simp [Pi.single_apply]

/-- Generalized equipartition for any pair of coordinates. The Hamiltonian
may couple the coordinates and need not be quadratic. -/
theorem generalized_equipartition {n : ℕ} (i j : Fin (n + 1))
    (β : ℝ) (H : (Fin (n + 1) → ℝ) → ℝ)
    (hβ : 0 < β) (hH : Differentiable ℝ H)
    (hweight : Integrable (boltzmannWeight β H))
    (hmoment : Integrable (fun x => x i * partialDeriv j H x * boltzmannWeight β H x))
    (hbot : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => (j.insertNth (α := fun _ => ℝ) t y) i * boltzmannWeight β H (j.insertNth t y)) atBot (𝓝 0))
    (htop : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => (j.insertNth (α := fun _ => ℝ) t y) i * boltzmannWeight β H (j.insertNth t y)) atTop (𝓝 0)) :
    canonicalExpectation volume β H (fun x => x i * partialDeriv j H x) =
      (if i = j then 1 else 0) / β := by
  have hright : Integrable (fun x =>
      partialDeriv j (fun y => y i) x * boltzmannWeight β H x) := by
    simp_rw [partialDeriv_coordinate]
    exact hweight.const_mul _
  have h := weighted_partial_identity j β H (fun x => x i) hH
    (differentiable_apply i) hmoment hright hbot htop
  simp_rw [partialDeriv_coordinate] at h
  rw [integral_const_mul] at h
  have hZ := partitionFunction_pos volume β H hweight
  unfold canonicalExpectation
  apply (div_eq_div_iff hZ.ne' hβ.ne').2
  simpa only [partitionFunction, mul_comm] using h


/-- The coordinate-pair identity at physical temperature `T`, with `β = (kB*T)⁻¹`. -/
theorem generalized_equipartition_temperature {n : ℕ} (i j : Fin (n + 1))
    (kB T : ℝ) (H : (Fin (n + 1) → ℝ) → ℝ)
    (hkB : 0 < kB) (hT : 0 < T) (hH : Differentiable ℝ H)
    (hweight : Integrable (boltzmannWeight (kB * T)⁻¹ H))
    (hmoment : Integrable (fun x =>
      x i * partialDeriv j H x * boltzmannWeight (kB * T)⁻¹ H x))
    (hbot : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => (j.insertNth (α := fun _ => ℝ) t y) i * boltzmannWeight (kB * T)⁻¹ H (j.insertNth t y))
      atBot (𝓝 0))
    (htop : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => (j.insertNth (α := fun _ => ℝ) t y) i * boltzmannWeight (kB * T)⁻¹ H (j.insertNth t y))
      atTop (𝓝 0)) :
    canonicalExpectation volume (kB * T)⁻¹ H (fun x => x i * partialDeriv j H x) =
      kB * T * (if i = j then 1 else 0) := by
  rw [generalized_equipartition i j _ H (inv_pos.mpr (mul_pos hkB hT))
    hH hweight hmoment hbot htop]
  simp [div_eq_mul_inv, mul_comm]

/-- Global integrability of the weighted coordinate is an alternative to
explicit limits along almost every coordinate line. -/
theorem generalized_equipartition_of_integrable {n : ℕ} (i j : Fin (n + 1))
    (β : ℝ) (H : (Fin (n + 1) → ℝ) → ℝ)
    (hβ : 0 < β) (hH : Differentiable ℝ H)
    (hweight : Integrable (boltzmannWeight β H))
    (hmoment : Integrable (fun x => x i * partialDeriv j H x * boltzmannWeight β H x))
    (hcoordinate : Integrable (fun x => x i * boltzmannWeight β H x)) :
    canonicalExpectation volume β H (fun x => x i * partialDeriv j H x) =
      (if i = j then 1 else 0) / β := by
  have hright : Integrable (fun x =>
      partialDeriv j (fun y => y i) x * boltzmannWeight β H x) := by
    simp_rw [partialDeriv_coordinate]
    exact hweight.const_mul _
  have h := weighted_partial_identity_of_integrable j β H (fun x => x i) hH
    (differentiable_apply i) hmoment hright hcoordinate
  simp_rw [partialDeriv_coordinate] at h
  rw [integral_const_mul] at h
  have hZ := partitionFunction_pos volume β H hweight
  unfold canonicalExpectation
  apply (div_eq_div_iff hZ.ne' hβ.ne').2
  simpa only [partitionFunction, mul_comm] using h

/-- The coordinate identity as an integral against a proved Gibbs probability measure. -/
theorem generalized_equipartition_gibbs {n : ℕ} (i j : Fin (n + 1))
    (β : ℝ) (H : (Fin (n + 1) → ℝ) → ℝ)
    (hβ : 0 < β) (hH : Differentiable ℝ H)
    (hweight : Integrable (boltzmannWeight β H))
    (hmoment : Integrable (fun x => x i * partialDeriv j H x * boltzmannWeight β H x))
    (hcoordinate : Integrable (fun x => x i * boltzmannWeight β H x)) :
    IsProbabilityMeasure (gibbsMeasure volume β H) ∧
      (∫ x, x i * partialDeriv j H x ∂gibbsMeasure volume β H) =
        (if i = j then 1 else 0) / β := by
  exact ⟨gibbsMeasure_isProbabilityMeasure volume β H hweight,
    (integral_gibbsMeasure volume β H _ hweight).trans
      (generalized_equipartition_of_integrable i j β H hβ hH hweight hmoment hcoordinate)⟩

/-- A quadratic coordinate contributes `1 / (2β)` to the mean energy,
even when the remaining coordinates have a nonquadratic Hamiltonian. -/
theorem quadratic_coordinate_equipartition {n : ℕ} (i : Fin (n + 1))
    (β c : ℝ) (H : (Fin (n + 1) → ℝ) → ℝ)
    (hβ : 0 < β) (hH : Differentiable ℝ H)
    (hweight : Integrable (boltzmannWeight β H))
    (hmoment : Integrable (fun x => x i * partialDeriv i H x * boltzmannWeight β H x))
    (hcoordinate : Integrable (fun x => x i * boltzmannWeight β H x))
    (hquadratic : ∀ x, partialDeriv i H x = 2 * c * x i) :
    canonicalExpectation volume β H (fun x => c * (x i) ^ 2) = 1 / (2 * β) := by
  have h := generalized_equipartition_of_integrable i i β H hβ hH
    hweight hmoment hcoordinate
  simp only [ite_true] at h
  have hfun : (fun x => x i * partialDeriv i H x) =
      (fun x => 2 * (c * (x i) ^ 2)) := by
    funext x
    rw [hquadratic x]
    ring
  rw [hfun, canonicalExpectation_const_mul] at h
  apply (eq_div_iff (mul_ne_zero (by norm_num) hβ.ne')).2
  have h' := (eq_div_iff hβ.ne').mp h
  nlinarith

end Equipartition
