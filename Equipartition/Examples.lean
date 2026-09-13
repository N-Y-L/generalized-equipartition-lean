import Equipartition.IntegrationByParts
import Equipartition.Canonical
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# A fully discharged quadratic example

For every positive inverse temperature `β` and coefficient `c`, the quadratic
Hamiltonian `H x = c * x^2` has expected energy `1 / (2 * β)`. All analytic
conditions follow from positivity and Gaussian integrability. Integration by
parts supplies the energy identity; the explicit Gaussian integral is needed
only for the separate partition-function formula.
-/

open MeasureTheory

namespace Equipartition

/-- A positive quadratic Hamiltonian has an integrable Boltzmann weight. -/
theorem quadratic_weight_integrable {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    Integrable (boltzmannWeight β (fun x : ℝ => c * x ^ 2)) := by
  change Integrable (fun x : ℝ => Real.exp (-β * (c * x ^ 2)))
  simpa only [← mul_assoc, neg_mul] using
    integrable_exp_neg_mul_sq (mul_pos hβ hc)

/-- The weighted coordinate is integrable for a positive quadratic Hamiltonian. -/
theorem quadratic_weighted_coordinate_integrable
    {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    Integrable (fun x : ℝ => x * Real.exp (-β * (c * x ^ 2))) := by
  simpa only [← mul_assoc, neg_mul] using
    integrable_mul_exp_neg_mul_sq (mul_pos hβ hc)

/-- The quadratic moment of a Gaussian is integrable. -/
theorem quadratic_weighted_square_integrable
    {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-β * (c * x ^ 2))) := by
  simpa only [Real.rpow_two, ← mul_assoc, neg_mul] using
    (integrable_rpow_mul_exp_neg_mul_sq (mul_pos hβ hc) (s := (2 : ℝ)) (by norm_num))

/-- The partition function of `H(x) = c x²` is the standard Gaussian integral. -/
theorem quadratic_partitionFunction (β c : ℝ) :
    partitionFunction volume β (fun x : ℝ => c * x ^ 2) =
      Real.sqrt (Real.pi / (β * c)) := by
  simpa only [partitionFunction, boltzmannWeight, ← mul_assoc, neg_mul] using
    integral_gaussian (β * c)

/-- Every positive quadratic degree of freedom has canonical expected energy
`1 / (2β)`. Positivity is the only hypothesis: derivatives, integrability, and
the absence of boundary terms are established in the proof. -/
theorem quadratic_equipartition {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    canonicalExpectation volume β (fun x : ℝ => c * x ^ 2)
      (fun x => c * x ^ 2) = 1 / (2 * β) := by
  have hH (x : ℝ) : HasDerivAt (fun x : ℝ => c * x ^ 2) (2 * c * x) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul c using 1
    simp only [id_eq]
    ring
  have hprod : Integrable
      (fun x : ℝ => x * (2 * c * x) * Real.exp (-β * (c * x ^ 2))) := by
    convert (quadratic_weighted_square_integrable hβ hc).const_mul (2 * c) using 1
    ext x
    ring
  have hIBP := canonical_identity_of_integrable hH (fun x => hasDerivAt_id x)
    (by simpa only [one_mul] using quadratic_weight_integrable hβ hc)
    hprod (quadratic_weighted_coordinate_integrable hβ hc)
  have htwo : (fun x : ℝ => x * (2 * c * x) * Real.exp (-β * (c * x ^ 2))) =
      (fun x : ℝ => 2 * (c * x ^ 2 * Real.exp (-β * (c * x ^ 2)))) := by
    ext x
    ring
  simp only [id_eq, one_mul] at hIBP
  rw [htwo, integral_const_mul] at hIBP
  have hZ := (partitionFunction_pos volume β (fun x : ℝ => c * x ^ 2)
    (quadratic_weight_integrable hβ hc)).ne'
  simp only [canonicalExpectation, partitionFunction, boltzmannWeight] at hZ ⊢
  apply (div_eq_div_iff hZ (mul_ne_zero (by norm_num) hβ.ne')).2
  nlinarith [hIBP]

end Equipartition
