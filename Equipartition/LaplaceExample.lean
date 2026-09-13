import Equipartition.Slices
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# A nonquadratic Hamiltonian with a cusp

For `H(x) = |x|` and `β > 0`, the partition function is `2 / β`
and the mean energy is `1 / β`. All integrability hypotheses are proved.
Integration by parts allows the single nondifferentiable point at zero.
-/

open MeasureTheory Set

namespace Equipartition

/-- Reflection extends an integrable function on the positive half-line
to an integrable even function on the whole line. -/
theorem integrable_comp_abs_of_integrableOn_Ioi {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) : Integrable (fun x => f |x|) := by
  have hpos : IntegrableOn (fun x => f |x|) (Ioi 0) := by
    refine hf.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos hx]
  have hneg : IntegrableOn (fun x => f |x|) (Iic 0) := by
    have hneg' := IntegrableOn.comp_neg_Iio (c := (0 : ℝ))
      (f := fun x => f |x|) (μ := volume) (by simpa only [neg_zero] using hpos)
    have hiio : IntegrableOn (fun x => f |x|) (Iio 0) := by
      simpa only [abs_neg] using hneg'
    exact (integrableOn_Iic_iff_integrableOn_Iio (f := fun x : ℝ => f |x|)
      (μ := volume) (b := 0)).mpr hiio
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := 0), integrableOn_union]
  exact ⟨hneg, hpos⟩

/-- The absolute-value Hamiltonian has an integrable Boltzmann weight. -/
theorem laplace_weight_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (boltzmannWeight β (abs : ℝ → ℝ)) := by
  exact integrable_comp_abs_of_integrableOn_Ioi
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hβ) 0)

/-- The weighted energy of the absolute-value Hamiltonian is integrable. -/
theorem laplace_weighted_energy_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : ℝ => |x| * boltzmannWeight β abs x) := by
  apply integrable_comp_abs_of_integrableOn_Ioi (f := fun x => x * Real.exp (-β * x))
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num)
      le_rfl hβ)

/-- The weighted coordinate is absolutely integrable. -/
theorem laplace_weighted_coordinate_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : ℝ => x * boltzmannWeight β abs x) := by
  refine (laplace_weighted_energy_integrable hβ).mono' ?_ ?_
  · exact (continuous_id.mul
      ((continuous_const.mul continuous_abs).rexp)).aestronglyMeasurable
  · filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (boltzmannWeight_pos β abs x)]
    exact le_rfl

/-- Exact partition function of `H(x) = |x|`. -/
theorem laplace_partitionFunction {β : ℝ} (hβ : 0 < β) :
    partitionFunction volume β (abs : ℝ → ℝ) = 2 / β := by
  unfold partitionFunction boltzmannWeight
  rw [integral_comp_abs (f := fun x => Real.exp (-β * x)),
    integral_exp_mul_Ioi (neg_lt_zero.mpr hβ)]
  simp
  ring

/-- The mean energy of `H(x) = |x|` is `1 / β`. Positivity is the only
hypothesis; continuity, the derivative off zero, and integrability are proved. -/
theorem laplace_equipartition {β : ℝ} (hβ : 0 < β) :
    canonicalExpectation volume β (abs : ℝ → ℝ) abs = 1 / β := by
  have hd : ∀ t ∉ ({0} : Set ℝ), HasDerivAt
      (fun x : ℝ => x * boltzmannWeight β abs x)
      (boltzmannWeight β abs t - β * (|t| * boltzmannWeight β abs t)) t := by
    intro t ht
    have ht0 : t ≠ 0 := fun h => ht (by simp [h])
    simpa only [id_eq, one_mul, self_mul_sign, boltzmannWeight] using
      hasDerivAt_observable_boltzmann (β := β) (hasDerivAt_abs ht0) (hasDerivAt_id t)
  have hIBP := integral_derivative_off_countable_of_integrable
    (continuous_id.mul ((continuous_const.mul continuous_abs).rexp))
    (countable_singleton 0) hd (laplace_weighted_coordinate_integrable hβ)
    ((laplace_weight_integrable hβ).sub
      ((laplace_weighted_energy_integrable hβ).const_mul β))
  rw [integral_sub (laplace_weight_integrable hβ)
    ((laplace_weighted_energy_integrable hβ).const_mul β), integral_const_mul] at hIBP
  have hZ := (partitionFunction_pos volume β (abs : ℝ → ℝ)
    (laplace_weight_integrable hβ)).ne'
  unfold canonicalExpectation
  apply (div_eq_div_iff hZ hβ.ne').2
  dsimp only [partitionFunction] at hZ ⊢
  nlinarith

end Equipartition
