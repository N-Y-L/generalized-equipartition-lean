import Equipartition.Canonical
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The normalized Gibbs probability measure -/

open MeasureTheory

namespace Equipartition

variable {X : Type*} [MeasurableSpace X]

/-- The Gibbs measure obtained by normalizing the Boltzmann density. -/
noncomputable def gibbsMeasure (μ : Measure X) (β : ℝ) (H : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal
    (boltzmannWeight β H x / partitionFunction μ β H))

theorem gibbsMeasure_isProbabilityMeasure (μ : Measure X) [NeZero μ]
    (β : ℝ) (H : X → ℝ) (hweight : Integrable (boltzmannWeight β H) μ) :
    IsProbabilityMeasure (gibbsMeasure μ β H) := by
  have hZ := partitionFunction_pos μ β H hweight
  constructor
  rw [gibbsMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hweight.div_const _) (Filter.Eventually.of_forall
      (fun x => (div_pos (boltzmannWeight_pos β H x) hZ).le))]
  rw [integral_div]
  change ENNReal.ofReal (partitionFunction μ β H / partitionFunction μ β H) = 1
  rw [div_self hZ.ne', ENNReal.ofReal_one]

/-- The integral against the normalized Gibbs measure agrees with the canonical
expectation. The integrable weight supplies its almost-everywhere measurability. -/
theorem integral_gibbsMeasure (μ : Measure X) [NeZero μ] (β : ℝ) (H A : X → ℝ)
    (hweight : Integrable (boltzmannWeight β H) μ) :
    (∫ x, A x ∂gibbsMeasure μ β H) = canonicalExpectation μ β H A := by
  have hZ := partitionFunction_pos μ β H hweight
  rw [gibbsMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (hweight.aemeasurable.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_of_lt (div_pos (boltzmannWeight_pos β H _) hZ)),
    smul_eq_mul, canonicalExpectation]
  simp_rw [div_mul_eq_mul_div, mul_comm (boltzmannWeight β H _) (A _)]
  exact integral_div _ _

end Equipartition
