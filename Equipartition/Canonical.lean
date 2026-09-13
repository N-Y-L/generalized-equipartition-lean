import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Canonical expectations

The partition function is positive whenever the Boltzmann weight is integrable
and the underlying measure is nonzero. Expectations are normalized Lebesgue
integrals; no independence or separation of the Hamiltonian is assumed.
-/

open MeasureTheory

namespace Equipartition

variable {X : Type*} [MeasurableSpace X]

/-- The unnormalized canonical density at inverse temperature `β`. -/
noncomputable def boltzmannWeight (β : ℝ) (H : X → ℝ) (x : X) : ℝ :=
  Real.exp (-β * H x)

/-- The canonical partition function with respect to `μ`. -/
noncomputable def partitionFunction (μ : Measure X) (β : ℝ) (H : X → ℝ) : ℝ :=
  ∫ x, boltzmannWeight β H x ∂μ

/-- Canonical expectation of the observable `A`. -/
noncomputable def canonicalExpectation (μ : Measure X) (β : ℝ) (H A : X → ℝ) : ℝ :=
  (∫ x, A x * boltzmannWeight β H x ∂μ) / partitionFunction μ β H

omit [MeasurableSpace X] in
theorem boltzmannWeight_pos (β : ℝ) (H : X → ℝ) (x : X) :
    0 < boltzmannWeight β H x := Real.exp_pos _

theorem partitionFunction_pos (μ : Measure X) [NeZero μ] (β : ℝ) (H : X → ℝ)
    (hweight : Integrable (boltzmannWeight β H) μ) :
    0 < partitionFunction μ β H :=
  integral_exp_pos hweight

theorem canonicalExpectation_one (μ : Measure X) [NeZero μ] (β : ℝ) (H : X → ℝ)
    (hweight : Integrable (boltzmannWeight β H) μ) :
    canonicalExpectation μ β H (fun _ => 1) = 1 := by
  simp only [canonicalExpectation, one_mul]
  exact div_self (partitionFunction_pos μ β H hweight).ne'

theorem canonicalExpectation_const_mul (μ : Measure X) (β : ℝ) (H A : X → ℝ)
    (c : ℝ) :
    canonicalExpectation μ β H (fun x => c * A x) =
      c * canonicalExpectation μ β H A := by
  simp only [canonicalExpectation, mul_assoc, integral_const_mul]
  ring

theorem canonicalExpectation_congr (μ : Measure X) (β : ℝ) (H : X → ℝ)
    {A B : X → ℝ} (hAB : ∀ x, A x = B x) :
    canonicalExpectation μ β H A = canonicalExpectation μ β H B := by
  congr 1
  exact funext hAB

end Equipartition
