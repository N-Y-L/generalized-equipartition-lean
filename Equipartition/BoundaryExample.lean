import Equipartition.DomainTheorem

/-!
# Uniform distribution on an interval

For `H = 0` on `(0, 1)`, the weighted coordinate has endpoint traces `0` and `1`.
The boundary correction is one and the force moment is zero. Thus the usual
boundary-free identity does not hold on this domain.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Equipartition

/-- The unit interval as a one-dimensional coordinate domain. -/
def unitIntervalDomain : Set (Fin 1 → ℝ) :=
  coordinateDomain 0 univ (fun _ => 0) (fun _ => 1)

/-- The interval has unit Lebesgue volume. -/
theorem volume_unitIntervalDomain : volume unitIntervalDomain = 1 := by
  have heq : unitIntervalDomain = univ.pi (fun _ : Fin 1 => Ioo (0 : ℝ) 1) := by
    ext x
    simp [unitIntervalDomain, coordinateDomain, Set.mem_pi, Fin.forall_fin_one]
  rw [heq, volume_pi_pi]
  norm_num [Real.volume_Ioo]

/-- The zero Hamiltonian on the unit interval has unit partition function. -/
theorem uniform_interval_partitionFunction (β : ℝ) :
    partitionFunction (volume.restrict unitIntervalDomain) β (fun _ => 0) = 1 := by
  simp [partitionFunction, boltzmannWeight, integral_const, measureReal_def,
    volume_unitIntervalDomain]

/-- All hypotheses of the domain theorem hold for the uniform interval law.
The boundary term cancels the unit coordinate derivative exactly. -/
theorem uniform_interval_boundary_correction (β : ℝ) (hβ : 0 < β) :
    canonicalExpectation (volume.restrict unitIntervalDomain) β (fun _ => 0)
      (fun x => x 0 * (0 : ℝ)) = (1 - 1) / β ∧
    canonicalExpectation (volume.restrict unitIntervalDomain) β (fun _ => 0)
      (fun x => x 0 * (0 : ℝ)) ≠ 1 / β := by
  have hD : MeasurableSet unitIntervalDomain :=
    measurableSet_coordinateDomain 0 MeasurableSet.univ measurable_const measurable_const
  have hμ : volume.restrict unitIntervalDomain ≠ 0 := by
    rw [ne_eq, Measure.restrict_eq_zero, volume_unitIntervalDomain]
    norm_num
  have hw : IntegrableOn (boltzmannWeight β (fun _ : Fin 1 → ℝ => 0))
      unitIntervalDomain := by
    change IntegrableOn (fun _ => Real.exp (-β * (0 : ℝ))) unitIntervalDomain
    simp only [mul_zero, Real.exp_zero]
    exact integrableOn_const (by rw [volume_unitIntervalDomain]; norm_num)
  have hleft : IntegrableOn (fun x : Fin 1 → ℝ =>
      x 0 * (0 : ℝ) * boltzmannWeight β (fun _ => 0) x) unitIntervalDomain := by
    simp only [mul_zero, zero_mul]
    exact integrableOn_zero
  have hL : ∀ᵐ y : Fin 0 → ℝ, Tendsto
      (fun t => (Fin.insertNth (α := fun _ => ℝ) 0 t y) 0 *
        boltzmannWeight β (fun _ => 0) (Fin.insertNth (α := fun _ => ℝ) 0 t y))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    filter_upwards [] with y
    simpa [boltzmannWeight] using
      (continuousAt_id.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  have hR : ∀ᵐ y : Fin 0 → ℝ, Tendsto
      (fun t => (Fin.insertNth (α := fun _ => ℝ) 0 t y) 0 *
        boltzmannWeight β (fun _ => 0) (Fin.insertNth (α := fun _ => ℝ) 0 t y))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    filter_upwards [] with y
    simpa [boltzmannWeight] using
      (continuousAt_id.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ))))
  have h := generalized_equipartition_coordinateDomain_boundary 0 0 univ
    (fun _ : Fin 0 → ℝ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 1)
    β (fun _ => 0) (fun _ => 0) hβ MeasurableSet.univ hD
    (fun _ _ => by norm_num) hμ
    (fun _ _ t _ => hasDerivAt_const t 0) hw hleft
    (by simpa only [Measure.restrict_univ] using hL)
    (by simpa only [Measure.restrict_univ] using hR)
  have hflux : (∫ _ : Fin 0 → ℝ, (1 : ℝ) - 0) = 1 := by
    simp only [sub_zero, integral_const, smul_eq_mul, mul_one, measureReal_def]
    rw [volume_pi]
    simp
  simp only [ite_true, Measure.restrict_univ] at h
  rw [hflux] at h
  change canonicalExpectation (volume.restrict unitIntervalDomain) β (fun _ => 0)
    (fun x => x 0 * (0 : ℝ)) =
      (1 - 1 / partitionFunction (volume.restrict unitIntervalDomain) β (fun _ => 0)) / β at h
  rw [uniform_interval_partitionFunction, div_one] at h
  refine ⟨h, ?_⟩
  rw [h]
  exact ne_of_lt (by simpa using one_div_pos.mpr hβ)

end Equipartition
