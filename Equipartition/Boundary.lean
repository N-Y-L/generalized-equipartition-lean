import Equipartition.Multivariate

/-!
# Boundary terms on coordinate domains

A coordinate domain has an arbitrary measurable transverse set and an open interval
on each selected-coordinate slice. Its endpoints may vary with the other coordinates.
The fundamental theorem of calculus uses one-sided traces, so neither differentiability
nor finite values of the Hamiltonian at the endpoints are required.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Equipartition

/-- A domain whose selected-coordinate slices are variable open intervals. -/
def coordinateDomain {n : ℕ} (j : Fin (n + 1)) (S : Set (Fin n → ℝ))
    (a b : (Fin n → ℝ) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {x | j.removeNth x ∈ S ∧ x j ∈ Ioo (a (j.removeNth x)) (b (j.removeNth x))}

/-- Measurable endpoint functions define a measurable coordinate domain. -/
theorem measurableSet_coordinateDomain {n : ℕ} (j : Fin (n + 1))
    {S : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → ℝ}
    (hS : MeasurableSet S) (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet (coordinateDomain j S a b) := by
  have hr : Measurable (fun x : Fin (n + 1) → ℝ => j.removeNth x) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (j.succAbove i))
  exact (hS.preimage hr).inter
    ((measurableSet_lt (ha.comp hr) (measurable_pi_apply j)).inter
      (measurableSet_lt (measurable_pi_apply j) (hb.comp hr)))

/-- Improper FTC on an open bounded interval, expressed as a set integral. -/
theorem integral_Ioo_of_hasDerivAt_of_traces {a b L R : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hg : IntegrableOn g (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (g t) t)
    (hL : Tendsto f (𝓝[>] a) (𝓝 L)) (hR : Tendsto f (𝓝[<] b) (𝓝 R)) :
    ∫ t in Ioo a b, g t = R - L := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hd
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hg) hL hR
  rwa [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at hi

/-- Integrating a coordinate derivative gives the integral of the two slice traces.
All derivative and trace hypotheses concern only the domain's interior slices. -/
theorem integral_coordinateDomain_derivative {n : ℕ} (j : Fin (n + 1))
    (S : Set (Fin n → ℝ)) (a b L R : (Fin n → ℝ) → ℝ)
    (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hS : MeasurableSet S) (hD : MeasurableSet (coordinateDomain j S a b))
    (hab : ∀ y ∈ S, a y < b y)
    (hg : IntegrableOn g (coordinateDomain j S a b))
    (hd : ∀ y ∈ S, ∀ t ∈ Ioo (a y) (b y),
      HasDerivAt (fun s => f (j.insertNth s y)) (g (j.insertNth t y)) t)
    (hL : ∀ᵐ y ∂volume.restrict S,
      Tendsto (fun t => f (j.insertNth t y)) (𝓝[>] (a y)) (𝓝 (L y)))
    (hR : ∀ᵐ y ∂volume.restrict S,
      Tendsto (fun t => f (j.insertNth t y)) (𝓝[<] (b y)) (𝓝 (R y))) :
    ∫ x in coordinateDomain j S a b, g x = ∫ y in S, R y - L y := by
  classical
  let D := coordinateDomain j S a b
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
  have he : MeasurePreserving e := (volume_preserving_piFinSuccAbove _ j).symm
  have hge : Integrable (fun p : ℝ × (Fin n → ℝ) => D.indicator g (e p)) :=
    he.integrable_comp_of_integrable (hg.integrable_indicator hD)
  have hslice (y : Fin n → ℝ) (hy : y ∈ S) :
      (fun t => D.indicator g (e (t, y))) =
        (Ioo (a y) (b y)).indicator (fun t => g (j.insertNth t y)) := by
    funext t
    simp [D, coordinateDomain, e, Fin.insertNthEquiv, indicator, hy]
  rw [← integral_indicator hD, ← he.integral_comp']
  change (∫ p, D.indicator g (e p) ∂(volume.prod volume)) = _
  rw [integral_prod_symm _ hge, ← integral_indicator hS]
  apply integral_congr_ae
  have hL' := (ae_restrict_iff' hS).mp hL
  have hR' := (ae_restrict_iff' hS).mp hR
  filter_upwards [hge.prod_left_ae, hL', hR'] with y hgy hLy hRy
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, hslice y hy, integral_indicator measurableSet_Ioo]
    apply integral_Ioo_of_hasDerivAt_of_traces (hab y hy)
    · exact (integrable_indicator_iff measurableSet_Ioo).mp ((hslice y hy) ▸ hgy)
    · exact hd y hy
    · exact hLy hy
    · exact hRy hy
  · simp [D, coordinateDomain, e, Fin.insertNthEquiv, indicator, hy]

/-- Canonical integration by parts on a coordinate domain, retaining boundary flux.
The supplied derivatives need exist only along interior slices. -/
theorem weighted_coordinateDomain_identity {n : ℕ} (j : Fin (n + 1))
    (S : Set (Fin n → ℝ)) (a b L R : (Fin n → ℝ) → ℝ)
    (β : ℝ) (H A H' A' : (Fin (n + 1) → ℝ) → ℝ)
    (hS : MeasurableSet S) (hD : MeasurableSet (coordinateDomain j S a b))
    (hab : ∀ y ∈ S, a y < b y)
    (hH : ∀ y ∈ S, ∀ t ∈ Ioo (a y) (b y),
      HasDerivAt (fun s => H (j.insertNth s y)) (H' (j.insertNth t y)) t)
    (hA : ∀ y ∈ S, ∀ t ∈ Ioo (a y) (b y),
      HasDerivAt (fun s => A (j.insertNth s y)) (A' (j.insertNth t y)) t)
    (hleft : IntegrableOn (fun x => A x * H' x * boltzmannWeight β H x)
      (coordinateDomain j S a b))
    (hright : IntegrableOn (fun x => A' x * boltzmannWeight β H x)
      (coordinateDomain j S a b))
    (hL : ∀ᵐ y ∂volume.restrict S, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y))
      (𝓝[>] (a y)) (𝓝 (L y)))
    (hR : ∀ᵐ y ∂volume.restrict S, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y))
      (𝓝[<] (b y)) (𝓝 (R y))) :
    β * (∫ x in coordinateDomain j S a b, A x * H' x * boltzmannWeight β H x) =
      (∫ x in coordinateDomain j S a b, A' x * boltzmannWeight β H x) -
        ∫ y in S, R y - L y := by
  have hz := integral_coordinateDomain_derivative j S a b L R
    (fun x => A x * boltzmannWeight β H x)
    (fun x => A' x * boltzmannWeight β H x -
      β * (A x * H' x * boltzmannWeight β H x))
    hS hD hab (hright.sub (hleft.const_mul β))
    (fun y hy t ht => hasDerivAt_observable_boltzmann (hH y hy t ht) (hA y hy t ht))
    hL hR
  rw [integral_sub hright (hleft.const_mul β), integral_const_mul] at hz
  linarith

end Equipartition
