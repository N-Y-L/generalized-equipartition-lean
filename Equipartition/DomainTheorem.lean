import Equipartition.Boundary
import Equipartition.MainTheorem

/-!
# Canonical equipartition with boundary terms

On a coordinate domain, normalized integration by parts includes the difference
of the weighted observable's endpoint traces. The partition function is positive
under an integrable weight and nonzero restricted volume.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Equipartition

/-- Normalized canonical identity on a domain with variable finite endpoints. -/
theorem canonical_coordinateDomain_identity {n : ℕ} (j : Fin (n + 1))
    (S : Set (Fin n → ℝ)) (a b L R : (Fin n → ℝ) → ℝ)
    (β : ℝ) (H A H' A' : (Fin (n + 1) → ℝ) → ℝ)
    (hS : MeasurableSet S) (hD : MeasurableSet (coordinateDomain j S a b))
    (hab : ∀ y ∈ S, a y < b y)
    (hμ : volume.restrict (coordinateDomain j S a b) ≠ 0)
    (hH : ∀ y ∈ S, ∀ t ∈ Ioo (a y) (b y),
      HasDerivAt (fun s => H (j.insertNth s y)) (H' (j.insertNth t y)) t)
    (hA : ∀ y ∈ S, ∀ t ∈ Ioo (a y) (b y),
      HasDerivAt (fun s => A (j.insertNth s y)) (A' (j.insertNth t y)) t)
    (hweight : IntegrableOn (boltzmannWeight β H) (coordinateDomain j S a b))
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
    β * canonicalExpectation (volume.restrict (coordinateDomain j S a b)) β H
        (fun x => A x * H' x) =
      canonicalExpectation (volume.restrict (coordinateDomain j S a b)) β H A' -
        (∫ y in S, R y - L y) /
          partitionFunction (volume.restrict (coordinateDomain j S a b)) β H := by
  letI : NeZero (volume.restrict (coordinateDomain j S a b)) := ⟨hμ⟩
  have hZ := partitionFunction_pos _ β H hweight
  have hw := weighted_coordinateDomain_identity j S a b L R β H A H' A'
    hS hD hab hH hA hleft hright hL hR
  unfold canonicalExpectation
  rw [← mul_div_assoc, ← sub_div]
  exact (div_left_inj' hZ.ne').2 hw

/-- Coordinate-pair equipartition with the boundary correction retained.
Only the selected directional derivative of the Hamiltonian is required. -/
theorem generalized_equipartition_coordinateDomain_boundary {n : ℕ}
    (i j : Fin (n + 1)) (S : Set (Fin n → ℝ)) (a b L R : (Fin n → ℝ) → ℝ)
    (β : ℝ) (H H' : (Fin (n + 1) → ℝ) → ℝ)
    (hβ : 0 < β) (hS : MeasurableSet S)
    (hD : MeasurableSet (coordinateDomain j S a b)) (hab : ∀ y ∈ S, a y < b y)
    (hμ : volume.restrict (coordinateDomain j S a b) ≠ 0)
    (hH : ∀ y ∈ S, ∀ t ∈ Ioo (a y) (b y),
      HasDerivAt (fun s => H (j.insertNth s y)) (H' (j.insertNth t y)) t)
    (hweight : IntegrableOn (boltzmannWeight β H) (coordinateDomain j S a b))
    (hmoment : IntegrableOn (fun x => x i * H' x * boltzmannWeight β H x)
      (coordinateDomain j S a b))
    (hL : ∀ᵐ y ∂volume.restrict S, Tendsto
      (fun t => (j.insertNth (α := fun _ => ℝ) t y) i *
        boltzmannWeight β H (j.insertNth t y)) (𝓝[>] (a y)) (𝓝 (L y)))
    (hR : ∀ᵐ y ∂volume.restrict S, Tendsto
      (fun t => (j.insertNth (α := fun _ => ℝ) t y) i *
        boltzmannWeight β H (j.insertNth t y)) (𝓝[<] (b y)) (𝓝 (R y))) :
    canonicalExpectation (volume.restrict (coordinateDomain j S a b)) β H
        (fun x => x i * H' x) =
      ((if i = j then 1 else 0) -
        (∫ y in S, R y - L y) /
          partitionFunction (volume.restrict (coordinateDomain j S a b)) β H) / β := by
  letI : NeZero (volume.restrict (coordinateDomain j S a b)) := ⟨hμ⟩
  have hZ := partitionFunction_pos _ β H hweight
  have hA (y : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun s => (j.insertNth (α := fun _ => ℝ) s y) i)
        (if i = j then 1 else 0) t := by
    simpa only [partialDeriv_coordinate] using
      hasDerivAt_slice j (fun x => x i) (differentiable_apply i) y t
  have h := canonical_coordinateDomain_identity j S a b L R β H (fun x => x i) H'
    (fun _ => if i = j then 1 else 0) hS hD hab hμ hH
    (fun y _ t _ => hA y t) hweight hmoment (hweight.const_mul _) hL hR
  have hc : canonicalExpectation (volume.restrict (coordinateDomain j S a b)) β H
      (fun _ => if i = j then 1 else 0) = if i = j then 1 else 0 := by
    rw [canonicalExpectation, integral_const_mul]
    exact mul_div_cancel_right₀ _ hZ.ne'
  rw [hc] at h
  exact (eq_div_iff hβ.ne').2 (by simpa only [mul_comm] using h)

end Equipartition
