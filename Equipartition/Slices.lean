import Equipartition.Multivariate
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Equipartition under coordinate-slice regularity

Only the selected coordinate derivative is needed. Almost every transverse
slice must be continuous and differentiable outside a countable set, which
may depend on the slice. The derivative need not be continuous. Integrability
and boundary conditions remain explicit.
-/

open MeasureTheory Filter Set
open scoped Topology Interval

namespace Equipartition

/-- Whole-line fundamental theorem of calculus for a continuous function
with an integrable derivative outside a countable exceptional set. -/
theorem integral_derivative_off_countable
    {f g : ℝ → ℝ} {s : Set ℝ} {left right : ℝ}
    (hc : Continuous f) (hs : s.Countable)
    (hd : ∀ t ∉ s, HasDerivAt f (g t) t) (hg : Integrable g)
    (hb : Tendsto f atBot (𝓝 left)) (ht : Tendsto f atTop (𝓝 right)) :
    (∫ t, g t) = right - left := by
  have hFTC (a b : ℝ) : (∫ t in a..b, g t) = f b - f a :=
    integral_eq_of_hasDerivAt_off_countable f g hs hc.continuousOn
      (fun t ht => hd t ht.2) hg.intervalIntegrable
  have hlim := intervalIntegral_tendsto_integral hg
    (tendsto_neg_atTop_atBot : Tendsto (fun t : ℝ => -t) atTop atBot)
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  simp_rw [hFTC] at hlim
  exact tendsto_nhds_unique hlim (ht.sub (hb.comp tendsto_neg_atTop_atBot))

/-- Integrability of both the continuous function and its derivative removes
the boundary term, including at countably many nondifferentiable points. -/
theorem integral_derivative_off_countable_of_integrable
    {f g : ℝ → ℝ} {s : Set ℝ}
    (hc : Continuous f) (hs : s.Countable)
    (hd : ∀ t ∉ s, HasDerivAt f (g t) t)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ t, g t) = 0 := by
  have hFTC (a b : ℝ) : (∫ t in a..b, g t) = f b - f a :=
    integral_eq_of_hasDerivAt_off_countable f g hs hc.continuousOn
      (fun t ht => hd t ht.2) hg.intervalIntegrable
  have htop : Tendsto f atTop (𝓝 ((∫ t in Ioi 0, g t) + f 0)) := by
    have hlim := (intervalIntegral_tendsto_integral_Ioi 0 hg.integrableOn
      (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)).add_const (f 0)
    simpa only [hFTC, sub_add_cancel] using hlim
  have hbot : Tendsto f atBot (𝓝 (f 0 - ∫ t in Iic 0, g t)) := by
    have hlim := (intervalIntegral_tendsto_integral_Iic 0 hg.integrableOn
      (tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot)).const_sub (f 0)
    simpa only [hFTC, sub_sub_cancel] using hlim
  have hztop : (∫ t in Ioi 0, g t) + f 0 = 0 := by
    apply (hf.integrableAtFilter atTop).eq_zero_of_tendsto ?_ htop
    intro u hu
    obtain ⟨b, hb⟩ := mem_atTop_sets.mp hu
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb
  have hzbot : f 0 - (∫ t in Iic 0, g t) = 0 := by
    apply (hf.integrableAtFilter atBot).eq_zero_of_tendsto ?_ hbot
    intro u hu
    obtain ⟨b, hb⟩ := mem_atBot_sets.mp hu
    rw [← top_le_iff, ← Real.volume_Iic (a := b)]
    exact measure_mono hb
  rw [hztop] at htop
  rw [hzbot] at hbot
  simpa using integral_derivative_off_countable hc hs hd hg hbot htop

/-- A supplied derivative along almost every coordinate line. Each such slice
is continuous and differentiable outside a countable set; no transverse
differentiability is required. -/
def HasAESliceDeriv {n : ℕ} (j : Fin (n + 1))
    (f g : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  ∀ᵐ y : Fin n → ℝ,
    Continuous (fun t : ℝ => f (j.insertNth t y)) ∧
      ∃ s : Set ℝ, s.Countable ∧
        ∀ t ∉ s, HasDerivAt (fun u => f (j.insertNth u y)) (g (j.insertNth t y)) t

/-- An everywhere differentiable function satisfies the slice hypotheses. -/
theorem hasAESliceDeriv_of_differentiable {n : ℕ} (j : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Differentiable ℝ f) :
    HasAESliceDeriv j f (partialDeriv j f) := by
  filter_upwards with y
  refine ⟨?_, ∅, countable_empty, fun t _ => hasDerivAt_slice j f hf y t⟩
  exact continuous_iff_continuousAt.mpr fun t => (hasDerivAt_slice j f hf y t).continuousAt

/-- Integrate a slice derivative under vanishing limits on almost every line. -/
theorem integral_eq_zero_of_ae_slice_derivative {n : ℕ}
    (j : Fin (n + 1)) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hd : HasAESliceDeriv j f g) (hg : Integrable g)
    (hb : ∀ᵐ y : Fin n → ℝ, Tendsto (fun t => f (j.insertNth t y)) atBot (𝓝 0))
    (ht : ∀ᵐ y : Fin n → ℝ, Tendsto (fun t => f (j.insertNth t y)) atTop (𝓝 0)) :
    (∫ x, g x) = 0 := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
  have he : MeasurePreserving e := (volume_preserving_piFinSuccAbove _ j).symm
  have hge : Integrable (fun p : ℝ × (Fin n → ℝ) => g (e p)) :=
    he.integrable_comp_of_integrable hg
  rw [← he.integral_comp' g]
  change (∫ p, g (e p) ∂(volume.prod volume)) = 0
  rw [integral_prod_symm _ hge]
  have hz : ∀ᵐ y : Fin n → ℝ, (∫ t : ℝ, g (e (t, y))) = 0 := by
    filter_upwards [hd, hge.prod_left_ae, hb, ht] with y hy hgy hby hty
    obtain ⟨hcy, s, hs, hdy⟩ := hy
    simpa using integral_derivative_off_countable hcy hs hdy hgy hby hty
  simpa using integral_congr_ae hz

/-- Integrability supplies zero boundary terms for almost every regular slice. -/
theorem integral_eq_zero_of_ae_slice_derivative_of_integrable {n : ℕ}
    (j : Fin (n + 1)) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hd : HasAESliceDeriv j f g) (hf : Integrable f) (hg : Integrable g) :
    (∫ x, g x) = 0 := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
  have he : MeasurePreserving e := (volume_preserving_piFinSuccAbove _ j).symm
  have hfe : Integrable (fun p : ℝ × (Fin n → ℝ) => f (e p)) :=
    he.integrable_comp_of_integrable hf
  have hge : Integrable (fun p : ℝ × (Fin n → ℝ) => g (e p)) :=
    he.integrable_comp_of_integrable hg
  rw [← he.integral_comp' g]
  change (∫ p, g (e p) ∂(volume.prod volume)) = 0
  rw [integral_prod_symm _ hge]
  have hz : ∀ᵐ y : Fin n → ℝ, (∫ t : ℝ, g (e (t, y))) = 0 := by
    filter_upwards [hd, hge.prod_left_ae, hfe.prod_left_ae] with y hy hgy hfy
    obtain ⟨hcy, s, hs, hdy⟩ := hy
    exact integral_derivative_off_countable_of_integrable hcy hs hdy hfy hgy
  simpa using integral_congr_ae hz

/-- Product and chain rules preserve the almost-everywhere slice hypotheses. -/
theorem HasAESliceDeriv.observable_boltzmann {n : ℕ} {j : Fin (n + 1)}
    {H A H' A' : (Fin (n + 1) → ℝ) → ℝ} (β : ℝ)
    (hH : HasAESliceDeriv j H H') (hA : HasAESliceDeriv j A A') :
    HasAESliceDeriv j (fun x => A x * boltzmannWeight β H x)
      (fun x => A' x * boltzmannWeight β H x -
        β * (A x * H' x * boltzmannWeight β H x)) := by
  filter_upwards [hH, hA] with y hyH hyA
  obtain ⟨hcH, sH, hsH, hdH⟩ := hyH
  obtain ⟨hcA, sA, hsA, hdA⟩ := hyA
  refine ⟨hcA.mul ((continuous_const.mul hcH).rexp), sH ∪ sA, hsH.union hsA, ?_⟩
  intro t ht
  exact hasDerivAt_observable_boltzmann (hdH t (fun h => ht (Or.inl h)))
    (hdA t (fun h => ht (Or.inr h)))

/-- Canonical integration by parts from derivatives along almost every line,
allowing a countable set of derivative exceptions on each regular slice. -/
theorem weighted_slice_identity {n : ℕ} (j : Fin (n + 1))
    (β : ℝ) (H A H' A' : (Fin (n + 1) → ℝ) → ℝ)
    (hH : HasAESliceDeriv j H H') (hA : HasAESliceDeriv j A A')
    (hleft : Integrable (fun x => A x * H' x * boltzmannWeight β H x))
    (hright : Integrable (fun x => A' x * boltzmannWeight β H x))
    (hbot : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y)) atBot (𝓝 0))
    (htop : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y)) atTop (𝓝 0)) :
    β * (∫ x, A x * H' x * boltzmannWeight β H x) =
      ∫ x, A' x * boltzmannWeight β H x := by
  have hz := integral_eq_zero_of_ae_slice_derivative j _ _
    (hH.observable_boltzmann β hA) (hright.sub (hleft.const_mul β)) hbot htop
  rw [integral_sub hright (hleft.const_mul β), integral_const_mul] at hz
  linarith

/-- The slice identity with integrability of the weighted observable in place
of explicit boundary limits. -/
theorem weighted_slice_identity_of_integrable {n : ℕ} (j : Fin (n + 1))
    (β : ℝ) (H A H' A' : (Fin (n + 1) → ℝ) → ℝ)
    (hH : HasAESliceDeriv j H H') (hA : HasAESliceDeriv j A A')
    (hleft : Integrable (fun x => A x * H' x * boltzmannWeight β H x))
    (hright : Integrable (fun x => A' x * boltzmannWeight β H x))
    (hobs : Integrable (fun x => A x * boltzmannWeight β H x)) :
    β * (∫ x, A x * H' x * boltzmannWeight β H x) =
      ∫ x, A' x * boltzmannWeight β H x := by
  have hz := integral_eq_zero_of_ae_slice_derivative_of_integrable j _ _
    (hH.observable_boltzmann β hA) hobs (hright.sub (hleft.const_mul β))
  rw [integral_sub hright (hleft.const_mul β), integral_const_mul] at hz
  linarith

/-- Normalized observable identity under almost-everywhere slice regularity. -/
theorem canonical_slice_identity {n : ℕ} (j : Fin (n + 1))
    (β : ℝ) (H A H' A' : (Fin (n + 1) → ℝ) → ℝ)
    (hH : HasAESliceDeriv j H H') (hA : HasAESliceDeriv j A A')
    (_hweight : Integrable (boltzmannWeight β H))
    (hleft : Integrable (fun x => A x * H' x * boltzmannWeight β H x))
    (hright : Integrable (fun x => A' x * boltzmannWeight β H x))
    (hbot : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y)) atBot (𝓝 0))
    (htop : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => A (j.insertNth t y) * boltzmannWeight β H (j.insertNth t y)) atTop (𝓝 0)) :
    β * canonicalExpectation volume β H (fun x => A x * H' x) =
      canonicalExpectation volume β H A' := by
  unfold canonicalExpectation
  rw [← mul_div_assoc, weighted_slice_identity j β H A H' A' hH hA
    hleft hright hbot htop]

/-- Normalized slice identity with integrability of the weighted observable. -/
theorem canonical_slice_identity_of_integrable {n : ℕ} (j : Fin (n + 1))
    (β : ℝ) (H A H' A' : (Fin (n + 1) → ℝ) → ℝ)
    (hH : HasAESliceDeriv j H H') (hA : HasAESliceDeriv j A A')
    (_hweight : Integrable (boltzmannWeight β H))
    (hleft : Integrable (fun x => A x * H' x * boltzmannWeight β H x))
    (hright : Integrable (fun x => A' x * boltzmannWeight β H x))
    (hobs : Integrable (fun x => A x * boltzmannWeight β H x)) :
    β * canonicalExpectation volume β H (fun x => A x * H' x) =
      canonicalExpectation volume β H A' := by
  unfold canonicalExpectation
  rw [← mul_div_assoc, weighted_slice_identity_of_integrable j β H A H' A' hH hA
    hleft hright hobs]

/-- Coordinates have the Kronecker-delta slice derivative. -/
theorem hasAESliceDeriv_coordinate {n : ℕ} (i j : Fin (n + 1)) :
    HasAESliceDeriv j (fun x => x i) (fun _ => if i = j then 1 else 0) := by
  have hd : partialDeriv j (fun x : Fin (n + 1) → ℝ => x i) =
      (fun _ => if i = j then 1 else 0) := by
    funext x
    rw [partialDeriv, (hasFDerivAt_apply i x).fderiv]
    simp [Pi.single_apply]
  simpa only [hd] using hasAESliceDeriv_of_differentiable j _ (differentiable_apply i)

/-- The coordinate-pair law requires only almost-everywhere slice regularity
of the Hamiltonian in coordinate `j`. -/
theorem generalized_equipartition_slices {n : ℕ} (i j : Fin (n + 1))
    (β : ℝ) (H H' : (Fin (n + 1) → ℝ) → ℝ)
    (hβ : β ≠ 0) (hH : HasAESliceDeriv j H H')
    (hweight : Integrable (boltzmannWeight β H))
    (hmoment : Integrable (fun x => x i * H' x * boltzmannWeight β H x))
    (hbot : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => (j.insertNth (α := fun _ => ℝ) t y) i *
        boltzmannWeight β H (j.insertNth t y)) atBot (𝓝 0))
    (htop : ∀ᵐ y : Fin n → ℝ, Tendsto
      (fun t => (j.insertNth (α := fun _ => ℝ) t y) i *
        boltzmannWeight β H (j.insertNth t y)) atTop (𝓝 0)) :
    canonicalExpectation volume β H (fun x => x i * H' x) =
      (if i = j then 1 else 0) / β := by
  have h := weighted_slice_identity j β H (fun x => x i) H'
    (fun _ => if i = j then 1 else 0) hH (hasAESliceDeriv_coordinate i j)
    hmoment (hweight.const_mul _) hbot htop
  rw [integral_const_mul] at h
  have hZ := partitionFunction_pos volume β H hweight
  unfold canonicalExpectation
  apply (div_eq_div_iff hZ.ne' hβ).2
  simpa only [partitionFunction, mul_comm] using h

/-- The coordinate-pair law with integrability of the weighted coordinate
in place of explicit limits at infinity. -/
theorem generalized_equipartition_slices_of_integrable {n : ℕ}
    (i j : Fin (n + 1)) (β : ℝ) (H H' : (Fin (n + 1) → ℝ) → ℝ)
    (hβ : β ≠ 0) (hH : HasAESliceDeriv j H H')
    (hweight : Integrable (boltzmannWeight β H))
    (hmoment : Integrable (fun x => x i * H' x * boltzmannWeight β H x))
    (hcoordinate : Integrable (fun x => x i * boltzmannWeight β H x)) :
    canonicalExpectation volume β H (fun x => x i * H' x) =
      (if i = j then 1 else 0) / β := by
  have h := weighted_slice_identity_of_integrable j β H (fun x => x i) H'
    (fun _ => if i = j then 1 else 0) hH (hasAESliceDeriv_coordinate i j)
    hmoment (hweight.const_mul _) hcoordinate
  rw [integral_const_mul] at h
  have hZ := partitionFunction_pos volume β H hweight
  unfold canonicalExpectation
  apply (div_eq_div_iff hZ.ne' hβ).2
  simpa only [partitionFunction, mul_comm] using h

/-- Absolute value satisfies the slice regularity condition despite its cusp.
This is a regularity result; canonical integrability is a separate hypothesis. -/
theorem hasAESliceDeriv_abs_coordinate {n : ℕ} (j : Fin (n + 1)) :
    HasAESliceDeriv j (fun x => |x j|) (fun x => (SignType.sign (x j) : ℝ)) := by
  filter_upwards with y
  refine ⟨?_, {0}, countable_singleton 0, ?_⟩
  · simpa using (continuous_abs : Continuous (abs : ℝ → ℝ))
  · intro t ht
    simpa using hasDerivAt_abs (show t ≠ 0 from fun h => ht (by simp [h]))

end Equipartition
