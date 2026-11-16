module

public import QuantitativeMaassWindowMajorantV1
public import QuantitativeMaassWindowIdentityTermV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeNinaMaass

/-- A positive normalization at every center, agreeing eventually with
the proved first-moment normalization. No conditions at small centers
are imposed on the original width function. -/
def windowEnergyDenominator (K : SchwartzMap ℝ ℝ) (ε : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (1 / 2) (1 - (∫ u, |u| * K u) /
    (positiveWindowRadius ε t * smoothingWidth (slowScale t) (ε t)))

theorem windowEnergyDenominator_pos (K : SchwartzMap ℝ ℝ) (ε : ℝ → ℝ) (t : ℝ) :
    0 < windowEnergyDenominator K ε t :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_left _ _)

theorem windowEnergyDenominator_tendsto (K : SchwartzMap ℝ ℝ) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (windowEnergyDenominator K ε) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))).max
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
      (window_majorant_loss_tendsto K ε hε hproduct))
  norm_num only [sub_zero, max_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 1)] at h
  exact h

theorem windowEnergyDenominator_eventually (K : SchwartzMap ℝ ℝ) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    ∀ᶠ t in atTop, windowEnergyDenominator K ε t =
      1 - (∫ u, |u| * K u) /
        (positiveWindowRadius ε t * smoothingWidth (slowScale t) (ε t)) := by
  filter_upwards [(window_majorant_loss_tendsto K ε hε hproduct).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with t ht
  exact max_eq_right (by linarith)

/-- The literal compact time profile for the normalized enlarged window,
at the manuscript radius and buffer. -/
def originalWindowMajorant (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) (ε : ℝ → ℝ) (t : ℝ) :
    SchwartzMap ℝ ℂ :=
  ((windowEnergyDenominator K ε t)⁻¹ : ℂ) •
    windowTimeSchwartz K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
      (t - smoothingWidth (slowScale t) (ε t))
      (t + ε t + smoothingWidth (slowScale t) (ε t))

theorem originalWindowMajorant_compact (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) (ε : ℝ → ℝ) (t : ℝ) :
    HasCompactSupport (originalWindowMajorant K hc ε t : ℝ → ℂ) := by
  exact (symmetricWindowTimeTest_compact K hc (positiveWindowRadius ε t) _ _
    (positiveWindowRadius_pos ε t)).smul_left

theorem originalWindowMajorant_even (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) (ε : ℝ → ℝ) (t : ℝ) :
    Function.Even (originalWindowMajorant K hc ε t) := by
  intro s
  change ((windowEnergyDenominator K ε t)⁻¹ : ℂ) *
    symmetricWindowTimeTest K (positiveWindowRadius ε t) _ _ (-s) = _
  rw [symmetricWindowTimeTest_even K he]
  rfl

theorem originalWindowMajorant_real (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) (ε : ℝ → ℝ) (t s : ℝ) :
    star (originalWindowMajorant K hc ε t s) = originalWindowMajorant K hc ε t s := by
  change star (((windowEnergyDenominator K ε t)⁻¹ : ℂ) *
    symmetricWindowTimeTest K (positiveWindowRadius ε t) _ _ s) = _
  have ha : star ((windowEnergyDenominator K ε t)⁻¹ : ℂ) =
      ((windowEnergyDenominator K ε t)⁻¹ : ℂ) := by simp
  rw [star_mul, ha, symmetricWindowTimeTest_real K he]
  exact mul_comm _ _

/-- One fixed multiplier of the manuscript radius controls the support
for every center and width, including the harmless global extension. -/
theorem originalWindowMajorant_support (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) :
    ∃ B : ℝ, 0 < B ∧ ∀ (ε : ℝ → ℝ) (t : ℝ),
      Function.support (originalWindowMajorant K hc ε t) ⊆
        Icc (-(B * positiveWindowRadius ε t)) (B * positiveWindowRadius ε t) := by
  obtain ⟨B, hB, hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  refine ⟨B, hB, ?_⟩
  intro ε t s hmem
  apply hs _ (positiveWindowRadius_pos ε t) _ _
  intro hz
  apply hmem
  change ((windowEnergyDenominator K ε t)⁻¹ : ℂ) *
    symmetricWindowTimeTest K (positiveWindowRadius ε t) _ _ s = 0
  rw [hz, mul_zero]

theorem cosinePacket_const_mul (f : ℝ → ℂ) (a : ℂ) (r : ℝ) :
    cosinePacket (fun s => a * f s) r = a * cosinePacket f r := by
  unfold cosinePacket
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  ring

/-- Exact cosine multiplier of the actual normalized time profile. -/
theorem originalWindowMajorant_cosine (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) (ε : ℝ → ℝ) (t r : ℝ)
    (ht : 0 < t - smoothingWidth (slowScale t) (ε t)) :
    cosinePacket (originalWindowMajorant K hc ε t) r =
      ((smoothedWindow K (positiveWindowRadius ε t)
        (Icc (t - smoothingWidth (slowScale t) (ε t))
          (t + ε t + smoothingWidth (slowScale t) (ε t)) ∪
        Icc (-(t + ε t + smoothingWidth (slowScale t) (ε t)))
          (-(t - smoothingWidth (slowScale t) (ε t)))) r /
        windowEnergyDenominator K ε t : ℝ) : ℂ) := by
  change cosinePacket (fun s => ((windowEnergyDenominator K ε t)⁻¹ : ℂ) *
    symmetricWindowTimeTest K (positiveWindowRadius ε t) _ _ s) r = _
  rw [cosinePacket_const_mul,
    symmetricWindowTimeTest_cosinePacket K he hc _ _ _ r (positiveWindowRadius_pos ε t) ht]
  push_cast
  ring

/-- Original hypotheses suffice for the positive buffer and the
enlarged interval to stay on the positive spectral line. -/
theorem originalWindowMajorant_parameters (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    ∀ᶠ t in atTop, 0 < smoothingWidth (slowScale t) (ε t) ∧
      2 * smoothingWidth (slowScale t) (ε t) ≤ ε t ∧
      0 < t - smoothingWidth (slowScale t) (ε t) := by
  have hsmall := (shrinking_window_parameters ε (hε.mono (fun _ h => h.1)) hproduct).2.2.1
  filter_upwards [hε, slowScale_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (1 : ℝ)] with t het hL hb ht
  have hp : 0 < propagation (slowScale t) (ε t) := Real.sqrt_pos.mpr (div_pos hL het.1)
  have hbp : 0 < smoothingWidth (slowScale t) (ε t) := Real.sqrt_pos.mpr (div_pos het.1 hp)
  have hble := (div_lt_iff₀ het.1).mp hb
  exact ⟨hbp, by linarith, by linarith⟩

/-- The constructed even real compact smooth test majorizes one on the
literal original window, without regularity assumptions on its width. -/
theorem originalWindowMajorant_majorizes (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    ∀ᶠ t in atTop, ∀ r ∈ Icc t (t + ε t),
      1 ≤ (cosinePacket (originalWindowMajorant K hc ε t) r).re := by
  filter_upwards [originalWindowMajorant_parameters ε hε hproduct,
    windowEnergyDenominator_eventually K ε (hε.mono (fun _ h => h.1)) hproduct]
      with t ht hd
  intro r hr
  rw [originalWindowMajorant_cosine K he hc ε t r ht.2.2, Complex.ofReal_re]
  apply (le_div_iff₀ (windowEnergyDenominator_pos K ε t)).mpr
  rw [one_mul, hd]
  simpa only [pow_one] using enlarged_symmetricWindow_lower K hK hm _
    (positiveWindowRadius_pos ε t) t (t + ε t) _ r ht.1 hr 1

/-- The fixed support multiplier does not alter the required
little-o propagation scale. -/
theorem originalWindowMajorant_radius_limit (B : ℝ) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => B * positiveWindowRadius ε t / slowScale t) atTop (𝓝 0) := by
  simpa only [mul_div_assoc, mul_zero] using
    (positiveWindowRadius_div_scale ε hε hproduct).const_mul B

#print axioms windowEnergyDenominator_pos
#print axioms windowEnergyDenominator_tendsto
#print axioms windowEnergyDenominator_eventually
#print axioms originalWindowMajorant_compact
#print axioms originalWindowMajorant_even
#print axioms originalWindowMajorant_real
#print axioms originalWindowMajorant_support
#print axioms cosinePacket_const_mul
#print axioms originalWindowMajorant_cosine
#print axioms originalWindowMajorant_parameters
#print axioms originalWindowMajorant_majorizes
#print axioms originalWindowMajorant_radius_limit

end QuantitativeNinaMaass
