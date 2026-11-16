module

public import QuantitativeNinaMaassWindowEnergyV1
public import QuantitativeMaassEnlargedUpperTraceV1
public import QuantitativeMaassEnlargedIdentityLimitV1
public import QuantitativeMaassUpperTailLimitV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace FourierTransform SchwartzMap

namespace QuantitativeNinaMaass

/-- The original triple-log propagation radius also satisfies the weaker
sublogarithmic condition needed by the geometric upper trace estimate. -/
theorem originalWindowRadius_div_log (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => positiveWindowRadius ε t / Real.log t) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (positiveWindowRadius_div_scale ε hε hproduct)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact div_nonneg (positiveWindowRadius_pos ε t).le (Real.log_pos ht).le
  · filter_upwards [exp_slowScale_le_eventually,
      slowScale_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
      eventually_gt_atTop (1 : ℝ)] with t he hL ht
    have hlog : slowScale t ≤ Real.log t :=
      (Real.le_log_iff_exp_le (by linarith : 0 < t)).mpr he
    exact div_le_div_of_nonneg_left (positiveWindowRadius_pos ε t).le hL hlog

/-- At the literal manuscript schedule the buffer eventually exceeds
the inverse propagation radius, as required by the checked identity term. -/
theorem originalWindowRadius_inverse_le_buffer (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    ∀ᶠ t in atTop, 1 / positiveWindowRadius ε t ≤ smoothingWidth (slowScale t) (ε t) := by
  filter_upwards [(positiveWindowRadius_smoothing_product ε hε hproduct).eventually
    (eventually_ge_atTop (1 : ℝ))] with t ht
  exact (div_le_iff₀ (positiveWindowRadius_pos ε t)).mpr (by simpa only [mul_comm] using ht)

/-- The checked geometric trace gives its sharp full-cusp upper coefficient
at the original radius and buffer. No stronger width or leakage hypothesis
is introduced. The fixed-parity new coefficient is a subsequent step. -/
theorem originalWindow_enlarged_upper_limit {ι : Type*}
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcus : ∀ i, v i ∈ localCuspidalSpace N hN)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    ∃ U : ℝ → ℝ, Tendsto U atTop (𝓝 ((quotientMeasure N).real univ / (2 * Real.pi))) ∧
      ∀ᶠ t in atTop,
        (∑' i, ‖windowWavePacket N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          (t - smoothingWidth (slowScale t) (ε t))
          (t + ε t + smoothingWidth (slowScale t) (ε t)) (v i)‖ ^ 2) / (t * ε t) ≤ U t := by
  obtain ⟨H, A, B, C, D, hH, hA, hB, hC, hD, hbound⟩ :=
    windowWavePacket_enlarged_upper_trace (ι := ι) N hN K he hc
  have hep : ∀ᶠ t in atTop, 0 < ε t := hε.mono (fun _ h => h.1)
  have htrim := originalWindowMajorant_parameters ε hε hproduct
  have hR := originalWindowRadius_div_log ε hep hproduct
  have hheight := upperCuspHeight_admissible (positiveWindowRadius ε) H hH hR
  let I := fun t => (windowIdentityContribution K hc (positiveWindowRadius ε t)
    (positiveWindowRadius_pos ε t) (t - smoothingWidth (slowScale t) (ε t))
      (t + ε t + smoothingWidth (slowScale t) (ε t))).re / (t * ε t)
  let E := fun t => C * Real.sqrt t * (ε t)^2 * Real.exp (A * positiveWindowRadius ε t) *
    (1 + Real.sqrt (upperCuspHeight t)) / (t * ε t)
  let F := fun t => (D * (positiveWindowRadius ε t)^3 * (ε t)^2 * t * Real.sqrt t *
    Real.exp (B * positiveWindowRadius ε t) / upperCuspHeight t) / (t * ε t)
  have hI : Tendsto I atTop (𝓝 (1 / (2 * Real.pi))) :=
    windowIdentityContribution_enlarged_normalized K he hc hK hm ε hε
      (fun t => smoothingWidth (slowScale t) (ε t))
      (htrim.mono (fun _ h => ⟨h.1.le, h.2.1⟩))
      (positiveWindowRadius ε) (positiveWindowRadius_pos ε)
      (Eventually.of_forall (fun _ => le_max_left _ _))
      (originalWindowRadius_inverse_le_buffer ε hep hproduct)
      (shrinking_window_parameters ε hep hproduct).2.2.1 hproduct
  have hE : Tendsto E atTop (𝓝 0) :=
    upper_core_error_tendsto ε (positiveWindowRadius ε) A C hA.le hC hε hR
  have hF : Tendsto F atTop (𝓝 0) :=
    upper_tail_error_tendsto ε (positiveWindowRadius ε) B D hB.le hD hε
      (Eventually.of_forall (fun t => (positiveWindowRadius_pos ε t).le)) hR
  refine ⟨fun t => I t * (quotientMeasure N).real univ + E t + F t, ?_, ?_⟩
  · convert ((hI.mul_const ((quotientMeasure N).real univ)).add hE).add hF using 1
    congr 1
    ring
  · filter_upwards [hε, htrim, hheight, eventually_ge_atTop (1 : ℝ)] with t het hdt hyt ht
    have hh := hbound (positiveWindowRadius ε t) (le_max_left _ _)
      (ε t) (smoothingWidth (slowScale t) (ε t)) t het.1.le het.2 hdt.1.le hdt.2.1 ht
      v hv hcus (upperCuspHeight t) hyt.1 hyt.2
    have hb := div_le_div_of_nonneg_right hh (mul_pos (show 0 < t by linarith) het.1).le
    convert hb using 1
    dsimp [I, E, F]
    ring

/-- The actual compact profile multiplies the actual geometric packet by
the stated positive normalization; this is an integral identity on the
whole automorphic Hilbert space, including exceptional spectrum. -/
theorem originalWindowMajorant_packet (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) (ε : ℝ → ℝ) (t : ℝ)
    (v : AutomorphicSpace N) :
    Wave.shiftedQuotientWavePacket N (originalWindowMajorant K hc ε t)
      (compactSmoothWaveWeight _ ((originalWindowMajorant K hc ε t).smooth ⊤)
        (originalWindowMajorant_compact K hc ε t)) v =
      ((windowEnergyDenominator K ε t)⁻¹ : ℂ) •
        windowWavePacket N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          (t - smoothingWidth (slowScale t) (ε t))
          (t + ε t + smoothingWidth (slowScale t) (ε t)) v := by
  change (∫ s, (((windowEnergyDenominator K ε t)⁻¹ : ℂ) *
    symmetricWindowTimeTest K (positiveWindowRadius ε t) _ _ s) •
      Wave.shiftedQuotientWave N s v) =
    ((windowEnergyDenominator K ε t)⁻¹ : ℂ) •
      ∫ s, symmetricWindowTimeTest K (positiveWindowRadius ε t) _ _ s •
        Wave.shiftedQuotientWave N s v
  simp_rw [mul_smul]
  exact integral_smul _ _

/-- Positive normalization tends to one, so the literal majorant packet
has the same sharp full-cusp upper coefficient at the manuscript radius. -/
theorem originalWindowMajorant_cuspidal_upper_limit {ι : Type*}
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcus : ∀ i, v i ∈ localCuspidalSpace N hN)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    ∃ U : ℝ → ℝ, Tendsto U atTop (𝓝 ((quotientMeasure N).real univ / (2 * Real.pi))) ∧
      ∀ᶠ t in atTop,
        (∑' i, ‖Wave.shiftedQuotientWavePacket N (originalWindowMajorant K hc ε t)
          (compactSmoothWaveWeight _ ((originalWindowMajorant K hc ε t).smooth ⊤)
            (originalWindowMajorant_compact K hc ε t)) (v i)‖ ^ 2) / (t * ε t) ≤ U t := by
  obtain ⟨U, hU, hbound⟩ := originalWindow_enlarged_upper_limit N hN K he hc hK hm v hv hcus ε hε hproduct
  have hd := (windowEnergyDenominator_tendsto K ε (hε.mono (fun _ h => h.1)) hproduct).inv₀
    (by norm_num : (1 : ℝ) ≠ 0)
  refine ⟨fun t => (windowEnergyDenominator K ε t)⁻¹ ^ 2 * U t, ?_, ?_⟩
  · simpa only [inv_one, one_pow, one_mul] using (hd.pow 2).mul hU
  · filter_upwards [hbound] with t ht
    have hn : ‖(↑(windowEnergyDenominator K ε t) : ℂ)⁻¹‖ ^ 2 =
        (windowEnergyDenominator K ε t)⁻¹ ^ 2 := by
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, ← abs_inv, sq_abs]
    simp only [originalWindowMajorant_packet, norm_smul, mul_pow, hn, tsum_mul_left]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ht (sq_nonneg _)

#print axioms originalWindowRadius_div_log
#print axioms originalWindowRadius_inverse_le_buffer
#print axioms originalWindow_enlarged_upper_limit
#print axioms originalWindowMajorant_packet
#print axioms originalWindowMajorant_cuspidal_upper_limit

end QuantitativeNinaMaass
