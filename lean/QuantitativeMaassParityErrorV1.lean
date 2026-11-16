module

public import QuantitativeMaassParityLocalTraceV1
public import QuantitativeMaassReflectionLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace SchwartzMap FourierTransform ENNReal

namespace QuantitativeMaass

/-- Joint continuity of the original window-square kernel, obtained from the
actual strongly continuous Hilbert columns. -/
theorem windowTimeSquare_kernel_continuous (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d : ℝ) :
    Continuous (fun p : ℍ×ℍ => radialPoincareKernel N (abelProfile (evenCoshLift
      (timeConvolution (windowTimeSchwartz K hc R hR a d) (windowTimeSchwartz K hc R hR a d)))) p.1 p.2) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  let f := windowTimeSchwartz K hc R hR a d
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R a d hR
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R a d
  have hfr : ∀ t,star (f t)=f t := symmetricWindowTimeTest_real K he R a d
  let c := timeAbelColumn N f hfc hfe (B*R) (mul_nonneg hB.le hR.le) (hs R hR a d)
  have hcont : Continuous c := oneSidedAbelColumn_continuous N _ _ _ _ _
  have hh : (fun p : ℍ×ℍ => radialPoincareKernel N
      (abelProfile (evenCoshLift (timeConvolution f f))) p.1 p.2)=
      (fun p => inner ℂ (c p.2) (c p.1)) := by
    funext p
    exact (timeSquare_kernel_cross N f hfc hfe hfr (B*R) (mul_nonneg hB.le hR.le)
      (hs R hR a d) p.1 p.2).symm
  change Continuous (fun p : ℍ×ℍ => radialPoincareKernel N
    (abelProfile (evenCoshLift (timeConvolution f f))) p.1 p.2)
  rw [hh]
  exact (hcont.comp continuous_snd).inner (hcont.comp continuous_fst)

/-- Both literal geometric errors are continuous and hence integrable on
compact regions of the actual quotient. -/
theorem windowGeometricErrors_continuous (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d : ℝ) :
    Continuous (windowGeometricRemainder N K hc R hR a d) ∧
      Continuous (windowReflection N K hc R hR a d) := by
  have hk := windowTimeSquare_kernel_continuous N K he hc R hR a d
  have hd := hk.comp (continuous_id.prodMk continuous_id)
  have hr := hk.comp (continuous_id.prodMk (continuous_const_smul J))
  have hh : windowGeometricRemainder N K hc R hR a d=(fun x =>
      radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution
        (windowTimeSchwartz K hc R hR a d) (windowTimeSchwartz K hc R hR a d)))) x x-
        windowIdentityContribution K hc R hR a d) := by
    funext x
    rw [windowTimeSquare_kernel_split N K hc R hR a d x]
    ring
  constructor
  · rw [hh]
    exact hd.sub continuous_const
  · exact hr

/-- Quantitative local trace error around one half of the spherical identity.
Both errors are the actual quotient kernel integrals already bounded geometrically. -/
theorem windowParity_integral_error (N : ℕ) [NeZero N]
    (s : Set ℍ) (hs : IsCompact s) (σ : ℝ) (hσ : σ^2=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d : ℝ) :
    |(∫ x in s,windowParityDensity N σ K hc R hR a d x ∂quotientMeasure N)-
      (quotientMeasure N).real s*(windowIdentityContribution K hc R hR a d).re/2| ≤
      ((∫ x in s,‖windowGeometricRemainder N K hc R hR a d x‖ ∂quotientMeasure N)+
        ∫ x in s,‖windowReflection N K hc R hR a d x‖ ∂quotientMeasure N)/2 := by
  have hc' := windowGeometricErrors_continuous N K he hc R hR a d
  let G := windowGeometricRemainder N K hc R hR a d
  let H := windowReflection N K hc R hR a d
  have hG : IntegrableOn G s (quotientMeasure N) := hc'.1.continuousOn.integrableOn_compact hs
  have hH : IntegrableOn H s (quotientMeasure N) := hc'.2.continuousOn.integrableOn_compact hs
  have hσa : |σ|=1 := by
    rcases sq_eq_one_iff.mp hσ with h | h <;> rw [h] <;> norm_num
  let e := fun x => (G x).re+(σ*(H x).re)
  have hei : IntegrableOn e s (quotientMeasure N) := hG.re.add (hH.re.const_mul σ)
  have hid : (∫ x in s,windowParityDensity N σ K hc R hR a d x ∂quotientMeasure N)-
      (quotientMeasure N).real s*(windowIdentityContribution K hc R hR a d).re/2=
      (∫ x in s,e x ∂quotientMeasure N)/2 := by
    have hf : windowParityDensity N σ K hc R hR a d=(fun x =>
        (windowIdentityContribution K hc R hR a d).re/2+e x/2) := by
      funext x
      dsimp [windowParityDensity,e,G,H]
      ring
    rw [hf,integral_add (integrable_const _) (hei.div_const 2)]
    simp_rw [integral_div]
    rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
    ring
  rw [hid,abs_div,show |(2:ℝ)|=2 by norm_num]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    |∫ x in s,e x ∂quotientMeasure N| ≤ ∫ x in s,‖e x‖ ∂quotientMeasure N :=
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := (quotientMeasure N).restrict s) e
    _ ≤ ∫ x in s,(‖G x‖+‖H x‖) ∂quotientMeasure N := by
      apply integral_mono hei.norm (hG.norm.add hH.norm)
      intro x
      change |(G x).re+σ*(H x).re|≤‖G x‖+‖H x‖
      calc
        _ ≤ |(G x).re|+|σ*(H x).re| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul,hσa,one_mul]
          exact add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
    _ = _ := integral_add hG.norm hH.norm

/-- The actual parity trace on the prescribed expanding balls has negligible
geometric error for the literal interval [t,t+epsilon(t)]. Only the original
width and slow-scale product hypotheses are used. -/
theorem windowParity_local_trace_geometric_negligible {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (σ : ℝ) (hσ : σ^2=1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      |(∑' i,∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        ‖(windowWavePacket N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          t (t+ε t) (parityProjection N σ (b i))).val x‖^2 ∂quotientMeasure N)-
        (quotientMeasure N).real (Metric.closedBall o (positiveWindowRadius ε t))*
          (windowIdentityContribution K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
            t (t+ε t)).re/2|/(t*ε t)) atTop (𝓝 0) := by
  have hG := windowGeometricRemainder_interval_negligible N K he hc o ε hε hproduct
  have hH := windowReflection_interval_negligible N K he hc o ε hε hproduct
  have hmajor := (hG.add hH).div_const 2
  simp only [zero_add,zero_div] at hmajor
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
    exact div_nonneg (abs_nonneg _) (mul_pos hp ht.1).le
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
    rw [(windowParity_local_real_trace N b _ (isCompact_closedBall o (positiveWindowRadius ε t))
      σ hσ K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t)).tsum_eq]
    calc
      _ ≤ ((∫ x in Metric.closedBall o (positiveWindowRadius ε t),
          ‖windowGeometricRemainder N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
            t (t+ε t) x‖ ∂quotientMeasure N)+
          ∫ x in Metric.closedBall o (positiveWindowRadius ε t),
          ‖windowReflection N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
            t (t+ε t) x‖ ∂quotientMeasure N)/2/(t*ε t) :=
        div_le_div_of_nonneg_right (windowParity_integral_error N _
          (isCompact_closedBall o (positiveWindowRadius ε t)) σ hσ K he hc
          (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t)) (mul_pos hp ht.1).le
      _ = _ := by ring


#print axioms windowTimeSquare_kernel_continuous
#print axioms windowGeometricErrors_continuous
#print axioms windowParity_integral_error
#print axioms windowParity_local_trace_geometric_negligible

end QuantitativeMaass
