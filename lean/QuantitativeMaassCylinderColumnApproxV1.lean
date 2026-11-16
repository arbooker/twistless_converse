module

public import QuantitativeMaassCylinderColumnContinuityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Smooth radial shifts converge strongly as literal cylinder columns.
The domination uses finite strip rectangles, not finite quotient volume. -/
theorem cylinderAbelColumn_shift_tendsto {ι : Type*} (L : Filter ι) [L.IsCountablyGenerated]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a L (𝓝 0)) (x : ℍ) :
    Tendsto (fun i => cylinderAbelColumn (radialShiftApprox F (a i))
      (radialShiftApprox_smooth F hF _ (ha i)).contDiffOn R hR
      (radialShiftApprox_upper_support F _ (fun _ hq => not_not.mp (fun hn => (not_le_of_gt hq) (hs hn)))
        _ (ha i)) x) L (𝓝 (cylinderAbelColumn F hF R hR hs x)) := by
  have hz : ∀ q,Real.cosh R<q → F q=0 := fun q hq => by
    by_contra hn
    exact (not_le_of_gt hq) (hs hn)
  let K := upperRectangle 0 1 (Real.exp (Real.log x.im-(R+0))) (Real.exp (Real.log x.im+(R+0)))
  have hK : IsCompact K := upperRectangle_compact _ _ _ _ (Real.exp_pos _)
  let k (i : ι) := radialPoincareKernel 0 (abelProfile (radialShiftApprox F (a i))) x
  let g := radialPoincareKernel 0 (abelProfile F) x
  have hg : Continuous g := Continuous.uncurry_left (f:=radialPoincareKernel 0 (abelProfile F)) x (oneSidedAbelKernel_joint_continuous 0 F hF R hR hs)
  have hk (i : ι) : Continuous (k i) := Continuous.uncurry_left
    (f:=radialPoincareKernel 0 (abelProfile (radialShiftApprox F (a i)))) x
    (oneSidedAbelKernel_joint_continuous 0 _ (radialShiftApprox_smooth F hF _ (ha i)).contDiffOn
      R hR (radialShiftApprox_upper_support F _ hz _ (ha i)))
  obtain ⟨D,hD,hbound⟩ := radialShiftAbelKernel_local_bound 0 F hF R hR hs x 0
  obtain ⟨E,hE,hboundE⟩ := oneSidedAbelKernel_local_bound 0 F hF R hR hs x 0
  let bound : ℍ → ℝ := K.indicator (fun _ => (D+E)^2)
  have hi0 : Integrable bound volume :=
    (integrable_indicator_iff hK.measurableSet).mpr (integrableOn_const hK.measure_ne_top)
  have hi : Integrable bound (quotientMeasure 0) := by
    rw [translation_quotient_measure]
    exact hi0.integrableOn
  have hstrip : ∀ᵐ y ∂quotientMeasure 0,y∈strip := by
    rw [translation_quotient_measure]
    exact ae_restrict_mem strip_measurable
  have hzero (G : ℝ → ℂ) (hG : Function.support G⊆Iic (Real.cosh R))
      (y : ℍ) (hy : y∈strip) (hyK : y∉K) : radialPoincareKernel 0 G x y=0 := by
    by_contra hn
    exact hyK (cylinderRadialKernel_strip_support G R hR hG x x 0 (by simp) y hy hn)
  have hb : ∀ᶠ i in L,∀ᵐ y ∂quotientMeasure 0,‖‖k i y-g y‖^2‖≤bound y := by
    filter_upwards [(tendsto_order.1 ha0).2 1 (by norm_num)] with i hai
    filter_upwards [hstrip] with y hy
    by_cases hyK : y∈K
    · rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),show bound y=K.indicator _ y from rfl,Set.indicator_of_mem hyK]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (add_le_add
        (hbound _ (ha i) hai.le x (by simp) y) (hboundE x (by simp) y))
    · have hk0 : k i y=0 := hzero _ (abelProfile_support _ _
        (radialShiftApprox_upper_support F _ hz _ (ha i))) y hy hyK
      have hg0 : g y=0 := hzero _ (abelProfile_support F _ hs) y hy hyK
      simp only [bound,Set.indicator_of_notMem hyK,hk0,hg0,sub_self,norm_zero,
        zero_pow (by decide : 2≠0),le_refl]
  have hpoint : ∀ᵐ y ∂quotientMeasure 0,Tendsto (fun i => ‖k i y-g y‖^2) L (𝓝 (0:ℝ)) := by
    filter_upwards with y
    have hh := ((radialShiftAbelKernel_tendsto L 0 F hF R hR hs a ha ha0 x y).sub_const (g y)).norm.pow 2
    simpa only [k,g,sub_self,norm_zero,zero_pow (by decide : 2≠0)] using hh
  have henergy := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall (fun i => ((hk i).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2))
    hb hi hpoint
  simp only [integral_zero] at henergy
  have hnorm (i : ι) :
      ‖cylinderAbelColumn (radialShiftApprox F (a i))
        (radialShiftApprox_smooth F hF _ (ha i)).contDiffOn R hR
        (radialShiftApprox_upper_support F _ hz _ (ha i)) x-cylinderAbelColumn F hF R hR hs x‖^2=
        ∫ y,‖k i y-g y‖^2 ∂quotientMeasure 0 := by
    rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
      (cylinderAbelColumn (radialShiftApprox F (a i))
        (radialShiftApprox_smooth F hF _ (ha i)).contDiffOn R hR
        (radialShiftApprox_upper_support F _ hz _ (ha i)) x)
      (cylinderAbelColumn F hF R hR hs x),
      cylinderAbelColumn_coeFn (radialShiftApprox F (a i))
        (radialShiftApprox_smooth F hF _ (ha i)).contDiffOn R hR
        (radialShiftApprox_upper_support F _ hz _ (ha i)) x,
      cylinderAbelColumn_coeFn F hF R hR hs x] with y hy h1 h2
    rw [hy,Pi.sub_apply,h1,h2]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun i => ∫ y,‖k i y-g y‖^2 ∂quotientMeasure 0) L (𝓝 (0:ℝ)) at henergy
  simp_rw [←hnorm] at henergy
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp henergy
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using! hh

#print axioms cylinderAbelColumn_shift_tendsto

end QuantitativeMaass
