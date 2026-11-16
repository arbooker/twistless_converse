module

public import QuantitativeMaassCylinderAbelColumnV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Strong continuity of literal Abel rows on the infinite-volume cylinder.
The dominating function is compactly supported on the translation strip. -/
theorem cylinderAbelKernel_row_L2_continuous (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    Tendsto (fun u => ∫ y,‖radialPoincareKernel 0 (abelProfile F) u y-
      radialPoincareKernel 0 (abelProfile F) x y‖^2 ∂quotientMeasure 0) (𝓝 x) (𝓝 0) := by
  let K := upperRectangle 0 1 (Real.exp (Real.log x.im-(R+1))) (Real.exp (Real.log x.im+(R+1)))
  have hK : IsCompact K := upperRectangle_compact _ _ _ _ (Real.exp_pos _)
  let k := radialPoincareKernel 0 (abelProfile F)
  have hc : Continuous (fun p : ℍ×ℍ => k p.1 p.2) :=
    oneSidedAbelKernel_joint_continuous 0 F hF R hR hs
  have hm (u : ℍ) : AEStronglyMeasurable (k u) (quotientMeasure 0) :=
    (Continuous.uncurry_left u hc).aestronglyMeasurable
  obtain ⟨D,_,hD⟩ := oneSidedAbelKernel_local_bound 0 F hF R hR hs x 1
  let bound : ℍ → ℝ := K.indicator (fun _ => (2*D)^2)
  have hi0 : Integrable bound volume :=
    (integrable_indicator_iff hK.measurableSet).mpr (integrableOn_const hK.measure_ne_top)
  have hi : Integrable bound (quotientMeasure 0) := by
    rw [translation_quotient_measure]
    exact hi0.integrableOn
  have hstrip : ∀ᵐ y ∂quotientMeasure 0,y∈strip := by
    rw [translation_quotient_measure]
    exact ae_restrict_mem strip_measurable
  have hzero (u : ℍ) (hu : dist u x≤1) (y : ℍ) (hy : y∈strip) (hk : y∉K) : k u y=0 := by
    by_contra hn
    exact hk (cylinderRadialKernel_strip_support _ R hR (abelProfile_support F _ hs) x u 1 hu y hy hn)
  have hb : ∀ᶠ u in 𝓝 x,∀ᵐ y ∂quotientMeasure 0,‖‖k u y-k x y‖^2‖≤bound y := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with u hu
    change dist u x<1 at hu
    filter_upwards [hstrip] with y hy
    by_cases hk : y∈K
    · rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),show bound y=K.indicator _ y from rfl,Set.indicator_of_mem hk]
      apply pow_le_pow_left₀ (norm_nonneg _)
      have hh := (norm_sub_le (k u y) (k x y)).trans
        (add_le_add (hD u hu.le y) (hD x (by simp) y))
      linarith
    · simp only [bound,Set.indicator_of_notMem hk,hzero u hu.le y hy hk,
        hzero x (by simp) y hy hk,sub_self,norm_zero,zero_pow (by decide : 2≠0),le_refl]
  have hl : ∀ᵐ y ∂quotientMeasure 0,Tendsto (fun u => ‖k u y-k x y‖^2) (𝓝 x) (𝓝 (0:ℝ)) := by
    filter_upwards with y
    have hh : Continuous (fun u => k u y) := Continuous.uncurry_right y hc
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
      ((hh.continuousAt (x:=x)).tendsto.sub_const (k x y)).norm.pow 2
  have ht := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall (fun u => ((hm u).sub (hm x)).norm.pow 2)) hb hi hl
  simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero,k] using ht

theorem cylinderAbelColumn_sub_energy (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x u : ℍ) :
    ‖cylinderAbelColumn F hF R hR hs u-cylinderAbelColumn F hF R hR hs x‖^2=
      ∫ y,‖radialPoincareKernel 0 (abelProfile F) u y-
        radialPoincareKernel 0 (abelProfile F) x y‖^2 ∂quotientMeasure 0 := by
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (cylinderAbelColumn F hF R hR hs u)
    (cylinderAbelColumn F hF R hR hs x),cylinderAbelColumn_coeFn F hF R hR hs u,
    cylinderAbelColumn_coeFn F hF R hR hs x] with y hy hu hx
  rw [hy,Pi.sub_apply,hu,hx]

theorem cylinderAbelColumn_continuous (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    Continuous (cylinderAbelColumn F hF R hR hs) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := cylinderAbelKernel_row_L2_continuous F hF R hR hs x
  simp_rw [←cylinderAbelColumn_sub_energy F hF R hR hs x] at ht
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

/-- Exact literal kernel pairing, valid for every cylinder L2 input. -/
theorem cylinderAbelColumn_inner (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (x : ℍ) (f : Lp ℂ 2 (quotientMeasure 0)) :
    inner ℂ (cylinderAbelColumn F hF R hR hs x) f=
      ∫ y,radialPoincareKernel 0 (abelProfile F) x y*f y ∂quotientMeasure 0 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cylinderAbelColumn_coeFn F hF R hR hs x] with y hy
  rw [hy,RCLike.inner_apply]
  change f y*star (radialPoincareKernel 0 (abelProfile F) x y)=_
  rw [radialPoincareKernel_star 0 _ (abelProfile_real F hr),mul_comm]

#print axioms cylinderAbelKernel_row_L2_continuous
#print axioms cylinderAbelColumn_sub_energy
#print axioms cylinderAbelColumn_continuous
#print axioms cylinderAbelColumn_inner

end QuantitativeMaass
