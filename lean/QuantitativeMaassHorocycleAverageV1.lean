module

public import QuantitativeMaassCuspHeightTestV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The compact-region height marginal is finite. -/
theorem heightMeasure_finite (K : Set ℍ) (hK : IsCompact K) :
    IsFiniteMeasure (heightMeasure K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  dsimp only [heightMeasure]
  infer_instance

/-- Continuous height tests determine every L2 vector, by density. -/
theorem heightTest_ext (K : Set ℍ) (hK : IsCompact K)
    (u v : Lp ℂ 2 (heightMeasure K))
    (h : ∀ g : ℝ → ℂ, ∀ hg : Continuous g,
      inner ℂ (heightTestVector K hK g hg) u=inner ℂ (heightTestVector K hK g hg) v) : u=v := by
  let : IsFiniteMeasure (heightMeasure K) := heightMeasure_finite K hK
  have he : (fun g : Lp ℂ 2 (heightMeasure K) => inner ℂ g u)=fun g => inner ℂ g v := by
    apply (BoundedContinuousFunction.toLp_denseRange ℂ (heightMeasure K) ℂ (p := 2)
      (by norm_num)).equalizer (by fun_prop) (by fun_prop)
    funext g
    dsimp only [Function.comp_apply]
    have ht : BoundedContinuousFunction.toLp 2 (heightMeasure K) ℂ g=
        heightTestVector K hK g g.continuous := by
      apply Lp.ext
      exact (BoundedContinuousFunction.coeFn_toLp 2 (heightMeasure K) ℂ g).trans
        (heightTestVector_ae K hK g g.continuous).symm
    rw [ht]
    exact h g g.continuous
  exact ext_inner_left ℂ (fun g => congrFun he g)

/-- Pairing two continuous height tests is integration against the actual
height marginal, with no choice of representatives left in the integrand. -/
theorem heightTest_inner (K : Set ℍ) (hK : IsCompact K)
    (g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h) :
    inner ℂ (heightTestVector K hK g hg) (heightTestVector K hK h hh)=
      ∫ y, star (g y)*h y ∂heightMeasure K := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [heightTestVector_ae K hK g hg,heightTestVector_ae K hK h hh] with y hy hy'
  change inner ℂ (heightTestVector K hK g hg y) (heightTestVector K hK h hh y)=_
  rw [hy,hy']
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

/-- A continuous extension of the normalized horizontal average. The lower
clamp only defines the function away from the rectangle's positive heights. -/
def horocycleAverageExtension (l r a : ℝ) (F : ℍ → ℂ) (y : ℝ) : ℂ :=
  ((r-l : ℝ):ℂ)⁻¹ * ∫ x in Icc l r, F (cartesianLift (x,max a y))

theorem horocycleAverageExtension_continuous (l r a : ℝ) (ha : 0<a)
    (F : ℍ → ℂ) (hF : Continuous F) : Continuous (horocycleAverageExtension l r a F) := by
  have hc : Continuous (fun W : ℝ × ℝ => cartesianLift (W.2,max a W.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro W
    exact (cartesianLift_continuousAt _ (ha.trans_le (le_max_left _ _))).comp
      (continuous_snd.prodMk (continuous_const.max continuous_fst)).continuousAt
  exact (continuous_parametric_integral_of_continuous
    (f := fun y x : ℝ => F (cartesianLift (x,max a y)))
    (hF.comp hc) isCompact_Icc).const_mul _

/-- The constructed bounded fiber average is exactly the normalized
horocycle integral, as an L2 vector, for continuous local representatives. -/
theorem localHeightAverage_eq_horocycle (l r a b : ℝ) (hlr : l<r) (ha : 0<a)
    (F : ℍ → ℂ) (hF : Continuous F)
    (f : Lp ℂ 2 (volume.restrict (upperRectangle l r a b)))
    (hf : (f : ℍ → ℂ)=ᵐ[volume.restrict (upperRectangle l r a b)] F) :
    localHeightAverage (upperRectangle l r a b) f=
      heightTestVector _ (upperRectangle_compact l r a b ha)
        (horocycleAverageExtension l r a F) (horocycleAverageExtension_continuous l r a ha F hF) := by
  apply heightTest_ext _ (upperRectangle_compact l r a b ha)
  intro g hg
  rw [localHeightAverage_rectangle_test l r a b ha F hF f hf g hg,heightTest_inner]
  rw [heightMeasure_rectangle_integral l r a b ha
    (fun y => star (g y)*horocycleAverageExtension l r a F y)
    (hg.star.mul (horocycleAverageExtension_continuous l r a ha F hF))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hwidth : (volume (Icc l r)).toReal=r-l := by
    rw [Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hlr.le)]
  have hn : ((r-l:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hlr.ne')
  rw [hwidth,horocycleAverageExtension,max_eq_right hy.1]
  change _=((r-l:ℝ):ℂ)*(star (g y)*
    (((r-l:ℝ):ℂ)⁻¹ * ∫ x in Icc l r, F (cartesianLift (x,y)))/(y:ℂ)^2)
  field_simp

/-- Literal almost-everywhere horizontal integration formula. -/
theorem localHeightAverage_horocycle_ae (l r a b : ℝ) (hlr : l<r) (ha : 0<a)
    (F : ℍ → ℂ) (hF : Continuous F)
    (f : Lp ℂ 2 (volume.restrict (upperRectangle l r a b)))
    (hf : (f : ℍ → ℂ)=ᵐ[volume.restrict (upperRectangle l r a b)] F) :
    (localHeightAverage (upperRectangle l r a b) f : ℝ → ℂ)=ᵐ[heightMeasure (upperRectangle l r a b)]
      horocycleAverageExtension l r a F := by
  rw [localHeightAverage_eq_horocycle l r a b hlr ha F hF f hf]
  exact heightTestVector_ae _ _ _ _

#print axioms heightTest_ext
#print axioms localHeightAverage_eq_horocycle
#print axioms localHeightAverage_horocycle_ae

end QuantitativeMaass
