module

public import QuantitativeMaassCylinderKernelMeanV1
public import QuantitativeMaassCylinderHeightOrthogonalV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem cylinder_height_base_translation (w : ℍ) :
    w=w.re+ᵥcartesianLift (0,w.im) := by
  rw [cartesianLift_positive _ w.im_pos]
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change w.re=w.re+0
    ring
  · exact (vadd_im w.re _).symm

/-- A globally continuous extension of the radial mean as a height test. -/
def cylinderRadialMeanHeight (g : ℝ → ℂ) (z : ℍ) (a y : ℝ) : ℂ :=
  cylinderRadialMean g z (cartesianLift (0,max a y))

theorem cylinderRadialMeanHeight_continuous (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (z : ℍ) (a : ℝ) (ha : 0<a) : Continuous (cylinderRadialMeanHeight g z a) := by
  apply (cylinderRadialMean_continuous g hg R hR hs z).comp
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (cartesianLift_continuousAt _ (ha.trans_le (le_max_left _ _))).comp
    (continuous_const.prodMk (continuous_const.max continuous_id)).continuousAt

theorem cylinderRadialMean_eq_height (g : ℝ → ℂ) (z w : ℍ) (a : ℝ) (ha : a≤w.im) :
    cylinderRadialMean g z w=cylinderRadialMeanHeight g z a w.im := by
  unfold cylinderRadialMeanHeight
  rw [max_eq_right ha]
  conv_lhs => rw [cylinder_height_base_translation w]
  rw [cylinderRadialMean_translation]

/-- On the translation strip, the literal period mean is exactly a
compactly supported height test. The bounds come from geometric propagation. -/
theorem cylinderRadialMean_height_indicator (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) (z : ℍ) :
    cylinderRadialMean g z=ᵐ[quotientMeasure 0]
      (upperRectangle 0 1 (Real.exp (Real.log z.im-R)) (Real.exp (Real.log z.im+R))).indicator
        (fun w => cylinderRadialMeanHeight g z (Real.exp (Real.log z.im-R)) w.im) := by
  rw [translation_quotient_measure]
  filter_upwards [ae_restrict_mem strip_measurable] with w hw
  classical
  by_cases hK : w∈upperRectangle 0 1 (Real.exp (Real.log z.im-R)) (Real.exp (Real.log z.im+R))
  · rw [Set.indicator_of_mem hK]
    exact cylinderRadialMean_eq_height g z w _ hK.2.1
  · rw [Set.indicator_of_notMem hK]
    apply cylinderRadialMean_log_zero g R hR hs z w
    by_contra hh
    have hb := abs_le.mp (le_of_not_gt hh)
    apply hK
    refine ⟨⟨hw.1,hw.2.le⟩,?_,?_⟩
    · rw [←Real.exp_log w.im_pos]
      apply Real.exp_le_exp.mpr
      linarith [hb.1]
    · rw [←Real.exp_log w.im_pos]
      apply Real.exp_le_exp.mpr
      linarith [hb.2]

/-- Any L2 representative of the actual period-mean kernel is orthogonal
to every vector in the closed nonzero-mode cylinder space. -/
theorem cylinderRadialMean_orthogonal (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) (z : ℍ)
    (c v : Lp ℂ 2 (quotientMeasure 0)) (hc : c=ᵐ[quotientMeasure 0] cylinderRadialMean g z)
    (hv : v∈cylinderNonzeroModes) : inner ℂ c v=0 :=
  cylinderNonzeroModes_height_inner_zero _ _ (Real.exp_pos _) _
    (cylinderRadialMeanHeight_continuous g hg R hR hs z _ (Real.exp_pos _)) c v
    (hc.trans (cylinderRadialMean_height_indicator g R hR hs z)) hv

#print axioms cylinder_height_base_translation
#print axioms cylinderRadialMeanHeight_continuous
#print axioms cylinderRadialMean_eq_height
#print axioms cylinderRadialMean_height_indicator
#print axioms cylinderRadialMean_orthogonal

end QuantitativeMaass
