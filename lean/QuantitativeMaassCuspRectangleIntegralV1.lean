module

public import QuantitativeMaassCuspRectangleV1
public import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

/-- Fubini in a genuine compact hyperbolic rectangle. -/
theorem integral_upperRectangle_iterated (l r a b : ℝ) (ha : 0<a)
    (F : ℍ → ℂ) (hF : Continuous F) :
    (∫ Z in upperRectangle l r a b, F Z)=
      ∫ y in Icc a b, ∫ x in Icc l r, F (cartesianLift (x,y))/(y:ℂ)^2 := by
  rw [integral_upperRectangle l r a b ha]
  have hc : ContinuousOn cartesianLift (Icc l r ×ˢ Icc a b) := by
    intro Z hZ
    exact (cartesianLift_continuousAt Z (ha.trans_le hZ.2.1)).continuousWithinAt
  have hcont : ContinuousOn (fun Z : ℝ × ℝ => F (cartesianLift Z)/(Z.2:ℂ)^2)
      (Icc l r ×ˢ Icc a b) :=
    (hF.comp_continuousOn hc).div
      (((Complex.continuous_ofReal.comp continuous_snd).pow 2).continuousOn)
      (fun Z hZ => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt (ha.trans_le hZ.2.1))))
  have hi : IntegrableOn (fun Z : ℝ × ℝ => F (cartesianLift Z)/(Z.2:ℂ)^2)
      (Icc l r ×ˢ Icc a b) volume :=
    hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  change Integrable _ (((volume : Measure ℝ).prod volume).restrict (Icc l r ×ˢ Icc a b)) at hi
  rw [← Measure.prod_restrict] at hi
  change (∫ Z, F (cartesianLift Z)/(Z.2:ℂ)^2
    ∂((volume : Measure ℝ).prod volume).restrict (Icc l r ×ˢ Icc a b))=_
  rw [← Measure.prod_restrict,integral_prod_symm _ hi]

/-- Explicit height marginal on a hyperbolic rectangle, tested against any
continuous function. Its density is horizontal length times dy/y². -/
theorem heightMeasure_rectangle_integral (l r a b : ℝ) (ha : 0<a)
    (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ y, g y ∂heightMeasure (upperRectangle l r a b))=
      ∫ y in Icc a b, (volume (Icc l r)).toReal • (g y/(y:ℂ)^2) := by
  rw [heightMeasure,integral_map continuous_im.measurable.aemeasurable hg.aestronglyMeasurable]
  change (∫ Z in upperRectangle l r a b, (g ∘ UpperHalfPlane.im) Z)=_
  rw [integral_upperRectangle_iterated l r a b ha _ (hg.comp continuous_im)]
  dsimp only [Function.comp_apply]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hp : 0<y := ha.trans_le hy.1
  have he : (fun x : ℝ => g (cartesianLift (x,y)).im/(y:ℂ)^2)=fun _ => g y/(y:ℂ)^2 := by
    funext x
    rw [cartesianLift_positive _ hp]
    rfl
  rw [he,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ]

#print axioms integral_upperRectangle_iterated
#print axioms heightMeasure_rectangle_integral

end QuantitativeMaass
