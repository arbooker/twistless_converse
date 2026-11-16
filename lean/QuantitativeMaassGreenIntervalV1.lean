module

public import QuantitativeMaassCuspGeneratorV1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval Topology

namespace QuantitativeMaass

/-- Complex Green identity with its actual endpoint boundary form. -/
theorem green_interval (f f₁ g₁ g₂ : ℝ → ℂ) (a b : ℝ)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f₁ x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g₁ (g₂ x) x)
    (hf₁ : ContinuousOn f₁ (uIcc a b)) (hg₂ : ContinuousOn g₂ (uIcc a b)) :
    (∫ x in a..b, star (f x)*(-g₂ x))=
      (∫ x in a..b, star (f₁ x)*g₁ x)-
        (star (f b)*g₁ b-star (f a)*g₁ a) := by
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => (hf x hx).star) hg
    (hf₁.star.intervalIntegrable) hg₂.intervalIntegrable
  simp_rw [mul_neg]
  rw [intervalIntegral.integral_neg,hi]
  ring

/-- A continuous compact-rectangle Fubini theorem; the integrability needed
for the Green identity is derived, not left as an interchange assumption. -/
theorem rectangle_integral_swap (F : ℝ → ℝ → ℂ) (a b c d : ℝ)
    (hab : a≤b) (hcd : c≤d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, F x y)=∫ y in c..d, ∫ x in a..b, F x y := by
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simpa only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hcd]
    using integral_integral_swap hi

#print axioms green_interval
#print axioms rectangle_integral_swap

end QuantitativeMaass
