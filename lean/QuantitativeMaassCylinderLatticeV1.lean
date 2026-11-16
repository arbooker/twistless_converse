module

public import QuantitativeMaassCylinderStationaryV1
public import QuantitativeMaassParabolicVariationScaleV1
public import QuantitativeMaassCuspCenteredVariationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open AsymptoticIntegralSubgroup
open scoped Topology ContDiff

namespace QuantitativeMaass

def integerCylinderTranslation (n : ℤ) : gamma 0 :=
  ⟨translationLabel (n:ℚ),translation_mem 0 n⟩

theorem integerCylinderTranslation_bijective : Function.Bijective integerCylinderTranslation := by
  constructor
  · intro n m h
    have he := congrArg (fun γ : gamma 0 => (γ.val • UpperHalfPlane.I).re) h
    change (translationLabel (n:ℚ) • UpperHalfPlane.I).re=
      (translationLabel (m:ℚ) • UpperHalfPlane.I).re at he
    simp only [cylinder_translationLabel_vadd,vadd_re] at he
    exact_mod_cast (add_right_cancel he)
  · intro γ
    obtain ⟨n,hn⟩ := gamma_zero_translation γ
    exact ⟨n,Subtype.ext hn.symm⟩

/-- Exact integer periodization of the literal cylinder kernel at equal
heights. Unlike the congruence quotient formula, this needs no high-cusp cutoff. -/
theorem cylinderRadialKernel_line_sum (g : ℝ → ℂ) (z w : ℍ) (hh : z.im=w.im) :
    radialPoincareKernel 0 g w z=
      ∑' n : ℤ,parabolicLineProfile g z.im ((n:ℝ)+z.re-w.re) := by
  let e := Equiv.ofBijective integerCylinderTranslation integerCylinderTranslation_bijective
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  rw [←e.tsum_eq]
  apply tsum_congr
  intro n
  change g (Real.cosh (dist (translationLabel (n:ℚ) • z) w))=_
  rw [cylinder_translationLabel_vadd,equal_height_translated_cosh z w hh]
  rfl

/-- Uniform lattice discrepancy for the exact cylinder kernel. The bound
is independent of its height and horizontal centers. -/
theorem cylinderRadialKernel_line_discrepancy (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (B : ℝ) (hs : Function.support g⊆Iic B)
    (z w : ℍ) (hh : z.im=w.im) :
    ‖radialPoincareKernel 0 g w z-∫ v,parabolicLineProfile g z.im v‖≤
      ∫ v,‖deriv (parabolicLineProfile g 1) v‖ := by
  rw [cylinderRadialKernel_line_sum g z w hh]
  have h := (parabolicLineProfile_lattice_discrepancy g hg B hs z.im z.im_pos (z.re-w.re)).2
  rw [parabolicLineProfile_variation_scale g hg z.im z.im_pos] at h
  convert h using 1
  congr 2
  apply tsum_congr
  intro n
  congr 1
  ring

/-- The diagonal-minus-horizontal-mean kernel is uniformly bounded by
height-one variation. Its high-cusp hyperbolic integral therefore converges. -/
theorem cylinderRadialKernel_centered_bound (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) (z : ℍ) :
    ‖radialPoincareKernel 0 g z z-
      ∫ y in Icc (0:ℝ) 1,radialPoincareKernel 0 g (y+ᵥz) z‖≤
        2*∫ v,‖deriv (parabolicLineProfile g 1) v‖ := by
  let F := fun y : ℝ => radialPoincareKernel 0 g (y+ᵥz) z
  have ht : Continuous (fun y : ℝ => (y+ᵥz,z)) :=
    (cylinder_vadd_continuous z).prodMk continuous_const
  have hF := (radialPoincareKernel_joint_continuous_physical 0 g hg.continuousOn R hR hs).comp ht
  change Continuous F at hF
  have hb (y : ℝ) : ‖F y-∫ v,parabolicLineProfile g z.im v‖≤
      ∫ v,‖deriv (parabolicLineProfile g 1) v‖ :=
    cylinderRadialKernel_line_discrepancy g hg (Real.cosh R) hs z (y+ᵥz) (vadd_im y z).symm
  simpa only [F,zero_vadd] using unit_average_centering_bound F hF
    (∫ v,parabolicLineProfile g z.im v) _ 0 (hb 0) (fun y _ => hb y)

#print axioms integerCylinderTranslation_bijective
#print axioms cylinderRadialKernel_line_sum
#print axioms cylinderRadialKernel_line_discrepancy
#print axioms cylinderRadialKernel_centered_bound

end QuantitativeMaass
