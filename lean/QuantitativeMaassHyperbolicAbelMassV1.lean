module

public import QuantitativeMaassDiskRadialIntegralV1
public import QuantitativeMaassAbelNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Absolute integrability of actual compact radial kernels. -/
theorem hyperbolic_radial_integrable (g : ℝ → ℂ) (hg : Continuous g)
    (w : ℍ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) :
    Integrable (fun z : ℍ => g (Real.cosh (dist z w))) := by
  have he : upperFunction (radialFunction g w)=(fun z : ℍ => g (Real.cosh (dist z w))) :=
    funext (radialFunction_upper g w)
  have hc : HasCompactSupport (fun z : ℍ => g (Real.cosh (dist z w))) := by
    rw [← he]
    exact (isCompact_closedBall w R).of_isClosed_subset isClosed_closure
      (radialFunction_support g w R hR hs)
  exact (hg.comp (Real.continuous_cosh.comp (continuous_id.dist continuous_const))).integrable_of_hasCompactSupport hc

/-- Exact absolute radial mass; no boundedness of the quotient kernel
operator is inferred merely from this scalar equality. -/
theorem integral_hyperbolic_radial_norm (g : ℝ → ℂ) (w : ℍ) :
    (∫ z : ℍ,‖g (Real.cosh (dist z w))‖)=
      (2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖ := by
  have h := integral_hyperbolic_radial (fun q => (‖g q‖:ℂ)) w
  simp only [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The constructed Abel kernel has the correct mass for the shifted wave
packet, with respect to actual hyperbolic volume at every centre. -/
theorem hyperbolic_abel_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (w : ℍ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫ z : ℍ,abelProfile F (Real.cosh (dist z w)))=
      ∫ t,coshTimeTest F t*(Real.cosh (t/2):ℂ) := by
  rw [integral_hyperbolic_radial,abelProfile_time_mass F hF hc R hR hs]

theorem hyperbolic_abel_integrable (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (w : ℍ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Integrable (fun z : ℍ => abelProfile F (Real.cosh (dist z w))) :=
  hyperbolic_radial_integrable _ (abelProfile_smooth F hF hc).continuous w R hR
    (abelProfile_support F _ hs)

#print axioms hyperbolic_radial_integrable
#print axioms integral_hyperbolic_radial_norm
#print axioms hyperbolic_abel_mass
#print axioms hyperbolic_abel_integrable

end QuantitativeMaass
