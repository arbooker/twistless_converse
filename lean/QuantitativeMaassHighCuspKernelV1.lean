module

public import QuantitativeMaassHighCuspCrossV1
public import QuantitativeMaassRadialSeedV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels QuantitativeSpectralObservability
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- Every upper-triangular integral isometry commutes with real horocycle shifts. -/
theorem integral_upper_triangular_vadd (A : SL(2,ℤ)) (hc : A 1 0=0)
    (z : ℍ) (r : ℝ) : A•(r+ᵥz)=r+ᵥ(A•z) := by
  apply UpperHalfPlane.ext
  rw [coe_vadd,coe_specialLinearGroup_apply,coe_specialLinearGroup_apply,coe_vadd]
  rcases integral_upper_triangular_diagonal A hc with ⟨ha,hd⟩ | ⟨ha,hd⟩
  · simp [hc,ha,hd]
    ring
  · simp [hc,ha,hd,div_neg]
    ring

/-- Each compact radial summand is horizontally stationary above its propagation
height. Nonparabolic summands vanish on both sides. -/
theorem integral_high_cusp_profile_translation (A : SL(2,ℤ))
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (z w : ℍ) (hheight : z.im=w.im) (hz : Real.exp (R/2)<z.im) (r : ℝ) :
    g (Real.cosh (dist (A•(r+ᵥz)) (r+ᵥw)))=g (Real.cosh (dist (A•z) w)) := by
  by_cases hc : A 1 0=0
  · rw [integral_upper_triangular_vadd A hc]
    rw [(isometry_real_vadd r).dist_eq]
  · have hzero (z w : ℍ) (hh : z.im=w.im) (hy : Real.exp (R/2)<z.im) :
        g (Real.cosh (dist (A•z) w))=0 := by
      by_contra hn
      have hd : dist (A•z) w≤R := by
        have hb := Real.cosh_le_cosh.mp (hs hn)
        simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] using hb
      exact hc (integral_high_cusp_cross_lowerleft_zero A z w hh R hd hy)
    rw [hzero z w hheight hz,hzero (r+ᵥz) (r+ᵥw) (by simpa using hheight) (by simpa using hz)]

/-- The actual radial Poincare kernel is stationary along a high horocycle
in every integral cusp chart, with its original congruence sum. -/
theorem radialPoincareKernel_high_cusp_translation (N : ℕ) (A : SL(2,ℤ))
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (z w : ℍ) (hheight : z.im=w.im) (hz : Real.exp (R/2)<z.im) (r : ℝ) :
    radialPoincareKernel N g (A•(r+ᵥw)) (A•(r+ᵥz))=
      radialPoincareKernel N g (A•w) (A•z) := by
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  apply tsum_congr
  intro γ
  let B := representative (cuspConjugateFull N A γ)
  have hb (v : ℍ) : B•v=cuspConjugateFull N A γ•v := by
    rw [←integralLabel_action,representative_label]
    rfl
  rw [←cuspConjugateFull_cross_displacement N A γ,
    ←cuspConjugateFull_cross_displacement N A γ,←hb,←hb]
  exact integral_high_cusp_profile_translation B g R hR hs z w hheight hz r

#print axioms integral_upper_triangular_vadd
#print axioms integral_high_cusp_profile_translation
#print axioms radialPoincareKernel_high_cusp_translation

end QuantitativeMaass
