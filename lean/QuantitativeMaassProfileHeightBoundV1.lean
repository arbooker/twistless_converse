module

public import QuantitativeMaassCorrespondenceHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip QuantitativeArithmeticMaassOverlap
open scoped Topology

namespace QuantitativeMaass

/-- The correspondence geometry applies to any actual radial profile
with compact propagation and inverse-square-root displacement decay.
All dependence on the profile is confined to its explicit amplitude. -/
theorem radialIntegralRemainder_uniform_height_bound (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) [NeZero N]
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (S R : ℝ),0≤S → 0≤R → ∀ (g : ℝ → ℂ),ContinuousOn g (Ici 1) →
      Function.support g ⊆ Iic (Real.cosh R) → ∀ A : ℝ,0≤A →
      (∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤A/Real.sqrt (Real.sinh d)) →
      IntegrableOn (radialIntegralRemainder N M hM g) (Metric.closedBall o S) ∧
      (∫ z in Metric.closedBall o S,‖radialIntegralRemainder N M hM g z‖)≤
        C*(integralMatrixHeight M)^40*A*Real.exp (10*R+30*S) := by
  obtain ⟨G,hG,hgeom⟩ := correspondence_geometry_uniform_exp o
  obtain ⟨J,hJ,hheight⟩ := correspondence_height_cost o
  refine ⟨G*J,mul_pos hG hJ,?_⟩
  intro N _ M hM S R hS hR g hg hs A hA hbound
  have hB := integralMatrixHeight_bounds M
  have hBp : 0 < integralMatrixHeight M := lt_of_lt_of_le zero_lt_one hB.1
  have hlog : 0≤2*Real.log (2*integralMatrixHeight M) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hB.1]))
  obtain ⟨hi,hb⟩ := radialIntegralRemainder_integral_bound N M hM
    (integralMatrixHeight M) hBp hB.2 o S R hR g hg hs A hA hbound
  refine ⟨hi,hb.trans ?_⟩
  have hge := hgeom S (R+2*S) (dist (positiveIntegralGL M hM • o) o)
    (2*Real.log (2*integralMatrixHeight M)) hS (by positivity) dist_nonneg hlog
  have hj := hheight M hM _ hB.1 hB.2
  have he : Real.exp (10*((R+2*S)+S+dist (positiveIntegralGL M hM • o) o+
      2*Real.log (2*integralMatrixHeight M)))=
      Real.exp (10*R+30*S)*
        Real.exp (10*(dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hge
  have hge' := hge.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le) hG.le)
  calc
    _ = A*((energyMultiplicity o 0 (R+2*S+dist (positiveIntegralGL M hM • o) o):ℝ)*
        (Real.pi*(volume.real (Metric.closedBall o S)+hyperbolicSublevelConstant o S
          (R+2*S+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M))))) := by ring
    _ ≤ A*(G*(Real.exp (10*R+30*S)*(J*(integralMatrixHeight M)^40))) :=
      mul_le_mul_of_nonneg_left hge' hA
    _ = _ := by ring

#print axioms radialIntegralRemainder_uniform_height_bound

end QuantitativeMaass
