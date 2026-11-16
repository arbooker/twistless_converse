module

public import QuantitativeMaassCylinderWindowBranchV1
public import QuantitativeMaassCorrespondenceHeightV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- The actual cylinder branch error has constants independent of its
integral matrix. Matrix growth is displayed explicitly in the exponent;
no fixed-matrix limit is substituted for the growing-filter estimate. -/
theorem cylinder_window_branch_uniform_exp (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t →
      ∀ (a : ℍ→ℂ) (A : ℝ),0≤A →
      AEStronglyMeasurable a (volume.restrict (Metric.closedBall o L)) →
      (∀ᵐ x ∂volume.restrict (Metric.closedBall o L),‖a x‖≤A) →
      |(∫ x in Metric.closedBall o L,(a x*radialPoincareKernel 0
          (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t)
          x (positiveIntegralGL M hM • x)).re)-
        (∫ x in Metric.closedBall o L,(a x*(if integralIdentityCoset 0 M then
          windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) else 0)).re)|≤
        A*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L+
          10*dist (positiveIntegralGL M hM • o) o+20*Real.log (2*integralMatrixHeight M)) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := cylinder_window_branch_error K he hc
  obtain ⟨G,hG,hgeom⟩ := correspondence_geometry_uniform_exp o
  refine ⟨20*U+2,C*G,by positivity,mul_pos hC hG,?_⟩
  intro M hM L R ε t hR hL hε hε1 ht a A hA ha haB
  have hRp : 0≤R := by linarith
  have hB : 0≤2*Real.log (2*integralMatrixHeight M) := by
    have hh := (integralMatrixHeight_bounds M).1
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hg := hgeom L (2*(U*R)+2*L) (dist (positiveIntegralGL M hM • o) o)
    (2*Real.log (2*integralMatrixHeight M)) hL (by positivity) dist_nonneg hB
  apply (hbound M hM o L R ε t hR hε hε1 ht a A hA ha haB).trans
  calc
    _ = (A*C*Real.sqrt t*R^2*ε^2)*
        ((energyMultiplicity o 0 (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o):ℝ)*
          (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L
            (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M))))) := by ring
    _ ≤ (A*C*Real.sqrt t*R^2*ε^2)*(G*Real.exp
        (10*((2*(U*R)+2*L)+L+dist (positiveIntegralGL M hM • o) o+
          2*Real.log (2*integralMatrixHeight M)))) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (A*(C*G)*Real.sqrt t*ε^2)*(R^2*Real.exp ((20*U)*R))*
        Real.exp (30*L+10*dist (positiveIntegralGL M hM • o) o+
          20*Real.log (2*integralMatrixHeight M)) := by
      rw [show Real.exp (10*((2*(U*R)+2*L)+L+dist (positiveIntegralGL M hM • o) o+
          2*Real.log (2*integralMatrixHeight M)))=
        Real.exp ((20*U)*R)*Real.exp (30*L+10*dist (positiveIntegralGL M hM • o) o+
          20*Real.log (2*integralMatrixHeight M)) by rw [←Real.exp_add]; congr 1; ring]
      ring
    _ ≤ (A*(C*G)*Real.sqrt t*ε^2)*Real.exp ((20*U+2)*R)*
        Real.exp (30*L+10*dist (positiveIntegralGL M hM • o) o+
          20*Real.log (2*integralMatrixHeight M)) := by
      gcongr
      exact radius_square_exp_le (20*U) R hRp
    _ = _ := by
      rw [show Real.exp ((20*U+2)*R+30*L+10*dist (positiveIntegralGL M hM • o) o+
          20*Real.log (2*integralMatrixHeight M))=
        Real.exp ((20*U+2)*R)*Real.exp (30*L+10*dist (positiveIntegralGL M hM • o) o+
          20*Real.log (2*integralMatrixHeight M)) by rw [←Real.exp_add]; congr 1; ring]
      ring

#print axioms cylinder_window_branch_uniform_exp
end QuantitativeMaass
