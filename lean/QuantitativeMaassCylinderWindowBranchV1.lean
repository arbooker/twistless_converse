module

public import QuantitativeMaassCylinderCorrespondenceErrorV1
public import QuantitativeMaassCorrespondenceWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- Quantitative compact-branch comparison for the actual squared window
on the translation cylinder. The exact main term is the arithmetic
identity-coset indicator; all matrix and geometric costs are explicit. -/
theorem cylinder_window_branch_error (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (o : ℍ) (L R ε t : ℝ) (hR : 1≤R),0≤ε → ε≤1 → 1≤t →
      ∀ (a : ℍ→ℂ) (A : ℝ),0≤A →
      AEStronglyMeasurable a (volume.restrict (Metric.closedBall o L)) →
      (∀ᵐ x ∂volume.restrict (Metric.closedBall o L),‖a x‖≤A) →
      |(∫ x in Metric.closedBall o L,(a x*radialPoincareKernel 0
          (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t)
          x (positiveIntegralGL M hM • x)).re)-
        (∫ x in Metric.closedBall o L,(a x*(if integralIdentityCoset 0 M then
          windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) else 0)).re)|≤
        A*((energyMultiplicity o 0 (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o):ℝ)*
          (C*Real.sqrt t*R^2*ε^2)*
          (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L
            (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M))))) := by
  obtain ⟨U,hU,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  refine ⟨U,C,hU,hC,?_⟩
  intro M hM o L R ε t hR hε hε1 ht a A hA ha haB
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hheight := integralMatrixHeight_bounds M
  have hB : 0 < integralMatrixHeight M := lt_of_lt_of_le zero_lt_one hheight.1
  let f := windowTimeSchwartz K hc R hRp (t-ε) (t+ε)
  have hfs : Function.support (f : ℝ→ℂ)⊆Icc (-(U*R)) (U*R) := hs R hRp (t-ε) (t+ε)
  have hgs : Function.support (timeConvolution f f : ℝ→ℂ)⊆Icc (-(2*(U*R))) (2*(U*R)) := by
    simpa only [two_mul] using timeConvolution_support f f (U*R) (U*R) hfs hfs
  have hps : Function.support (windowSquareProfile K hc R hRp ε t)⊆Iic (Real.cosh (2*(U*R))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)
  exact cylinder_weighted_correspondence_error M hM (integralMatrixHeight M) hB hheight.2
    o L (2*(U*R)) (by positivity) (windowSquareProfile K hc R hRp ε t)
    (windowSquareProfile_continuous K he hc R hRp ε t) hps
    (C*Real.sqrt t*R^2*ε^2) (by positivity)
    (fun d hd => hbound R ε t d hR hε hε1 ht hd) a ha A hA haB

#print axioms cylinder_window_branch_error

end QuantitativeMaass
