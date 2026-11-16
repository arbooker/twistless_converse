module

public import QuantitativeMaassReflectedCorrespondenceIntegralV1
public import QuantitativeMaassCylinderWindowBranchV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Reflected cylinder branches contribute only the explicit geometric error,
including in the presence of bounded measurable coefficients. -/
theorem cylinder_weighted_reflected_correspondence_bound
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (B : ℝ) (hB : 0<B) (hentry : ∀ i j,|(M i j:ℝ)|≤B)
    (o : ℍ) (L R : ℝ) (hR : 0≤R) (g : ℝ→ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d))
    (a : ℍ→ℂ)
    (A : ℝ) (hA : 0≤A) (haB : ∀ᵐ x ∂volume.restrict (Metric.closedBall o L),‖a x‖≤A) :
    |(∫ x in Metric.closedBall o L,(a x*radialPoincareKernel 0 g x (positiveIntegralGL M hM • (J•x))).re)|≤
      A*((QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0
        (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o):ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+
          reflectedSublevelConstant o L (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o+2*Real.log (2*B))))) := by
  let S := Metric.closedBall o L
  let E := fun x => radialPoincareKernel 0 g x (positiveIntegralGL M hM • (J•x))
  obtain ⟨hi,hbound⟩ := radialReflectedIntegralKernel_integral_bound 0 M hM B hB hentry o L R hR g hg hs C hC hb
  rw [←Real.norm_eq_abs]
  calc
    _≤∫ x in S,A*‖E x‖ := by
      apply norm_integral_le_of_norm_le (hi.norm.const_mul A)
      filter_upwards [haB] with x hx
      calc
        _≤‖a x*E x‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (a x*E x)
        _=‖a x‖*‖E x‖ := norm_mul _ _
        _≤_ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _=A*(∫ x in S,‖E x‖) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left hbound hA

/-- Quantitative reflected-branch bound for the actual squared cylinder
window, with constants uniform in the window and explicit geometric costs. -/
theorem cylinder_window_reflected_branch_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (o : ℍ) (L R ε t : ℝ) (hR : 1≤R),0≤ε → ε≤1 → 1≤t →
      ∀ (a : ℍ→ℂ) (A : ℝ),0≤A →
      (∀ᵐ x ∂volume.restrict (Metric.closedBall o L),‖a x‖≤A) →
      |(∫ x in Metric.closedBall o L,(a x*radialPoincareKernel 0
          (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t)
          x (positiveIntegralGL M hM • (J•x))).re)|≤
        A*((energyMultiplicity o 0 (2*(U*R)+2*L+dist (positiveIntegralGL M hM • (J•o)) o):ℝ)*
          (C*Real.sqrt t*R^2*ε^2)*
          (Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L
            (2*(U*R)+2*L+dist (positiveIntegralGL M hM • (J•o)) o+2*Real.log (2*integralMatrixHeight M))))) := by
  obtain ⟨U,hU,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  refine ⟨U,C,hU,hC,?_⟩
  intro M hM o L R ε t hR hε hε1 ht a A hA haB
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hheight := integralMatrixHeight_bounds M
  have hB : 0 < integralMatrixHeight M := lt_of_lt_of_le zero_lt_one hheight.1
  let f := windowTimeSchwartz K hc R hRp (t-ε) (t+ε)
  have hfs : Function.support (f : ℝ→ℂ)⊆Icc (-(U*R)) (U*R) := hs R hRp (t-ε) (t+ε)
  have hgs : Function.support (timeConvolution f f : ℝ→ℂ)⊆Icc (-(2*(U*R))) (2*(U*R)) := by
    simpa only [two_mul] using timeConvolution_support f f (U*R) (U*R) hfs hfs
  have hps : Function.support (windowSquareProfile K hc R hRp ε t)⊆Iic (Real.cosh (2*(U*R))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)
  exact cylinder_weighted_reflected_correspondence_bound M hM (integralMatrixHeight M) hB hheight.2
    o L (2*(U*R)) (by positivity) (windowSquareProfile K hc R hRp ε t)
    (windowSquareProfile_continuous K he hc R hRp ε t) hps
    (C*Real.sqrt t*R^2*ε^2) (by positivity)
    (fun d hd => hbound R ε t d hR hε hε1 ht hd) a A hA haB

#print axioms cylinder_weighted_reflected_correspondence_bound
#print axioms cylinder_window_reflected_branch_bound

end QuantitativeMaass
