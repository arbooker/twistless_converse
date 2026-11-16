module

public import QuantitativeArithmeticMaassResidualConvolutionV1
public import QuantitativeMaassCylinderCorrespondenceErrorV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

theorem spectralTimeResidual_support (t : ℝ) (f : ℝ → ℂ) (R : ℝ)
    (hs : Function.support f ⊆ Icc (-R) R) :
    Function.support (spectralTimeResidual t f) ⊆ Icc (-R) R := by
  have hd : Function.support (deriv (deriv f)) ⊆ Icc (-R) R :=
    support_deriv_subset.trans
      (tsupport_deriv_subset.trans (closure_minimal hs isClosed_Icc))
  intro x hx
  by_contra hn
  have hf0 : f x = 0 := by
    by_contra h
    exact hn (hs h)
  have hd0 : deriv (deriv f) x = 0 := by
    by_contra h
    exact hn (hd h)
  exact hx (by simp [spectralTimeResidual, hf0, hd0])

/-- Residual-square profile of the literal one-sided window. -/
def windowResidualSquareProfile (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (R : ℝ) (hR : 0 < R) (t ε : ℝ) : ℝ → ℂ :=
  abelProfile (evenCoshLift (spectralTimeResidual t (spectralTimeResidual t
    (timeConvolution (windowTimeSchwartz K hc R hR t (t+ε))
      (windowTimeSchwartz K hc R hR t (t+ε))))))

theorem windowResidualSquareProfile_continuous (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (R : ℝ) (hR : 0 < R) (t ε : ℝ) :
    ContinuousOn (windowResidualSquareProfile K hc R hR t ε) (Ici 1) := by
  let f := windowTimeSchwartz K hc R hR t (t+ε)
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R t (t+ε)
  have hfc : HasCompactSupport (f : ℝ → ℂ) :=
    symmetricWindowTimeTest_compact K hc R t (t+ε) hR
  exact evenTime_abel_continuous _
    (spectralTimeResidual_smooth t _ (spectralTimeResidual_smooth t _
      ((timeConvolution f f).smooth ⊤)))
    (spectralTimeResidual_even t _ (spectralTimeResidual_even t _
      (timeConvolution_even f f hfe hfe)))
    (spectralTimeResidual_compact t _ (spectralTimeResidual_compact t _
      (timeConvolution_compact f f hfc hfc)))

/-- The residual derivatives do not enlarge the wave propagation radius. -/
theorem windowResidualSquareProfile_uniform_support (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) :
    ∃ U : ℝ, 0 < U ∧ ∀ (R : ℝ) (hR : 0 < R) (t ε : ℝ),
      Function.support (windowResidualSquareProfile K hc R hR t ε) ⊆
        Iic (Real.cosh (2*(U*R))) := by
  obtain ⟨U,hU,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  refine ⟨U,hU,?_⟩
  intro R hR t ε
  let f := windowTimeSchwartz K hc R hR t (t+ε)
  have hfs : Function.support (f : ℝ → ℂ) ⊆ Icc (-(U*R)) (U*R) := hs R hR t (t+ε)
  have hcs : Function.support (timeConvolution f f : ℝ → ℂ) ⊆
      Icc (-(2*(U*R))) (2*(U*R)) := by
    simpa only [two_mul] using timeConvolution_support f f (U*R) (U*R) hfs hfs
  exact abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _
    (by positivity) (spectralTimeResidual_support t _ _
      (spectralTimeResidual_support t _ _ hcs)))

/-- The actual residual remainder is integrable on every finite centre
region. The estimate includes the cylinder N=0 and is uniform in the
correspondence matrix through its displayed geometric costs. -/
theorem windowResidualSquare_integrated_remainder (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) :
    ∃ U C : ℝ, 0 < U ∧ 0 < C ∧ ∀ (N : ℕ)
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det)
      (o : ℍ) (L R t ε : ℝ) (hR : 1 ≤ R),
      1 ≤ t → 0 ≤ ε → ε ≤ 1 →
      let g := windowResidualSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) t ε
      IntegrableOn (radialIntegralRemainder N M hM g) (Metric.closedBall o L) ∧
      (∫ z in Metric.closedBall o L, ‖radialIntegralRemainder N M hM g z‖) ≤
        (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0
          (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o) : ℝ)*
        (C*t^2*Real.sqrt t*R^2*ε^2)*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L
          (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o+
            2*Real.log (2*integralMatrixHeight M)))) := by
  obtain ⟨U,hU,hs⟩ := windowResidualSquareProfile_uniform_support K hc
  obtain ⟨C,hC,hb⟩ := windowResidualSquare_abel_decay K he hc
  refine ⟨U,C,hU,hC,?_⟩
  intro N M hM o L R t ε hR ht hε hε1
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hheight := integralMatrixHeight_bounds M
  exact radialIntegralRemainder_all_integral_bound N M hM (integralMatrixHeight M)
    (lt_of_lt_of_le zero_lt_one hheight.1) hheight.2 o L (2*(U*R)) (by positivity)
    (windowResidualSquareProfile K hc R hRp t ε)
    (windowResidualSquareProfile_continuous K he hc R hRp t ε) (hs R hRp t ε)
    (C*t^2*Real.sqrt t*R^2*ε^2) (by positivity)
    (fun d hd => hb R ε t d hR hε hε1 ht hd)

#print axioms windowResidualSquareProfile_uniform_support
#print axioms windowResidualSquare_integrated_remainder

end QuantitativeMaass
