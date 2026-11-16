module

public import QuantitativeMaassPhysicalAbelSmoothV1
public import QuantitativeMaassCuspPositiveTailV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace MatrixGroups SchwartzMap FourierTransform ENNReal

namespace QuantitativeMaass

/-- Sharp inverse-height tail for the actual quotient window column in
unit horizontal cusp coordinates. No cylinder comparison is assumed. -/
theorem windowAbelColumn_centered_sharp_cusp_tail (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B : ℝ,0<B ∧ ∀ (N : ℕ) [NeZero N],0<N → ∀ (R : ℝ) (hR : 0<R) (a b : ℝ)
      (A : SL(2,ℤ)) (H : ℝ),0<H → B*R<Real.log H →
      (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,
        ENNReal.ofReal (‖windowAbelColumn N K he hc R hR a b
          (cuspLogPoint N A (Real.log z.im) z.re)-
          cuspColumnMean N (windowAbelColumn N K he hc R hR a b) A (Real.log z.im)‖^2))≤
        ENNReal.ofReal (2*(Fintype.card (cuspAdmissibleResidues N A):ℝ))*
          (ENNReal.ofReal H⁻¹*ENNReal.ofReal (windowTimeSquareProfile K hc R hR a b 1).re) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  refine ⟨B,hB,?_⟩
  intro N _ hN R hR a b A H hH hheight
  let f := windowTimeSchwartz K hc R hR a b
  have hBR : 0≤B*R+B*R := by positivity
  have hps : Function.support (windowTimeSquareProfile K hc R hR a b)⊆Iic (Real.cosh (B*R+B*R)) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ hBR
      (timeConvolution_support f f (B*R) (B*R) (hs R hR a b) (hs R hR a b)))
  have hfr : ∀ t,star (f t)=f t := symmetricWindowTimeTest_real K he R a b
  have hgr : ∀ v,star (windowTimeSquareProfile K hc R hR a b v)=
      windowTimeSquareProfile K hc R hR a b v :=
    abelProfile_real _ (evenCoshLift_real _ (timeConvolution_real f f hfr hfr))
  have hgp : ∀ ξ,0≤(𝓕 (parabolicLineProfile (windowTimeSquareProfile K hc R hR a b) 1) ξ).re :=
    timeSquareLine_fourier_nonneg f (symmetricWindowTimeTest_compact K hc R a b hR)
      (symmetricWindowTimeTest_even K he R a b) hfr (B*R) (by positivity) (hs R hR a b)
  exact cuspColumn_centered_positive_tail N hN (windowAbelColumn N K he hc R hR a b)
    (windowAbelColumn_continuous N K he hc R hR a b)
    (windowAbelColumn_invariant N K he hc R hR a b)
    (windowTimeSquareProfile K hc R hR a b) (windowTimeSquareProfile_smoothOn K he hc R hR a b) hgr hgp
    (windowAbelColumn_kernel_cross N K he hc R hR a b)
    (B*R+B*R) hBR hps A H hH (by linarith)

#print axioms windowAbelColumn_centered_sharp_cusp_tail

end QuantitativeMaass
