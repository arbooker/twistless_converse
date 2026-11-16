module

public import QuantitativeMaassPhysicalAbelSmoothV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace MatrixGroups SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The actual window's height-one variation is finite. -/
theorem windowTimeSquareProfile_variation_integrable (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    Integrable (fun v => ‖deriv (parabolicLineProfile (windowTimeSquareProfile K hc R hR a b) 1) v‖) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  let f := windowTimeSchwartz K hc R hR a b
  have hBR : 0≤B*R+B*R := by positivity
  have hps : Function.support (windowTimeSquareProfile K hc R hR a b)⊆Iic (Real.cosh (B*R+B*R)) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ hBR
      (timeConvolution_support f f (B*R) (B*R) (hs R hR a b) (hs R hR a b)))
  have hsmooth := parabolicLineProfile_smooth _ (windowTimeSquareProfile_smoothOn K he hc R hR a b) 1
  have hcompact := parabolicLineProfile_compact _ _ hps 1 zero_lt_one
  exact (((contDiff_infty_iff_deriv.mp hsmooth).2).continuous.integrable_of_hasCompactSupport
    hcompact.deriv).norm

/-- Unconditional height-independent variation control for actual centered
window columns in every integral cusp. No radial regularity premise remains. -/
theorem windowAbelColumn_high_centered_variation (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B : ℝ,0<B ∧ ∀ (N : ℕ) [NeZero N],0<N → ∀ (R : ℝ) (hR : 0<R) (a b : ℝ)
      (A : SL(2,ℤ)) (u : ℝ),B*R<u → ∀ x : ℝ,
      ‖windowAbelColumn N K he hc R hR a b (cuspLogPoint N A u x)-
        cuspColumnMean N (windowAbelColumn N K he hc R hR a b) A u‖^2≤
      2*(Fintype.card (cuspAdmissibleResidues N A):ℝ)*
        ∫ v,‖deriv (parabolicLineProfile (windowTimeSquareProfile K hc R hR a b) 1) v‖ := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  refine ⟨B,hB,?_⟩
  intro N _ hN R hR a b A u hu x
  let f := windowTimeSchwartz K hc R hR a b
  have hBR : 0≤B*R+B*R := by positivity
  have hps : Function.support (windowTimeSquareProfile K hc R hR a b)⊆Iic (Real.cosh (B*R+B*R)) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ hBR
      (timeConvolution_support f f (B*R) (B*R) (hs R hR a b) (hs R hR a b)))
  exact cuspColumn_high_centered_variation N hN (windowAbelColumn N K he hc R hR a b)
    (windowAbelColumn_continuous N K he hc R hR a b)
    (windowAbelColumn_invariant N K he hc R hR a b)
    (windowTimeSquareProfile K hc R hR a b) (windowTimeSquareProfile_smoothOn K he hc R hR a b)
    (windowAbelColumn_kernel_cross N K he hc R hR a b)
    (B*R+B*R) hBR hps A u (by linarith) x

#print axioms windowTimeSquareProfile_variation_integrable
#print axioms windowAbelColumn_high_centered_variation

end QuantitativeMaass
