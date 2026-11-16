module

public import QuantitativeMaassCuspCenteredKernelV1
public import QuantitativeMaassCenteredWindowBesselV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace MatrixGroups SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The squared-window Abel profile with the original two endpoints. -/
def windowTimeSquareProfile (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R) (a b : ℝ) : ℝ → ℂ :=
  abelProfile (evenCoshLift (timeConvolution (windowTimeSchwartz K hc R hR a b)
    (windowTimeSchwartz K hc R hR a b)))

theorem windowAbelColumn_kernel_cross (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (x y : ℍ) :
    inner ℂ (windowAbelColumn N K he hc R hR a b x)
      (windowAbelColumn N K he hc R hR a b y)=
      radialPoincareKernel N (windowTimeSquareProfile K hc R hR a b) y x := by
  unfold windowAbelColumn
  exact timeSquare_kernel_cross N _ _ _ (symmetricWindowTimeTest_real K he R a b) _ _ _ y x

/-- The actual high-cusp window column loses exactly its mean kernel term.
The propagation constant is chosen before every level, radius and endpoint. -/
theorem windowAbelColumn_high_centered_kernel (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B : ℝ,0<B ∧ ∀ (N : ℕ) [NeZero N] (R : ℝ) (hR : 0<R) (a b : ℝ)
      (A : SL(2,ℤ)) (u : ℝ),B*R<u → ∀ x : ℝ,
      ‖windowAbelColumn N K he hc R hR a b (cuspLogPoint N A u x)-
        cuspColumnMean N (windowAbelColumn N K he hc R hR a b) A u‖^2=
      (windowIdentityContribution K hc R hR a b).re+
      (windowGeometricRemainder N K hc R hR a b (cuspLogPoint N A u x)).re-
      (∫ y in Icc (0:ℝ) 1,radialPoincareKernel N (windowTimeSquareProfile K hc R hR a b)
        (cuspLogPoint N A u y) (cuspLogPoint N A u x)).re := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  refine ⟨B,hB,?_⟩
  intro N _ R hR a b A u hu x
  let f := windowTimeSchwartz K hc R hR a b
  have hBR : 0≤B*R := mul_nonneg hB.le hR.le
  have hps : Function.support (windowTimeSquareProfile K hc R hR a b)⊆
      Iic (Real.cosh (B*R+B*R)) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (add_nonneg hBR hBR)
      (timeConvolution_support f f (B*R) (B*R) (hs R hR a b) (hs R hR a b)))
  have hh := cuspColumn_high_centered_kernel N (windowAbelColumn N K he hc R hR a b)
    (windowAbelColumn_continuous N K he hc R hR a b)
    (windowAbelColumn_invariant N K he hc R hR a b)
    (windowTimeSquareProfile K hc R hR a b)
    (windowAbelColumn_kernel_cross N K he hc R hR a b)
    (B*R+B*R) (add_nonneg hBR hBR) hps A u (by linarith) x
  rw [windowAbelColumn_norm_square] at hh
  exact hh

#print axioms windowAbelColumn_kernel_cross
#print axioms windowAbelColumn_high_centered_kernel

end QuantitativeMaass
