module

public import QuantitativeMaassCuspTruncatedKernelV1
public import QuantitativeMaassIntegratedWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped Topology MatrixGroups FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The actual fixed-propagation window nonidentity kernel has a uniform
truncated cusp-chart integral O(sqrt(t)*(1+sqrt(H))). -/
theorem windowGeometricRemainder_fixedRadius_cusp_integral (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 1≤R) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) (A : SL(2,ℤ)) (ε t H : ℝ),
      0≤ε → ε≤1 → 1≤t → (1:ℝ)/4≤H →
      (∫ z in QuantitativeSpectralObservability.wideBox H,
        ‖windowGeometricRemainder N K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (A•z)‖)≤
        C*Real.sqrt t*ε^2*(1+Real.sqrt H) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  obtain ⟨D,hD,hgeom⟩ := radialNonidentity_cusp_truncation_bound (2*(B*R)) (by positivity)
  refine ⟨D*C*R^2,by positivity,?_⟩
  intro N A ε t H hε hε1 ht hH
  let f := windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)
  have hfs : Function.support (f : ℝ → ℂ)⊆Icc (-(B*R)) (B*R) := by
    change Function.support (symmetricWindowTimeTest K R (t-ε) (t+ε))⊆_
    exact hs R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)
  have hgs : Function.support (timeConvolution f f : ℝ → ℂ)⊆Icc (-(2*(B*R))) (2*(B*R)) := by
    simpa only [two_mul] using timeConvolution_support f f (B*R) (B*R) hfs hfs
  have hps : Function.support (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t)⊆Iic (Real.cosh (2*(B*R))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)
  have hp : ∀ d : ℝ,0<d → ‖windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t (Real.cosh d)‖≤
      (C*Real.sqrt t*R^2*ε^2)/Real.sqrt (Real.sinh d) := by
    intro d hd
    dsimp only [windowSquareProfile]
    exact hbound R ε t d hR hε hε1 ht hd
  have hh := hgeom N A (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t)
    (windowSquareProfile_continuous K he hc R (lt_of_lt_of_le zero_lt_one hR) ε t) hps
    (C*Real.sqrt t*R^2*ε^2) (by positivity) hp H hH
  convert hh using 1
  · rfl
  · ring

#print axioms windowGeometricRemainder_fixedRadius_cusp_integral

end QuantitativeMaass
