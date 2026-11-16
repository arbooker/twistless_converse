module

public import QuantitativeMaassCylinderPacketAlgebraV1
public import QuantitativeMaassPacketCrossKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- Continuous literal Abel column for a smooth compact cylinder packet. -/
def cylinderTimeColumn (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :=
  cylinderAbelColumn (evenCoshLift f) (evenCoshLift_smoothOn f (f.smooth ⊤) he hc)
    R hR (evenCoshLift_support_of_time_support f R hR hs)

/-- The square kernel is the inner product of actual continuous cylinder
columns at every pair of points. No finite quotient volume is used. -/
theorem cylinderTimeSquare_kernel_cross (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (x y : ℍ) :
    inner ℂ (cylinderTimeColumn f hc he R hR hs y) (cylinderTimeColumn f hc he R hR hs x)=
      radialPoincareKernel 0 (abelProfile (evenCoshLift (timeConvolution f f))) x y := by
  let F := evenCoshLift f
  have hF : ContDiffOn ℝ ∞ F (Ici 1) := evenCoshLift_smoothOn f (f.smooth ⊤) he hc
  have hsF : Function.support F⊆Iic (Real.cosh R) := evenCoshLift_support_of_time_support f R hR hs
  let g := timeConvolution f f
  have hgc : HasCompactSupport (g : ℝ → ℂ) := timeConvolution_compact f f hc hc
  have hge : Function.Even g := timeConvolution_even f f he he
  have hgr : ∀ t,star (g t)=g t := timeConvolution_real f f hr hr
  have hgs : Function.support g⊆Icc (-(R+R)) (R+R) := timeConvolution_support f f R R hs hs
  let G := evenCoshLift g
  have hG : ContDiffOn ℝ ∞ G (Ici 1) := evenCoshLift_smoothOn g (g.smooth ⊤) hge hgc
  have hsG : Function.support G⊆Iic (Real.cosh (R+R)) :=
    evenCoshLift_support_of_time_support g (R+R) (add_nonneg hR hR) hgs
  let c := fun z => cylinderAutomorphic (cylinderAbelColumn F hF R hR hsF z)
  let d := fun z => cylinderAutomorphic (cylinderAbelColumn G hG (R+R) (add_nonneg hR hR) hsG z)
  let A := Wave.shiftedQuotientWavePacket 0 f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
  have hAc (v : AutomorphicSpace 0) : (A v).val=ᵐ[quotientMeasure 0]
      (fun z => inner ℂ (c z) v) := by
    exact cylinderTimePacket_column_coeFn f (f.smooth ⊤) he hc hr R hR hs hsF v.val
  have hAd (v : AutomorphicSpace 0) : (A (A v)).val=ᵐ[quotientMeasure 0]
      (fun z => inner ℂ (d z) v) := by
    have hh := cylinderTimePacket_column_coeFn g (g.smooth ⊤) hge hgc hgr
      (R+R) (add_nonneg hR hR) hgs hsG v.val
    rw [cylinderTimePacket_convolution f f hc hc he] at hh
    exact hh
  have hcont := oneSidedAbelKernel_joint_continuous 0 G hG (R+R) (add_nonneg hR hR) hsG
  exact selfAdjoint_kernel_square_cross 0 A
    (Wave.shiftedQuotientWavePacket_isSelfAdjoint 0 f _ hr) c d
    (cylinderAutomorphic.continuous.comp (cylinderAbelColumn_continuous F hF R hR hsF))
    (cylinderAutomorphic.continuous.comp (cylinderAbelColumn_continuous G hG (R+R) (add_nonneg hR hR) hsG))
    (fun γ z => congrArg cylinderAutomorphic (cylinderAbelColumn_invariant F hF R hR hsF γ z))
    (fun γ z => congrArg cylinderAutomorphic (cylinderAbelColumn_invariant G hG (R+R) (add_nonneg hR hR) hsG γ z))
    (radialPoincareKernel 0 (abelProfile G))
    (fun z => Continuous.uncurry_left (f:=radialPoincareKernel 0 (abelProfile G)) z hcont)
    (fun z γ w => radialPoincareKernel_invariant 0 (abelProfile G) z w γ) hAc hAd
    (cylinderAbelColumn_coeFn G hG (R+R) (add_nonneg hR hR) hsG) x y

#print axioms cylinderTimeSquare_kernel_cross

end QuantitativeMaass
