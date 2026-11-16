module

public import QuantitativeMaassRadialKernelOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The Abel profile above one depends only on the test strictly above one. -/
theorem abelProfile_congr_above_one (F G : ℝ → ℂ) (he : ∀ q,1<q → F q=G q)
    (q : ℝ) (hq : 1≤q) : abelProfile F q=abelProfile G q := by
  have hd (v : ℝ) (hv : 1<v) : deriv F v=deriv G v := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hv] with w hw
    exact he w hw
  unfold abelProfile abelIntegral
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  apply hd
  have hs' : 0<s := hs
  nlinarith [sq_pos_of_pos hs']

/-- Radial kernels only evaluate their profiles at cosh distances, hence
values below one have no effect on the actual periodized kernel. -/
theorem radialPoincareKernel_congr_above_one (N : ℕ) (g h : ℝ → ℂ)
    (he : ∀ q,1≤q → g q=h q) (x y : ℍ) :
    radialPoincareKernel N g x y=radialPoincareKernel N h x y := by
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  apply tsum_congr
  intro γ
  exact he _ (Real.one_le_cosh _)

theorem radialKernelOperator_congr_above_one (N : ℕ) [NeZero N]
    (g h : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (R S : ℝ) (hR : 0≤R) (hS : 0≤S)
    (hsg : Function.support g⊆Iic (Real.cosh R))
    (hsh : Function.support h⊆Iic (Real.cosh S))
    (he : ∀ q,1≤q → g q=h q) :
    radialKernelOperator N g hg R hR hsg=radialKernelOperator N h hh S hS hsh := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [radialKernelOperator_coeFn N g hg R hR hsg f,
    radialKernelOperator_coeFn N h hh S hS hsh f] with x hx hy
  rw [hx,hy]
  apply integral_congr_ae
  filter_upwards with y
  rw [radialPoincareKernel_congr_above_one N g h he x y]

/-- A change of smooth extension below q=1 leaves the constructed geometric
operator unchanged, even when its two support-radius witnesses differ. -/
theorem abelKernelOperator_congr_above_one (N : ℕ) [NeZero N]
    (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (R S : ℝ) (hR : 0≤R) (hS : 0≤S)
    (hsF : Function.support F⊆Iic (Real.cosh R))
    (hsG : Function.support G⊆Iic (Real.cosh S))
    (he : ∀ q,1<q → F q=G q) :
    abelKernelOperator N F hF hcF R hR hsF=abelKernelOperator N G hG hcG S hS hsG :=
  radialKernelOperator_congr_above_one N (abelProfile F) (abelProfile G)
    (abelProfile_smooth F hF hcF) (abelProfile_smooth G hG hcG) R S hR hS
    (abelProfile_support F _ hsF) (abelProfile_support G _ hsG)
    (abelProfile_congr_above_one F G he)

#print axioms abelProfile_congr_above_one
#print axioms radialKernelOperator_congr_above_one
#print axioms abelKernelOperator_congr_above_one

end QuantitativeMaass
