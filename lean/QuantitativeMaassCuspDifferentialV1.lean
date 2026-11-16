module

public import QuantitativeMaassCuspChartCovarianceV1
public import QuantitativeMaassSmoothPeriodV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter Matrix UpperHalfPlane
open scoped Topology ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential AsymptoticCongruenceStrip

/-- A Cartesian representative restricted to the actual upper half-plane. -/
def upperFunction (u : Point → ℂ) (z : ℍ) : ℂ := u (z.re,z.im)

/-- Its actual hyperbolic Laplacian, restricted to the upper half-plane. -/
def upperLaplacian (u : Point → ℂ) (z : ℍ) : ℂ := hyperbolic u (z.re,z.im)

theorem cuspProfile_upperFunction (N : ℕ) (s : SL(2,ℤ)) (u : Point → ℂ)
    (x y : ℝ) (hy : 0<y) :
    cuspProfile N s (upperFunction u) x y=
      scaledProfile N (u ∘ integralCuspChart s) x y := by
  simp only [cuspProfile,dite_eq_left hy,upperFunction,scaledProfile,Function.comp_apply]
  rw [integralCuspChart_action s _ _ hy]

/-- This is the exact N-scaled chart used by the all-cusp Hecke identities. -/
theorem cuspConstant_upperFunction (N : ℕ) (s : SL(2,ℤ)) (u : Point → ℂ)
    (y : ℝ) (hy : 0<y) :
    cuspConstant N s (upperFunction u) y=
      zeroFourier (scaledProfile N (u ∘ integralCuspChart s)) y := by
  unfold cuspConstant zeroFourier
  apply intervalIntegral.integral_congr
  intro x _
  exact cuspProfile_upperFunction N s u x y hy

theorem cuspProfile_upperLaplacian (N : ℕ) (hN : N≠0) (s : SL(2,ℤ))
    {u : Point → ℂ} (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (x y : ℝ) (hy : 0<y) :
    cuspProfile N s (upperLaplacian u) x y=
      periodLaplacian N (scaledProfile N (u ∘ integralCuspChart s)) x y := by
  rw [periodLaplacian_scaledProfile _ (by exact_mod_cast hN)
    (integralCuspChart_pullback_smooth s hu) _ _ hy,
    hyperbolic_integralCuspChart s hu _ _ hy]
  simp only [cuspProfile,dite_eq_left hy,upperLaplacian]
  rw [integralCuspChart_action s _ _ hy]

/-- The genuine all-cusp constant-term/Laplacian differential intertwining,
with the same average and common period N as the arithmetic Hecke theorem.
Only smoothness of the representative and actual level invariance are inputs. -/
theorem cuspConstant_upperLaplacian (N : ℕ) (hN : N≠0) (s : SL(2,ℤ))
    {u : Point → ℂ} (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hinv : ∀ g : gamma N, ∀ z : ℍ, upperFunction u (g.val • z)=upperFunction u z)
    (y : ℝ) (hy : 0<y) :
    cuspConstant N s (upperLaplacian u) y=
      -(y:ℂ)^2*deriv (deriv (cuspConstant N s (upperFunction u))) y := by
  let V : Point → ℂ := Function.uncurry (scaledProfile N (u ∘ integralCuspChart s))
  have hV : ContDiffOn ℝ ∞ V {Z | 0<Z.2} :=
    scaledProfile_smooth N (integralCuspChart_pullback_smooth s hu)
  have hperiod : ∀ v, 0<v → Function.Periodic (fun x => V (x,v)) 1 := by
    intro v hv x
    change scaledProfile N (u ∘ integralCuspChart s) (x+1) v=
      scaledProfile N (u ∘ integralCuspChart s) x v
    rw [← cuspProfile_upperFunction N s u (x+1) v hv,
      ← cuspProfile_upperFunction N s u x v hv]
    exact cuspProfile_periodic N s (upperFunction u) hinv v x
  have hCT : cuspConstant N s (upperLaplacian u) y=
      zeroFourier (periodLaplacian N (Function.curry V)) y := by
    unfold cuspConstant zeroFourier
    apply intervalIntegral.integral_congr
    intro x _
    exact cuspProfile_upperLaplacian N hN s hu x y hy
  rw [hCT,zeroFourier_periodLaplacian_smooth N hV hperiod y hy]
  congr 1
  have he : cuspConstant N s (upperFunction u) =ᶠ[𝓝 y]
      zeroFourier (Function.curry V) := by
    filter_upwards [Ioi_mem_nhds hy] with v hv
    exact cuspConstant_upperFunction N s u v hv
  exact he.deriv.deriv_eq.symm

#print axioms cuspProfile_upperLaplacian
#print axioms cuspConstant_upperLaplacian

end QuantitativeMaass
