module

public import QuantitativeMaassCuspDifferentialV1
public import QuantitativeMaassZeroChannelWaveV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter Matrix UpperHalfPlane
open scoped Topology ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential AsymptoticCongruenceStrip

/-- Differentiation of the actual compact horocycle average for a smooth
positive-height representative. -/
theorem zeroFourier_smooth_hasDerivAt {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (y : ℝ) (hy : 0<y) :
    HasDerivAt (zeroFourier (Function.curry u))
      (zeroFourier (Function.curry (Y u)) y) y := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have huY := dir_contDiffOn hu hs e₂
  exact hasDerivAt_zeroFourier_positive (Function.curry u) (Function.curry (Y u))
    (hu.continuousOn.mono (fun _ hz => hz.2))
    (huY.continuousOn.mono (fun _ hz => hz.2))
    (smooth_vertical_hasDerivAt hu) y hy

/-- The zero-channel generator identity for the actual constant term in
any integral cusp, with the same common period and average as Hecke.
This is a smooth differential theorem, not a full-line L² mapping claim. -/
theorem cuspConstant_logHalfDensity_generator (N : ℕ) (hN : N≠0) (s : SL(2,ℤ))
    {u : Point → ℂ} (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hinv : ∀ g : gamma N, ∀ z : ℍ, upperFunction u (g.val • z)=upperFunction u z)
    (t : ℝ) :
    -deriv (deriv (logHalfDensity (cuspConstant N s (upperFunction u)))) t=
      (Real.exp (-t/2):ℂ)*
        (cuspConstant N s (upperLaplacian u) (Real.exp t)-
          cuspConstant N s (upperFunction u) (Real.exp t)/4) := by
  let V : Point → ℂ := Function.uncurry (scaledProfile N (u ∘ integralCuspChart s))
  have hV : ContDiffOn ℝ ∞ V {Z | 0<Z.2} :=
    scaledProfile_smooth N (integralCuspChart_pullback_smooth s hu)
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hVY := dir_contDiffOn hV hs e₂
  have hC : ∀ y, 0<y → HasDerivAt (cuspConstant N s (upperFunction u))
      (zeroFourier (Function.curry (Y V)) y) y := by
    intro y hy
    apply (zeroFourier_smooth_hasDerivAt hV y hy).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with v hv
    exact cuspConstant_upperFunction N s u v hv
  rw [logHalfDensity_generator (cuspConstant N s (upperFunction u))
    (zeroFourier (Function.curry (Y V))) (zeroFourier (Function.curry (Y (Y V))))
    hC (zeroFourier_smooth_hasDerivAt hVY) t,
    cuspConstant_upperLaplacian N hN s hu hinv (Real.exp t) (Real.exp_pos t)]

#print axioms zeroFourier_smooth_hasDerivAt
#print axioms cuspConstant_logHalfDensity_generator

end QuantitativeMaass
