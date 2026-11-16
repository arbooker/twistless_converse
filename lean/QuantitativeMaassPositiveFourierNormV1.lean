module

public import QuantitativeMaassCenteredPoissonEnergyV1
public import QuantitativeMaassShiftedPoissonBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- A real even profile with nonnegative Fourier transform has no loss
when its Fourier coefficients are replaced by their norms. -/
theorem schwartz_fourier_norm_eq_re (F : SchwartzMap ℝ ℂ)
    (he : Function.Even F) (hr : ∀ x,star (F x)=F x)
    (hp : ∀ ξ,0≤(𝓕 F ξ).re) (ξ : ℝ) : ‖𝓕 F ξ‖=(𝓕 F ξ).re := by
  have hc := schwartz_fourier_real F he hr ξ
  have hi : (𝓕 F ξ).im=0 := by
    have hh := congrArg Complex.im hc
    change -(𝓕 F ξ).im=(𝓕 F ξ).im at hh
    linarith only [hh]
  have hh : 𝓕 F ξ=((𝓕 F ξ).re:ℂ) := Complex.ext rfl (by simpa using hi)
  calc
    _=‖((𝓕 F ξ).re:ℂ)‖ := congrArg norm hh
    _=_ := Complex.norm_of_nonneg (hp ξ)

/-- Positivity bounds every shifted centered periodization by the same
nonzero Fourier mass as the unshifted cylinder energy. -/
theorem schwartz_shifted_positive_bound (F : SchwartzMap ℝ ℂ)
    (he : Function.Even F) (hr : ∀ x,star (F x)=F x)
    (hp : ∀ ξ,0≤(𝓕 F ξ).re) (x : ℝ) :
    ‖(∑' k : ℤ,F (x+k))-𝓕 F 0‖≤2*(∑' n : ℕ,(𝓕 F (n+1)).re) := by
  simpa only [schwartz_fourier_norm_eq_re F he hr hp] using schwartz_shifted_poisson_bound F he x

#print axioms schwartz_fourier_norm_eq_re
#print axioms schwartz_shifted_positive_bound

end QuantitativeMaass
