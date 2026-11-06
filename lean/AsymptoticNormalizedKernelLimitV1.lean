module

public import AsymptoticPeriodizedKernelLimitV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane Filter
open scoped Topology

theorem weight_ratio_tendsto :
    Tendsto (fun h : ℕ => ((2*h+1 : ℕ) : ℂ) / ((2*h+2 : ℕ) : ℂ)) atTop (𝓝 1) := by
  have hn : Tendsto (fun h : ℕ => 2*h+2) atTop atTop :=
    tendsto_atTop_mono (fun h => by omega : ∀ h : ℕ, h ≤ 2*h+2) tendsto_id
  have hi : Tendsto (fun h : ℕ => (((2*h+2 : ℕ) : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hr : Tendsto (fun h : ℕ => (1 : ℝ) - (((2*h+2 : ℕ) : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hi
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  apply hc.congr
  intro h
  simp only [Function.comp_apply]
  push_cast
  have hd : (2 : ℂ)*h+2 ≠ 0 := by exact_mod_cast (show (2 : ℝ)*h+2 ≠ 0 by positivity)
  field_simp [hd]
  ring

/-- The actual Fourier kernel, including the hyperbolic height factors,
has the normalized return limit 1/(4π), and vanishes off integer returns. -/
theorem normalized_hyperbolicKernel_tendsto {ε : ℝ} (hε : 0 < ε) (z u : ℍ) :
    Tendsto (fun h : ℕ => ((z.im*u.im : ℝ) * fourierKernel h ε z u) /
      ((2*h+2 : ℕ) : ℂ)) atTop (𝓝 (returnValue z u / (4*Real.pi))) := by
  have ht := (weight_ratio_tendsto.mul (periodized_kernel_tendsto z u)).div_const (4*Real.pi : ℂ)
  simp only [one_mul] at ht
  apply ht.congr
  intro h
  rw [hyperbolicKernel_periodization h hε z u]
  ring

#print axioms weight_ratio_tendsto
#print axioms normalized_hyperbolicKernel_tendsto

end AsymptoticUnweightedKernel
