module

public import QuantitativeMaassMovingWindowsV1
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The cosine packet of a compact smooth second derivative has the exact
quadratic spectral multiplier, with no parity assumption. -/
theorem cosinePacket_second_derivative (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (r : ℝ) :
    cosinePacket (deriv (deriv f)) r = -(r : ℂ)^2 * cosinePacket f r := by
  have hf1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hf1).2
  have hi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hc
  have hi1 : Integrable (deriv f) volume := hf1.continuous.integrable_of_hasCompactSupport hc.deriv
  have hi2 : Integrable (deriv (deriv f)) volume := hf2.continuous.integrable_of_hasCompactSupport hc.deriv.deriv
  have hfour (x : ℝ) : 𝓕 (deriv (deriv f)) x =
      -((2*Real.pi*x : ℝ) : ℂ)^2 * 𝓕 f x := by
    rw [Real.fourier_deriv hi1 (hf1.differentiable (by simp)) hi2,
      Real.fourier_deriv hi (hf.differentiable (by simp)) hi1]
    simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    calc
      _ = ((2*(Real.pi : ℂ)*(x : ℂ))^2 * Complex.I^2) * 𝓕 f x := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  unfold cosinePacket
  rw [compact_cosine_packet_fourier _ hf2 hc.deriv.deriv,
    compact_cosine_packet_fourier _ hf hc]
  change (𝓕 (deriv (deriv f)) (-r/(2*Real.pi)) +
      𝓕 (deriv (deriv f)) (r/(2*Real.pi)))/2 =
    -(r : ℂ)^2 * ((𝓕 f (-r/(2*Real.pi)) + 𝓕 f (r/(2*Real.pi)))/2)
  rw [hfour, hfour]
  have hp : 2*Real.pi*(r/(2*Real.pi)) = r := by field_simp
  have hm : 2*Real.pi*(-r/(2*Real.pi)) = -r := by field_simp
  rw [hp, hm, Complex.ofReal_neg, neg_sq]
  ring

/-- The source-column residual corresponds to the exact multiplier
r²−t². This retains the cancellation needed in its moment estimate. -/
theorem cosinePacket_spectral_residual (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (t r : ℝ) :
    cosinePacket (fun s => -deriv (deriv f) s - (t : ℂ)^2 * f s) r =
      ((r : ℂ)^2 - (t : ℂ)^2) * cosinePacket f r := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 := (contDiff_infty_iff_deriv.mp hf1).2
  have hi0 : Integrable (fun s => f s * (Real.cos (s*r) : ℂ)) :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport hc.mul_right
  have hi2 : Integrable (fun s => deriv (deriv f) s * (Real.cos (s*r) : ℂ)) :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport hc.deriv.deriv.mul_right
  have he : (fun s => (-deriv (deriv f) s - (t : ℂ)^2*f s)*(Real.cos (s*r) : ℂ)) =
      fun s => -(deriv (deriv f) s*(Real.cos (s*r) : ℂ)) -
        (t : ℂ)^2*(f s*(Real.cos (s*r) : ℂ)) := by funext s; ring
  have hsub : (∫ s, -(deriv (deriv f) s*(Real.cos (s*r) : ℂ)) -
      (t : ℂ)^2*(f s*(Real.cos (s*r) : ℂ))) =
      (∫ s, -(deriv (deriv f) s*(Real.cos (s*r) : ℂ))) -
      (∫ s, (t : ℂ)^2*(f s*(Real.cos (s*r) : ℂ))) :=
    integral_sub hi2.neg (hi0.const_mul _)
  unfold cosinePacket
  rw [he, hsub, integral_neg, integral_const_mul]
  change -cosinePacket (deriv (deriv f)) r - (t : ℂ)^2*cosinePacket f r = _
  rw [cosinePacket_second_derivative f hf hc r]
  simp only [cosinePacket]
  ring

#print axioms cosinePacket_second_derivative
#print axioms cosinePacket_spectral_residual

end QuantitativeMaass
