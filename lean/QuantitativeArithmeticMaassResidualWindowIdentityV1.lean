module

public import QuantitativeArithmeticMaassWindowResidualCarrierV1
public import QuantitativeMaassTimeResidualTransformV1
public import QuantitativeMaassWindowResidualUniformV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

theorem spectralTimeResidual_compact (t : ℝ) (f : ℝ → ℂ)
    (hc : HasCompactSupport f) : HasCompactSupport (spectralTimeResidual t f) := by
  change HasCompactSupport (-deriv (deriv f) - (fun _ => (t : ℂ)^2)*f)
  exact hc.deriv.deriv.neg.sub hc.mul_left

/-- The two residuals used in the off-diagonal estimate have exactly the
squared residual multiplier, including its mixed term. -/
theorem cosinePacket_spectralTimeResidual_twice (t : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (r : ℝ) :
    cosinePacket (spectralTimeResidual t (spectralTimeResidual t f)) r =
      ((r : ℂ)^2-(t : ℂ)^2)^2*cosinePacket f r := by
  have h1 : cosinePacket (spectralTimeResidual t f) r =
      ((r : ℂ)^2-(t : ℂ)^2)*cosinePacket f r :=
    cosinePacket_spectral_residual f hf hc t r
  have h2 : cosinePacket (spectralTimeResidual t (spectralTimeResidual t f)) r =
      ((r : ℂ)^2-(t : ℂ)^2)*cosinePacket (spectralTimeResidual t f) r :=
    cosinePacket_spectral_residual (spectralTimeResidual t f)
      (spectralTimeResidual_smooth t f hf) (spectralTimeResidual_compact t f hc) t r
  rw [h2,h1]
  ring

/-- The residual Abel diagonal of the actual window equals its explicit
positive spectral integral. No local trace asymptotic is assumed. -/
theorem windowResidualSquare_diagonal (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (R : ℝ) (hR : 0 < R) (t ε : ℝ) (ht : 0 < t) :
    abelProfile (evenCoshLift (spectralTimeResidual t (spectralTimeResidual t
      (timeConvolution (windowTimeSchwartz K hc R hR t (t+ε))
        (windowTimeSchwartz K hc R hR t (t+ε)))))) 1 =
      (1/(4*Real.pi) : ℂ) * ∫ r : ℝ,
        (((r^2-t^2)^2 *
          (smoothedWindow K R (Icc t (t+ε) ∪ Icc (-(t+ε)) (-t)) r)^2 *
          windowPlancherelWeight r : ℝ) : ℂ) := by
  let f := windowTimeSchwartz K hc R hR t (t+ε)
  have hf : Function.Even f := symmetricWindowTimeTest_even K he R t (t+ε)
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R t (t+ε) hR
  have hconv := (timeConvolution f f).smooth ⊤
  have hcc := timeConvolution_compact f f hfc hfc
  have hec := timeConvolution_even f f hf hf
  rw [abelProfile_evenCoshLift_fourier _
    (spectralTimeResidual_smooth t _ (spectralTimeResidual_smooth t _ hconv))
    (spectralTimeResidual_even t _ (spectralTimeResidual_even t _ hec))
    (spectralTimeResidual_compact t _ (spectralTimeResidual_compact t _ hcc))]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  rw [cosinePacket_spectralTimeResidual_twice t _ hconv hcc,
    cosinePacket_timeConvolution f f hf hf]
  have hcos : cosinePacket f r =
      (smoothedWindow K R (Icc t (t+ε) ∪ Icc (-(t+ε)) (-t)) r : ℂ) :=
    symmetricWindowTimeTest_cosinePacket K he hc R t (t+ε) r hR ht
  rw [hcos]
  simp only [windowPlancherelWeight, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sub]
  ring

/-- The identity term of the residual square is O_K(t³ ε), with an explicit
constant and the same one-sided window as the off-diagonal theorem. -/
theorem windowResidualSquare_diagonal_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (R t ε : ℝ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖abelProfile (evenCoshLift (spectralTimeResidual t (spectralTimeResidual t
      (timeConvolution
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε))
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε)))))) 1‖ ≤
      (576*(1+∫ x, |x|^5*K x)/(4*Real.pi))*t^3*ε := by
  have hb := symmetricWindow_residual_moment_uniform K hK hm R t ε hR ht hε hε1
  rw [windowResidualSquare_diagonal K he hc R _ t ε (lt_of_lt_of_le zero_lt_one ht), norm_mul]
  have hcoef : ‖(1/(4*Real.pi) : ℂ)‖ = 1/(4*Real.pi) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hcoef]
  have hi := norm_integral_le_of_norm_le hb.1 (show ∀ᵐ r : ℝ,
      ‖(((r^2-t^2)^2 *
          (smoothedWindow K R (Icc t (t+ε) ∪ Icc (-(t+ε)) (-t)) r)^2 *
          windowPlancherelWeight r : ℝ) : ℂ)‖ ≤
        (r^2-t^2)^2*|r| *
          (smoothedWindow K R (Icc t (t+ε) ∪ Icc (-(t+ε)) (-t)) r)^2 from by
    filter_upwards with r
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [windowPlancherelWeight, abs_mul, abs_sq]
    have hh := mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one (Real.pi*r)).le
      (show 0 ≤ (r^2-t^2)^2*
        (smoothedWindow K R (Icc t (t+ε) ∪ Icc (-(t+ε)) (-t)) r)^2*|r| by positivity)
    nlinarith only [hh])
  calc
    _ ≤ (1/(4*Real.pi))*((576*(1+∫ x, |x|^5*K x))*t^3*ε) :=
      mul_le_mul_of_nonneg_left (hi.trans hb.2) (by positivity)
    _ = _ := by ring

#print axioms cosinePacket_spectralTimeResidual_twice
#print axioms windowResidualSquare_diagonal
#print axioms windowResidualSquare_diagonal_bound

end QuantitativeMaass
