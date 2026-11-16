module

public import QuantitativeArithmeticMaassResidualWindowIdentityV1
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The actual residual time test, retaining its Schwartz structure. -/
def spectralResidualSchwartz (t : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) - (t : ℂ)^2 • f

theorem spectralResidualSchwartz_coe (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    (spectralResidualSchwartz t f : ℝ → ℂ) = spectralTimeResidual t f := rfl

theorem spectralResidualSchwartz_even (t : ℝ) (f : SchwartzMap ℝ ℂ)
    (he : Function.Even f) : Function.Even (spectralResidualSchwartz t f) :=
  spectralTimeResidual_even t f he

theorem spectralResidualSchwartz_compact (t : ℝ) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    HasCompactSupport (spectralResidualSchwartz t f : ℝ → ℂ) :=
  spectralTimeResidual_compact t f hc

/-- Uniqueness of the cosine transform on even Schwartz functions. -/
theorem even_schwartz_eq_of_cosinePacket_eq (f g : SchwartzMap ℝ ℂ)
    (hf : Function.Even f) (hg : Function.Even g)
    (heq : ∀ r, cosinePacket f r = cosinePacket g r) : f = g := by
  have hangular : angularFourier f = angularFourier g := by
    ext r
    rw [← cosinePacket_eq_angularFourier f hf, ← cosinePacket_eq_angularFourier g hg]
    exact heq r
  ext s
  have h := congrArg (fun h : SchwartzMap ℝ ℂ => cosinePacket h s) hangular
  rw [cosinePacket_angularFourier f hf, cosinePacket_angularFourier g hg] at h
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) h

/-- Squaring the residual column is exactly the same as applying two
residual multipliers to the original convolution square. This connects the
residual-column energy to the diagonal/off-diagonal bounds already proved. -/
theorem spectralResidualSchwartz_convolution_square (t : ℝ) (f : SchwartzMap ℝ ℂ)
    (he : Function.Even f) (hc : HasCompactSupport (f : ℝ → ℂ)) :
    timeConvolution (spectralResidualSchwartz t f) (spectralResidualSchwartz t f) =
      spectralResidualSchwartz t (spectralResidualSchwartz t (timeConvolution f f)) := by
  have hre := spectralResidualSchwartz_even t f he
  have hconv := timeConvolution_even f f he he
  apply even_schwartz_eq_of_cosinePacket_eq _ _
    (timeConvolution_even _ _ hre hre)
    (spectralResidualSchwartz_even t _ (spectralResidualSchwartz_even t _ hconv))
  intro r
  rw [cosinePacket_timeConvolution _ _ hre hre]
  have hr : cosinePacket (spectralResidualSchwartz t f) r =
      ((r : ℂ)^2-(t : ℂ)^2)*cosinePacket f r :=
    cosinePacket_spectral_residual f (f.smooth ⊤) hc t r
  rw [hr]
  have hh := cosinePacket_spectralTimeResidual_twice t (timeConvolution f f)
    ((timeConvolution f f).smooth ⊤) (timeConvolution_compact f f hc hc) r
  change _ = cosinePacket (spectralTimeResidual t (spectralTimeResidual t (timeConvolution f f))) r
  rw [hh, cosinePacket_timeConvolution f f he he]
  ring

/-- The convolution-square radial profile of the residual packet is the
literal residual profile estimated in the companion chapters. -/
theorem spectralResidualSchwartz_abel_square (t : ℝ) (f : SchwartzMap ℝ ℂ)
    (he : Function.Even f) (hc : HasCompactSupport (f : ℝ → ℂ)) :
    abelProfile (evenCoshLift
      (timeConvolution (spectralResidualSchwartz t f) (spectralResidualSchwartz t f))) =
      abelProfile (evenCoshLift
        (spectralTimeResidual t (spectralTimeResidual t (timeConvolution f f)))) := by
  rw [spectralResidualSchwartz_convolution_square t f he hc]
  rfl

#print axioms even_schwartz_eq_of_cosinePacket_eq
#print axioms spectralResidualSchwartz_convolution_square
#print axioms spectralResidualSchwartz_abel_square

end QuantitativeMaass
