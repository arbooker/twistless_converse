module

public import QuantitativeMaassCenteredPoissonEnergyV1
public import QuantitativeMaassCuspHeightMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Positive horizontal Fourier mass on the actual cusp strip, with the
sharp inverse-height factor and the exact diagonal normalization. -/
theorem positive_fourier_highStrip_tail (F : SchwartzMap ℝ ℂ)
    (he : Function.Even F) (hp : ∀ u,0≤(𝓕 F u).re) (H : ℝ) (hH : 0<H) :
    (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,
      2*ENNReal.ofReal z.im*(∑' n : ℕ,ENNReal.ofReal
        (𝓕 F (((n+1:ℕ):ℝ)*z.im)).re))≤
      ENNReal.ofReal H⁻¹*ENNReal.ofReal (F 0).re := by
  let g := fun y : ℝ => 2*ENNReal.ofReal y*(∑' n : ℕ,ENNReal.ofReal
    (𝓕 F (((n+1:ℕ):ℝ)*y)).re)
  have hm : Measurable g := by
    have hc : Continuous (fun u : ℝ => (𝓕 F u).re) :=
      Complex.continuous_re.comp (𝓕 F : SchwartzMap ℝ ℂ).continuous
    apply Measurable.mul
    · fun_prop
    · apply Measurable.tsum
      intro n
      exact (hc.comp (continuous_const.mul continuous_id)).measurable.ennreal_ofReal
  change (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,g z.im)≤_
  rw [lintegral_highStrip_height g hm H hH]
  have hpoint (y : ℝ) (hy : y∈Ici H) : g y/(ENNReal.ofReal y)^2=
      2*(∑' n : ℕ,ENNReal.ofReal (𝓕 F (((n+1:ℕ):ℝ)*y)).re/ENNReal.ofReal y) := by
    have hy0 : ENNReal.ofReal y≠0 := (ENNReal.ofReal_pos.mpr (hH.trans_le hy)).ne'
    have hinv : ((ENNReal.ofReal y)^2)⁻¹=(ENNReal.ofReal y)⁻¹*(ENNReal.ofReal y)⁻¹ := by
      rw [ENNReal.inv_pow,pow_two]
    dsimp only [g]
    rw [div_eq_mul_inv,hinv]
    calc
      _=(2*(∑' n : ℕ,ENNReal.ofReal (𝓕 F (((n+1:ℕ):ℝ)*y)).re)*ENNReal.ofReal y*
        (ENNReal.ofReal y)⁻¹)*(ENNReal.ofReal y)⁻¹ := by ac_rfl
      _=2*(∑' n : ℕ,ENNReal.ofReal (𝓕 F (((n+1:ℕ):ℝ)*y)).re)*(ENNReal.ofReal y)⁻¹ := by
        rw [ENNReal.mul_inv_cancel_right hy0 ENNReal.ofReal_ne_top]
      _=_ := by simp_rw [div_eq_mul_inv]; rw [ENNReal.tsum_mul_right,mul_assoc]
  rw [setLIntegral_congr_fun measurableSet_Ici hpoint,
    lintegral_const_mul' _ _ (by norm_num)]
  exact schwartz_positive_frequency_tail F he hp H hH

/-- Sharp cusp tail for the genuine centered cylinder column: its total
squared energy above H is bounded by the convolution-square diagonal/H. -/
theorem cylinderTimeColumn_centered_sharp_tail (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (H : ℝ) (hH : 0<H) :
    (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,
      ENNReal.ofReal (‖cylinderTimeColumn f hc he R hR hs z-
        ∫ x in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (x+ᵥz)‖^2))≤
      ENNReal.ofReal H⁻¹*ENNReal.ofReal
        (abelProfile (evenCoshLift (timeConvolution f f)) 1).re := by
  let F := evenCoshLift (timeConvolution f f)
  have hF : ContDiffOn ℝ ∞ F (Ici 1) :=
    evenCoshLift_smoothOn _ ((timeConvolution f f).smooth ⊤)
      (timeConvolution_even f f he he) (timeConvolution_compact f f hc hc)
  have hFs : Function.support F⊆Iic (Real.cosh (R+R)) :=
    evenCoshLift_support_of_time_support _ _ (add_nonneg hR hR)
      (timeConvolution_support f f R R hs hs)
  have hg := abelProfile_smoothOn_physical F hF (Real.cosh (R+R)) (Real.one_le_cosh _) hFs
  let Q := parabolicLineSchwartz (abelProfile F) hg (Real.cosh (R+R))
    (abelProfile_support F _ hFs) 1 zero_lt_one
  have hp : ∀ u,0≤(𝓕 Q u).re := by
    intro u
    change 0≤(𝓕 (parabolicLineProfile (abelProfile F) 1) u).re
    exact timeSquareLine_fourier_nonneg f hc he hr R hR hs u
  have hb := positive_fourier_highStrip_tail Q (parabolicLineProfile_even (abelProfile F) 1) hp H hH
  simp_rw [cylinderTimeColumn_centered_positive_modes f hc he hr R hR hs]
  have hzero : Q 0=abelProfile F 1 := by
    change parabolicLineProfile (abelProfile F) 1 0=_
    simp only [parabolicLineProfile,zero_pow (by decide : 2≠0),zero_div,add_zero]
  rw [hzero] at hb
  exact hb

#print axioms positive_fourier_highStrip_tail
#print axioms cylinderTimeColumn_centered_sharp_tail

end QuantitativeMaass
