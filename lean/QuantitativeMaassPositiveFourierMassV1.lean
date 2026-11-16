module

public import QuantitativeMaassSchwartzPositiveModesV1
public import QuantitativeMaassFrequencyTailDilationV1
public import QuantitativeMaassAbelCosineRepresentationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Fourier inversion at zero gives the full horizontal frequency mass. -/
theorem schwartz_fourier_integral (F : SchwartzMap ℝ ℂ) :
    (∫ u,𝓕 F u)=F 0 := by
  have hh := congrFun (F.continuous.fourierInv_fourier_eq F.integrable
    (𝓕 F : SchwartzMap ℝ ℂ).integrable) 0
  rw [Real.fourierInv_eq_fourier_neg,neg_zero] at hh
  simpa only [Real.fourier_real_eq_integral_exp_smul,mul_zero,Complex.ofReal_zero,
    zero_mul,Complex.exp_zero,one_smul,SchwartzMap.fourier_coe] using hh

/-- The positive half-line mass is exactly half the diagonal value, with
nonnegativity retained in the extended nonnegative integral. -/
theorem schwartz_positive_fourier_mass (F : SchwartzMap ℝ ℂ)
    (he : Function.Even F) (hp : ∀ u,0≤(𝓕 F u).re) :
    2*(∫⁻ u in Ioi (0:ℝ),ENNReal.ofReal (𝓕 F u).re)=ENNReal.ofReal (F 0).re := by
  have hh := integral_even_eq_two_half ((𝓕 F : SchwartzMap ℝ ℂ) : ℝ→ℂ)
    (𝓕 F : SchwartzMap ℝ ℂ).integrable (schwartz_fourier_even F he)
  rw [schwartz_fourier_integral] at hh
  have hr := congrArg Complex.re hh
  simp only [smul_eq_mul,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,sub_zero] at hr
  have hRe := integral_re (μ := volume.restrict (Ioi (0:ℝ)))
    (𝓕 F : SchwartzMap ℝ ℂ).integrable.integrableOn
  change (∫ u in Ioi (0:ℝ),(𝓕 F u).re)=(∫ u in Ioi (0:ℝ),𝓕 F u).re at hRe
  rw [←hRe] at hr
  have hi : IntegrableOn (fun u : ℝ => (𝓕 F u).re) (Ioi (0:ℝ)) :=
    (𝓕 F : SchwartzMap ℝ ℂ).integrable.re.integrableOn
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hp),
    hr,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_ofNat]

/-- All nonzero positive horizontal modes above height H have total mass
bounded by the diagonal divided by H. -/
theorem schwartz_positive_frequency_tail (F : SchwartzMap ℝ ℂ)
    (he : Function.Even F) (hp : ∀ u,0≤(𝓕 F u).re) (H : ℝ) (hH : 0<H) :
    2*(∫⁻ y in Ici H,∑' n : ℕ,
      ENNReal.ofReal (𝓕 F (((n+1:ℕ):ℝ)*y)).re/ENNReal.ofReal y)≤
      ENNReal.ofReal H⁻¹*ENNReal.ofReal (F 0).re := by
  have hh := positive_frequency_height_tail (fun u => ENNReal.ofReal (𝓕 F u).re)
    (Complex.continuous_re.comp (𝓕 F : SchwartzMap ℝ ℂ).continuous).measurable.ennreal_ofReal H hH
  calc
    _≤2*(ENNReal.ofReal H⁻¹*(∫⁻ u in Ioi (0:ℝ),ENNReal.ofReal (𝓕 F u).re)) :=
      mul_le_mul' le_rfl hh
    _=ENNReal.ofReal H⁻¹*(2*(∫⁻ u in Ioi (0:ℝ),ENNReal.ofReal (𝓕 F u).re)) := by ac_rfl
    _=_ := by rw [schwartz_positive_fourier_mass F he hp]

#print axioms schwartz_fourier_integral
#print axioms schwartz_positive_fourier_mass
#print axioms schwartz_positive_frequency_tail

end QuantitativeMaass
