module

public import QuantitativeMaassPositiveFourierNormV1
public import QuantitativeMaassParabolicLatticeSpacingV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- A shifted parabolic lattice has a positive-frequency error bound
uniform in the shift, with its exact spacing and height factors. -/
theorem parabolic_positive_spacing_bound (g : ℝ→ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (B : ℝ) (hs : Function.support g⊆Iic B)
    (hr : ∀ u,star (g u)=g u)
    (hp : ∀ ξ,0≤(𝓕 (parabolicLineProfile g 1) ξ).re)
    (y q a : ℝ) (hy : 0<y) (hq : 0<q) :
    ‖(∑' k : ℤ,parabolicLineProfile g y (a+q*k))-
      q⁻¹ • ∫ v,parabolicLineProfile g y v‖≤
      2*(y/q)*(∑' n : ℕ,(𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(y/q))).re) := by
  let Q := parabolicLineSchwartz g hg B hs (y/q) (div_pos hy hq)
  have hscale (ξ : ℝ) : 𝓕 Q ξ=((y/q:ℝ):ℂ)*𝓕 (parabolicLineProfile g 1) (ξ*(y/q)) := by
    change 𝓕 (parabolicLineProfile g (y/q)) ξ=_
    rw [funext (parabolicLineProfile_height_scale g (y/q)),
      real_fourier_height_scale _ (y/q) (div_pos hy hq)]
  have hQr : ∀ x,star (Q x)=Q x := fun x => hr _
  have hQp (ξ : ℝ) : 0≤(𝓕 Q ξ).re := by
    rw [hscale]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_nonneg (div_pos hy hq).le (hp _)
  have hzero : 𝓕 Q 0=q⁻¹ • ∫ v,parabolicLineProfile g y v := by
    change 𝓕 (parabolicLineProfile g (y/q)) 0=_
    simp only [Real.fourier_real_eq_integral_exp_smul,mul_zero,Complex.ofReal_zero,
      zero_mul,Complex.exp_zero,one_smul]
    rw [parabolicLineProfile_mass_scale g (y/q) (div_pos hy hq),
      parabolicLineProfile_mass_scale g y hy,smul_smul]
    congr 1
    ring
  have hh := schwartz_shifted_positive_bound Q (parabolicLineProfile_even g (y/q)) hQr hQp (a/q)
  change ‖(∑' k : ℤ,parabolicLineProfile g (y/q) (a/q+k))-𝓕 Q 0‖≤_ at hh
  simp_rw [parabolicLineProfile_lattice_scale g y q a _ hy.ne' hq.ne'] at hh
  rw [hzero] at hh
  have hcoef (n : ℕ) : (𝓕 Q (n+1)).re=
      (y/q)*(𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(y/q))).re := by
    rw [hscale]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp_rw [hcoef] at hh
  rw [tsum_mul_left,←mul_assoc] at hh
  exact hh

#print axioms parabolic_positive_spacing_bound

end QuantitativeMaass
