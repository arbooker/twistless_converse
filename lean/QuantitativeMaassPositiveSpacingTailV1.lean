module

public import QuantitativeMaassPositiveParabolicSpacingV1
public import QuantitativeMaassCylinderSharpCuspV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- The sharp inverse-height Fourier-mass bound is unchanged by the
parabolic lattice spacing. This is the scaling needed in every cusp. -/
theorem parabolic_positive_spacing_tail (g : ℝ→ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (B : ℝ) (hs : Function.support g⊆Iic B)
    (hp : ∀ ξ,0≤(𝓕 (parabolicLineProfile g 1) ξ).re)
    (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,
      2*ENNReal.ofReal (z.im/q)*(∑' n : ℕ,ENNReal.ofReal
        (𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(z.im/q))).re))≤
      ENNReal.ofReal H⁻¹*ENNReal.ofReal (g 1).re := by
  let Q := parabolicLineSchwartz g hg B hs (1/q) (div_pos zero_lt_one hq)
  have hscale (ξ : ℝ) : 𝓕 Q ξ=((1/q:ℝ):ℂ)*𝓕 (parabolicLineProfile g 1) (ξ*(1/q)) := by
    change 𝓕 (parabolicLineProfile g (1/q)) ξ=_
    rw [funext (parabolicLineProfile_height_scale g (1/q)),
      real_fourier_height_scale _ (1/q) (div_pos zero_lt_one hq)]
  have hQp (ξ : ℝ) : 0≤(𝓕 Q ξ).re := by
    rw [hscale]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_nonneg (div_pos zero_lt_one hq).le (hp _)
  have hh := positive_fourier_highStrip_tail Q (parabolicLineProfile_even g (1/q)) hQp H hH
  have hzero : Q 0=g 1 := by
    change parabolicLineProfile g (1/q) 0=g 1
    simp only [parabolicLineProfile,zero_pow (by decide : 2≠0),zero_div,add_zero]
  rw [hzero] at hh
  have heq (z : ℍ) :
      2*ENNReal.ofReal z.im*(∑' n : ℕ,ENNReal.ofReal (𝓕 Q (((n+1:ℕ):ℝ)*z.im)).re)=
      2*ENNReal.ofReal (z.im/q)*(∑' n : ℕ,ENNReal.ofReal
        (𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(z.im/q))).re) := by
    have hcoef (n : ℕ) : ENNReal.ofReal (𝓕 Q (((n+1:ℕ):ℝ)*z.im)).re=
        ENNReal.ofReal (1/q)*ENNReal.ofReal
          (𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(z.im/q))).re := by
      rw [hscale]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
        ENNReal.ofReal_mul (div_pos zero_lt_one hq).le,Nat.cast_add,Nat.cast_one]
      congr 3
      ring
    simp_rw [hcoef]
    rw [ENNReal.tsum_mul_left]
    have hm : ENNReal.ofReal (z.im/q)=ENNReal.ofReal z.im*ENNReal.ofReal (1/q) := by
      rw [←ENNReal.ofReal_mul z.im_pos.le]
      congr 1
      ring
    rw [hm]
    ac_rfl
  simp_rw [heq] at hh
  exact hh

#print axioms parabolic_positive_spacing_tail

end QuantitativeMaass
