module

public import QuantitativeMaassPositiveSpacingTailV1
public import QuantitativeMaassWideCuspHeightMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open QuantitativeArithmeticMaassCuspBand
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Positive horizontal Fourier mass on the full actual cusp strip carries
exactly its width, with no dependence on the parabolic lattice spacing. -/
theorem parabolic_positive_wide_spacing_tail (W : ℕ) (g : ℝ→ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (B : ℝ) (hs : Function.support g⊆Iic B)
    (hp : ∀ ξ,0≤(𝓕 (parabolicLineProfile g 1) ξ).re)
    (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    (∫⁻ z in cuspTailSet W H,
      2*ENNReal.ofReal (z.im/q)*(∑' n : ℕ,ENNReal.ofReal
        (𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(z.im/q))).re))≤
      (W:ℝ≥0∞)*(ENNReal.ofReal H⁻¹*ENNReal.ofReal (g 1).re) := by
  let E := fun y : ℝ => 2*ENNReal.ofReal (y/q)*(∑' n : ℕ,ENNReal.ofReal
    (𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(y/q))).re)
  have hF : Continuous (fun ξ : ℝ => (𝓕 (parabolicLineProfile g 1) ξ).re) :=
    Complex.continuous_re.comp (𝓕 (parabolicLineSchwartz g hg B hs 1 zero_lt_one) : SchwartzMap ℝ ℂ).continuous
  have hE : Measurable E := by
    apply Measurable.mul
    · fun_prop
    · apply Measurable.tsum
      intro n
      exact (hF.comp (continuous_const.mul (continuous_id.div_const q))).measurable.ennreal_ofReal
  change (∫⁻ z in cuspTailSet W H,E z.im)≤_
  rw [lintegral_cuspTail_height W E hE H hH,←lintegral_highStrip_height E hE H hH]
  exact mul_le_mul' le_rfl (parabolic_positive_spacing_tail g hg B hs hp q H hq hH)

#print axioms parabolic_positive_wide_spacing_tail

end QuantitativeMaass
