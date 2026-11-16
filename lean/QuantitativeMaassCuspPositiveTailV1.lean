module

public import QuantitativeMaassCuspCenteredPositiveV1
public import QuantitativeMaassPositiveSpacingTailV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace MatrixGroups FourierTransform ENNReal

namespace QuantitativeMaass

theorem nonnegative_series_ofReal_le_tsum (f : ℕ→ℝ) (hf : ∀ n,0≤f n) :
    ENNReal.ofReal (∑' n,f n)≤∑' n,ENNReal.ofReal (f n) := by
  by_cases hs : Summable f
  · exact (ENNReal.ofReal_tsum_of_nonneg hf hs).le
  · rw [tsum_eq_zero_of_not_summable hs,ENNReal.ofReal_zero]
    exact bot_le

/-- The actual centered cusp column has an inverse-height tail in the
unit horizontal cusp parameter. The cusp width contributes separately
when this parameter integral is transported to hyperbolic area. -/
theorem cuspColumn_centered_positive_tail (N : ℕ) [NeZero N] (hN : 0<N)
    (c : ℍ→AutomorphicSpace N) (hc : Continuous c)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (g : ℝ→ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1))
    (hr : ∀ v,star (g v)=g v)
    (hp : ∀ ξ,0≤(𝓕 (parabolicLineProfile g 1) ξ).re)
    (hk : ∀ z w,inner ℂ (c z) (c w)=radialPoincareKernel N g w z)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (A : SL(2,ℤ)) (H : ℝ) (hH : 0<H) (hheight : R/2<Real.log H) :
    (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,
      ENNReal.ofReal (‖c (cuspLogPoint N A (Real.log z.im) z.re)-
        cuspColumnMean N c A (Real.log z.im)‖^2))≤
      ENNReal.ofReal (2*(Fintype.card (cuspAdmissibleResidues N A):ℝ))*
        (ENNReal.ofReal H⁻¹*ENNReal.ofReal (g 1).re) := by
  let D := ENNReal.ofReal (2*(Fintype.card (cuspAdmissibleResidues N A):ℝ))
  let E := fun z : ℍ => 2*ENNReal.ofReal (z.im/(N:ℝ))*(∑' n : ℕ,ENNReal.ofReal
    (𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(z.im/(N:ℝ)))).re)
  have ht := parabolic_positive_spacing_tail g hg (Real.cosh R) hs hp N H
    (Nat.cast_pos.mpr hN) hH
  calc
    _≤∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,D*E z := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (AsymptoticHyperbolicArea.closedTerminal_measurable H)] with z hz
      have hzH : H≤z.im := hz.2
      have hu : R/2<Real.log z.im := hheight.trans_le (Real.log_le_log hH hzH)
      have hb := cuspColumn_high_centered_positive N hN c hc hinv g hg hr hp hk R hR hs
        A (Real.log z.im) hu z.re
      rw [Real.exp_log z.im_pos] at hb
      apply (ENNReal.ofReal_le_ofReal hb).trans
      have hsum := nonnegative_series_ofReal_le_tsum
        (fun n : ℕ => (𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(z.im/(N:ℝ)))).re)
        (fun _ => hp _)
      have hcard : 0≤2*(Fintype.card (cuspAdmissibleResidues N A):ℝ) := by positivity
      have hy : 0≤z.im/(N:ℝ) := (div_pos z.im_pos (Nat.cast_pos.mpr hN)).le
      rw [ENNReal.ofReal_mul hcard,ENNReal.ofReal_mul (mul_nonneg (by norm_num) hy),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat]
      exact mul_le_mul' (by
        dsimp only [D]
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat]) (mul_le_mul' (by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat]) hsum)
    _=D*(∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,E z) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _≤_ := mul_le_mul' le_rfl ht

#print axioms nonnegative_series_ofReal_le_tsum
#print axioms cuspColumn_centered_positive_tail

end QuantitativeMaass
