module

public import QuantitativeMaassCuspPositiveTailV1
public import QuantitativeMaassCuspCenteredTailV1
public import QuantitativeMaassPositiveWideSpacingTailV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology ContDiff InnerProductSpace MatrixGroups FourierTransform ENNReal

namespace QuantitativeMaass

/-- The centered actual column has a sharp inverse-height tail in genuine
hyperbolic area on the full cusp strip. -/
theorem cuspColumn_centered_wide_positive_tail (N W : ℕ) [NeZero N] (hN : 0<N)
    (c : ℍ→AutomorphicSpace N) (hc : Continuous c)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (g : ℝ→ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1))
    (hr : ∀ v,star (g v)=g v)
    (hp : ∀ ξ,0≤(𝓕 (parabolicLineProfile g 1) ξ).re)
    (hk : ∀ z w,inner ℂ (c z) (c w)=radialPoincareKernel N g w z)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (A : SL(2,ℤ)) (H : ℝ) (hH : 0<H) (hheight : R/2<Real.log H) :
    (∫⁻ z in cuspTailSet W H,
      ENNReal.ofReal (‖c (cuspAction A z)-
        cuspColumnMean N c A (Real.log z.im)‖^2))≤
      ENNReal.ofReal (2*(Fintype.card (cuspAdmissibleResidues N A):ℝ))*
        ((W:ℝ≥0∞)*(ENNReal.ofReal H⁻¹*ENNReal.ofReal (g 1).re)) := by
  let D := ENNReal.ofReal (2*(Fintype.card (cuspAdmissibleResidues N A):ℝ))
  let E := fun z : ℍ => 2*ENNReal.ofReal (z.im/(N:ℝ))*(∑' n : ℕ,ENNReal.ofReal
    (𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(z.im/(N:ℝ)))).re)
  have ht := parabolic_positive_wide_spacing_tail W g hg (Real.cosh R) hs hp N H
    (Nat.cast_pos.mpr hN) hH
  calc
    _≤∫⁻ z in cuspTailSet W H,D*E z := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (cuspTailSet_measurable W H)] with z hz
      have hzH : H≤z.im := hz.2
      have hu : R/2<Real.log z.im := hheight.trans_le (Real.log_le_log hH hzH)
      have hb := cuspColumn_high_centered_positive N hN c hc hinv g hg hr hp hk R hR hs
        A (Real.log z.im) hu (z.re/(N:ℝ))
      rw [Real.exp_log z.im_pos,cuspLogPoint_recover N hN A z] at hb
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
    _=D*(∫⁻ z in cuspTailSet W H,E z) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _≤_ := mul_le_mul' le_rfl ht

#print axioms cuspColumn_centered_wide_positive_tail

end QuantitativeMaass
