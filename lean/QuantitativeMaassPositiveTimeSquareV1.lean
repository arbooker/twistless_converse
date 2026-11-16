module

public import QuantitativeMaassNormalizedCosineWeightV1
public import QuantitativeMaassPacketCompositionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap Convolution

namespace QuantitativeMaass

def positiveTimeSquare (f : SchwartzMap ℝ ℂ) (s : ℝ) : ℝ :=
  (timeConvolution f f s).re

/-- The convolution square of a real time weight is literally the real
convolution of its real values. -/
theorem positiveTimeSquare_coe (f : SchwartzMap ℝ ℂ)
    (hf : ∀ s, ((f s).re:ℂ)=f s) (s : ℝ) :
    ((positiveTimeSquare f s):ℂ)=timeConvolution f f s := by
  have he : timeConvolution f f s =
      ((∫ u : ℝ, (f u).re*(f (s-u)).re : ℝ):ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [timeConvolution,SchwartzMap.convolution_apply,convolution_def,
      ContinuousLinearMap.mul_apply']
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by
      dsimp only
      rw [Complex.ofReal_mul,hf,hf])
  unfold positiveTimeSquare
  rw [he,Complex.ofReal_re]

theorem positiveTimeSquare_nonneg (f : SchwartzMap ℝ ℂ)
    (hf : ∀ s, ((f s).re:ℂ)=f s) (hnonneg : ∀ s, 0 ≤ (f s).re) (s : ℝ) :
    0 ≤ positiveTimeSquare f s := by
  have he : positiveTimeSquare f s = ∫ u : ℝ, (f u).re*(f (s-u)).re := by
    apply Complex.ofReal_injective
    rw [positiveTimeSquare_coe f hf,← integral_complex_ofReal]
    simp only [timeConvolution,SchwartzMap.convolution_apply,convolution_def,
      ContinuousLinearMap.mul_apply']
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by
      dsimp only
      rw [Complex.ofReal_mul,hf,hf])
  rw [he]
  exact integral_nonneg (fun u => mul_nonneg (hnonneg u) (hnonneg (s-u)))

theorem positiveTimeSquare_continuous (f : SchwartzMap ℝ ℂ) :
    Continuous (positiveTimeSquare f) := Complex.continuous_re.comp (timeConvolution f f).continuous

theorem positiveTimeSquare_compact (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) : HasCompactSupport (positiveTimeSquare f) := by
  apply HasCompactSupport.intro (timeConvolution_compact f f hc hc)
  intro s hs
  simp only [positiveTimeSquare,image_eq_zero_of_notMem_tsupport hs,Complex.zero_re]

/-- A probability time weight has a probability convolution square. -/
theorem positiveTimeSquare_mass (f : SchwartzMap ℝ ℂ)
    (hf : ∀ s, ((f s).re:ℂ)=f s) (he : Function.Even f)
    (hmass : (∫ s : ℝ, f s)=1) :
    (∫ s : ℝ, positiveTimeSquare f s)=1 := by
  have h := cosinePacket_timeConvolution f f he he 0
  simp only [cosinePacket,mul_zero,Real.cos_zero,Complex.ofReal_one,mul_one,hmass] at h
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    _ = ∫ s : ℝ, timeConvolution f f s :=
      integral_congr_ae (Filter.Eventually.of_forall (positiveTimeSquare_coe f hf))
    _ = _ := h

/-- The real cosine transform of a real even convolution square is
nonnegative at every frequency. This supplies the normalization lower
bound rather than assuming it of the eventual broad packet. -/
theorem positiveTimeSquare_cosine_nonneg (f : SchwartzMap ℝ ℂ)
    (hf : ∀ s, ((f s).re:ℂ)=f s) (he : Function.Even f) (r : ℝ) :
    0 ≤ ∫ s : ℝ, positiveTimeSquare f s*Real.cos (r*s) := by
  have hreal : ((∫ s : ℝ, (f s).re*Real.cos (s*r) : ℝ):ℂ)=cosinePacket f r := by
    rw [← integral_complex_ofReal,cosinePacket]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by
      dsimp only
      rw [Complex.ofReal_mul,hf])
  have hcast : ((∫ s : ℝ, positiveTimeSquare f s*Real.cos (r*s) : ℝ):ℂ)=
      cosinePacket f r*cosinePacket f r := by
    rw [← cosinePacket_timeConvolution f f he he r,cosinePacket,← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by
      dsimp only
      rw [Complex.ofReal_mul,positiveTimeSquare_coe f hf,mul_comm r s])
  rw [← hreal,← Complex.ofReal_mul] at hcast
  have heq := Complex.ofReal_injective hcast
  rw [heq]
  exact mul_self_nonneg _

#print axioms positiveTimeSquare_coe
#print axioms positiveTimeSquare_nonneg
#print axioms positiveTimeSquare_mass
#print axioms positiveTimeSquare_cosine_nonneg

end QuantitativeMaass
