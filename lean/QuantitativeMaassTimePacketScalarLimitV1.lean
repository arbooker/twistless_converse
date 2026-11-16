module

public import QuantitativeMaassRadialShiftLimitV1
public import QuantitativeMaassMovingWindowsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The scalar cosine transform is controlled by the same weighted time
norm as the complete-cylinder wave operator. -/
theorem cosinePacket_sub_norm_le (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (r : ℝ) :
    ‖cosinePacket f r-cosinePacket g r‖≤
      ∫ s,‖f s-g s‖*Real.cosh (|s|/2) := by
  have hcos : Continuous (fun s : ℝ => (Real.cos (s*r):ℂ)) := by fun_prop
  have hiF : Integrable (fun s => f s*(Real.cos (s*r):ℂ)) :=
    (hf.mul hcos).integrable_of_hasCompactSupport hfc.mul_right
  have hiG : Integrable (fun s => g s*(Real.cos (s*r):ℂ)) :=
    (hg.mul hcos).integrable_of_hasCompactSupport hgc.mul_right
  have hi : Integrable (fun s => ‖f s-g s‖*Real.cosh (|s|/2)) :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport (hfc.sub hgc).norm.mul_right
  rw [cosinePacket,cosinePacket,←integral_sub hiF hiG]
  apply norm_integral_le_of_norm_le hi
  filter_upwards with s
  rw [←sub_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩).trans
    (Real.one_le_cosh _)) (norm_nonneg _)

/-- Smooth radial shifts recover the exact scalar multiplier at every real
spectral parameter, including zero. -/
theorem radialShiftTime_cosinePacket_tendsto {ι : Type*} (L : Filter ι) [L.IsCountablyGenerated]
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a L (𝓝 0)) (r : ℝ) :
    Tendsto (fun i => cosinePacket (radialShiftTime f (a i)) r) L (𝓝 (cosinePacket f r)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun i =>
    cosinePacket_sub_norm_le _ _ (radialShiftTime_smooth f hf he hc (a i) (ha i)).continuous
      hf.continuous (radialShiftTime_compact f R hR hs (a i) (ha i)) hc r)
    (radialShiftTime_weighted_limit L f hf he hc R hR hs a ha ha0)

#print axioms cosinePacket_sub_norm_le
#print axioms radialShiftTime_cosinePacket_tendsto

end QuantitativeMaass
