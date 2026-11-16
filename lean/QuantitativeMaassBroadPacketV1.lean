module

public import QuantitativeMaassBroadTimeWeightV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem broadTimeBase_even : Function.Even broadTimeBase := by
  intro s
  change (timeConvolution broadTimeSeed broadTimeSeed (-s)).re=
    (timeConvolution broadTimeSeed broadTimeSeed s).re
  rw [timeConvolution_even broadTimeSeed broadTimeSeed broadTimeSeed_even broadTimeSeed_even]

theorem broadTimeWeight_even (L t : ℝ) : Function.Even (broadTimeWeight L t) := by
  intro s
  simp only [broadTimeWeight,normalizedCosineWeight,broadTimeDensity,mul_neg,
    Real.cos_neg]
  rw [broadTimeBase_even (L*s)]

theorem broadTimeWeight_real (L t s : ℝ) : star (broadTimeWeight L t s)=broadTimeWeight L t s := by
  simp only [broadTimeWeight,normalizedCosineWeight,Complex.star_def,Complex.conj_ofReal]

theorem broadTimeWaveWeight (L : ℝ) (hL : 0 < L) (t : ℝ) :
    Wave.ShiftedWaveWeight (broadTimeWeight L t) :=
  Wave.shiftedWaveWeight_of_support
    ((broadTimeWeight_smooth L t).continuous.integrable_of_hasCompactSupport
      (broadTimeWeight_compact L hL t))
    (le_of_lt (one_div_pos.mpr hL)) (broadTimeWeight_support L hL t)

/-- A concrete broad spectral packet on the full quotient, built by
strongly integrating the actual wave against the normalized smooth bump. -/
def broadQuotientPacket (N : ℕ) (L : ℝ) (hL : 0 < L) (t : ℝ) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  Wave.shiftedQuotientWavePacket N (broadTimeWeight L t) (broadTimeWaveWeight L hL t)

/-- The concrete packet has uniformly bounded operator norm when L
is bounded below. The exceptional-spectrum cost is explicit. -/
theorem broadQuotientPacket_norm (N : ℕ) (L : ℝ) (hL : 0 < L) (t : ℝ) :
    ‖broadQuotientPacket N L hL t‖ ≤ 2*Real.cosh ((1/L)/2) := by
  have hi : Integrable (broadTimeWeight L t) :=
    (broadTimeWeight_smooth L t).continuous.integrable_of_hasCompactSupport
      (broadTimeWeight_compact L hL t)
  apply (Wave.shiftedQuotientWavePacket_norm N _ (broadTimeWaveWeight L hL t)).trans
  calc
    _ ≤ ∫ s : ℝ, ‖broadTimeWeight L t s‖*Real.cosh ((1/L)/2) := by
      apply integral_mono (broadTimeWaveWeight L hL t).2 (hi.norm.mul_const _)
      intro s
      by_cases hs : broadTimeWeight L t s=0
      · simp only [hs,norm_zero,zero_mul,le_refl]
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have hab := abs_le.mpr (broadTimeWeight_support L hL t hs)
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_nonneg (by positivity : 0 ≤ |s|/2),
          abs_of_nonneg (by positivity : 0 ≤ (1/L)/2)]
        linarith
    _ = (∫ s : ℝ, ‖broadTimeWeight L t s‖)*Real.cosh ((1/L)/2) := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (broadTimeWeight_norm_integral_le L hL t)
      (Real.cosh_pos _).le

/-- Full-quotient approximation by the concrete packet. This gives the
`1/(t L)` gain needed to absorb a compact-cutoff graph residual without
enlarging the cutoff by the deep LV propagation radius. -/
theorem broadQuotientPacket_residual_norm (N : ℕ) (x d : AutomorphicSpace N)
    (t L : ℝ) (ht : 0 < t) (hL : 0 < L)
    (hgraph : FriedrichsGraph N x ((((t:ℂ)^2+1/4) • x)+d)) :
    ‖broadQuotientPacket N L hL t x-x‖ ≤
      (2*Real.cosh ((1/L)/2)/(t*L))*‖d‖ := by
  have hh := Wave.quotientWavePacket_residual_norm N x d t ht hgraph
    (broadTimeWeight L t) (broadTimeWeight_smooth L t).continuous
    (broadTimeWeight_compact L hL t) (1/L) (le_of_lt (one_div_pos.mpr hL))
    (broadTimeWeight_support L hL t) (broadTimeWeight_normalization L hL t)
  apply hh.trans
  calc
    _ ≤ 2*((1/L)*Real.cosh ((1/L)/2)*‖d‖/t) :=
      mul_le_mul_of_nonneg_right (broadTimeWeight_norm_integral_le L hL t) (by positivity)
    _ = _ := by ring

#print axioms broadTimeWeight_even
#print axioms broadTimeWeight_real
#print axioms broadQuotientPacket_norm
#print axioms broadQuotientPacket_residual_norm

end QuantitativeMaass
