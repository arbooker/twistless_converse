module

public import QuantitativeMaassShiftedWaveGeneratorScalarV1
public import QuantitativeMaassShiftedWaveRangeV1
public import QuantitativeMaassWaveSpectrumV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def shiftedRangeGeneratorError (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  (2/t^2 : ℝ) • ((shiftedRangeCosine A t-1)*A*A)+(A-(5/4 : ℝ) • (A*A))

theorem shiftedRangeGeneratorError_cfc (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (t : ℝ) :
    shiftedRangeGeneratorError A t=cfc (shiftedWeightedRemainder t) A := by
  have hg : shiftedRangeCosine A t*A=cfc (shiftedDampedCosine t) A := by
    ext v
    exact shiftedRangeCosine_range A hA hd t v
  unfold shiftedWeightedRemainder
  rw [cfc_add (a := A) (fun s => (2/t^2)*(shiftedDampedCosine t s*s-s^2))
      (fun s => s-(5/4)*s^2)
      (continuous_const.mul (((shiftedDampedCosine_continuous t).mul continuous_id).sub
        (continuous_id.pow 2))).continuousOn
      (continuous_id.sub (continuous_const.mul (continuous_id.pow 2))).continuousOn,
    cfc_const_mul (2/t^2) (fun s => shiftedDampedCosine t s*s-s^2) A
      (((shiftedDampedCosine_continuous t).mul continuous_id).sub (continuous_id.pow 2)).continuousOn,
    cfc_sub (fun s => shiftedDampedCosine t s*s) (fun s : ℝ => s^2) A
      ((shiftedDampedCosine_continuous t).mul continuous_id).continuousOn (continuous_id.pow 2).continuousOn,
    cfc_sub (fun s : ℝ => s) (fun s : ℝ => (5/4)*s^2) A
      continuous_id.continuousOn (continuous_const.mul (continuous_id.pow 2)).continuousOn,
    cfc_const_mul (5/4) (fun s : ℝ => s^2) A (continuous_id.pow 2).continuousOn,
    cfc_mul (shiftedDampedCosine t) (fun s : ℝ => s) A
      (shiftedDampedCosine_continuous t).continuousOn continuous_id.continuousOn,
    cfc_id' ℝ A hA,cfc_pow_id A 2 hA,pow_two]
  unfold shiftedRangeGeneratorError
  rw [sub_mul,one_mul,sub_mul,hg]
  simp only [pow_two]

theorem shiftedRangeGeneratorError_norm_le (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) {t : ℝ} (ht : t≠0) (ht1 : |t|≤1) :
    ‖shiftedRangeGeneratorError A t‖≤6*t^2 := by
  rw [shiftedRangeGeneratorError_cfc A hp.isSelfAdjoint hd]
  apply norm_cfc_le (by positivity)
  intro s hs
  have hb := positiveContraction_spectrum_bound A hp hn hs
  exact shiftedWeightedRemainder_bound ht ht1 hb.1 hb.2

theorem eventually_abs_time_le_one : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t|≤1 := by
  have h : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), |t|<1 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with t ht
    change dist t 0 < 1 at ht
    simpa only [Real.dist_eq,sub_zero] using ht
  exact (h.filter_mono nhdsWithin_le_nhds).mono (fun _ ht => ht.le)

theorem shiftedRangeGeneratorError_tendsto (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) :
    Tendsto (shiftedRangeGeneratorError A) (𝓝[≠] 0) (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [self_mem_nhdsWithin,eventually_abs_time_le_one] with t ht ht1
    exact shiftedRangeGeneratorError_norm_le A hp hn hd ht ht1
  · have h : Continuous (fun t : ℝ => 6*t^2) := by fun_prop
    simpa using (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))

#print axioms shiftedRangeGeneratorError_cfc
#print axioms shiftedRangeGeneratorError_tendsto

end QuantitativeMaass.Wave
