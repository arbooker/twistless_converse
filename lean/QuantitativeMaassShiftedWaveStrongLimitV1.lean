module

public import QuantitativeMaassShiftedWaveGeneratorCFCV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Dense-range convergence extends under an eventual uniform bound. -/
theorem tendsto_zero_of_dense_range_eventually {ι : Type*} {l : Filter ι}
    (A : H →L[ℂ] H) (hd : DenseRange A) (F : ι → H →L[ℂ] H)
    (hF : ∀ᶠ i in l, ‖F i‖≤7)
    (hlim : ∀ w, Tendsto (fun i => F i (A w)) l (𝓝 0)) (v : H) :
    Tendsto (fun i => F i v) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w,hw⟩ := hd.exists_dist_lt v (show 0<ε/14 by positivity)
  have he := Metric.tendsto_nhds.mp (hlim w) (ε/2) (by positivity)
  filter_upwards [he,hF] with i hi hFi
  rw [dist_zero_right] at hi ⊢
  rw [dist_eq_norm] at hw
  have hdecomp : F i v=F i (v-A w)+F i (A w) := by rw [← map_add,sub_add_cancel]
  rw [hdecomp]
  have hb := ((F i).le_opNorm (v-A w)).trans
    (mul_le_mul_of_nonneg_right hFi (norm_nonneg (v-A w)))
  exact (norm_add_le _ _).trans_lt (by linarith)

def shiftedOneResolventDifference (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  cfc (p := IsSelfAdjoint) (shiftedDampedSecondDifference t) A

theorem shiftedOneResolventDifference_formula (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (t : ℝ) :
    shiftedOneResolventDifference A t=(2/t^2 : ℝ) • (shiftedDampedOperator A t-A) := by
  unfold shiftedOneResolventDifference shiftedDampedSecondDifference shiftedDampedOperator
  rw [cfc_const_mul (2/t^2) (fun s => shiftedDampedCosine t s-s) A
      ((shiftedDampedCosine_continuous t).sub continuous_id).continuousOn,
    cfc_sub (shiftedDampedCosine t) (fun s : ℝ => s) A
      (shiftedDampedCosine_continuous t).continuousOn continuous_id.continuousOn,cfc_id' ℝ A hA]

theorem shiftedOneResolventDifference_norm_le (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) {t : ℝ} (ht : |t|≤1) : ‖shiftedOneResolventDifference A t‖≤4 := by
  apply norm_cfc_le (by norm_num)
  intro s hs
  have hb := positiveContraction_spectrum_bound A hp hn hs
  exact shiftedDampedSecondDifference_bound ht hb.1 hb.2

def shiftedOneResolventGeneratorError (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  shiftedOneResolventDifference A t+(1-(5/4 : ℝ) • A)

theorem shiftedOneResolventGeneratorError_norm_le (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) {t : ℝ} (ht : |t|≤1) : ‖shiftedOneResolventGeneratorError A t‖≤7 := by
  have h1 := shiftedOneResolventDifference_norm_le A hp hn ht
  have h2 := norm_sub_le (1 : H →L[ℂ] H) ((5/4 : ℝ) • A)
  have h3 : ‖(1 : H →L[ℂ] H)‖≤1 := ContinuousLinearMap.norm_id_le
  have h4 : ‖(5/4 : ℝ) • A‖≤5/4 := by
    calc
      _ ≤ ‖(5/4 : ℝ)‖*‖A‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 5/4 := by norm_num; linarith
  exact (norm_add_le _ _).trans (by linarith)

theorem shiftedOneResolventGeneratorError_mul (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (t : ℝ) :
    shiftedOneResolventGeneratorError A t*A=shiftedRangeGeneratorError A t := by
  have hg : shiftedRangeCosine A t*A=shiftedDampedOperator A t := by
    ext v
    exact shiftedRangeCosine_range A hA hd t v
  unfold shiftedOneResolventGeneratorError shiftedRangeGeneratorError
  rw [shiftedOneResolventDifference_formula A hA]
  simp only [add_mul,sub_mul,one_mul,smul_mul_assoc,hg]

theorem shiftedOneResolventGeneratorError_tendsto (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) (v : H) :
    Tendsto (fun t => shiftedOneResolventGeneratorError A t v) (𝓝[≠] 0) (𝓝 0) := by
  apply tendsto_zero_of_dense_range_eventually A hd _ _ _ v
  · exact eventually_abs_time_le_one.mono (fun _ ht =>
      shiftedOneResolventGeneratorError_norm_le A hp hn ht)
  · intro w
    have hc : Continuous (fun B : H →L[ℂ] H => B w) := continuous_id.clm_apply continuous_const
    have h := (hc.tendsto 0).comp (shiftedRangeGeneratorError_tendsto A hp hn hd)
    have h' : Tendsto (fun t => shiftedRangeGeneratorError A t w) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [zero_apply,Function.comp_def] using h
    apply h'.congr'
    filter_upwards with t
    exact congrArg (fun B : H →L[ℂ] H => B w)
      (shiftedOneResolventGeneratorError_mul A hp.isSelfAdjoint hd t).symm

#print axioms shiftedOneResolventGeneratorError_tendsto

end QuantitativeMaass.Wave
