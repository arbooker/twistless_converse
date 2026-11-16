module

public import QuantitativeMaassWaveGeneratorLimitV1
public import QuantitativeMaassWaveDifferenceBoundV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Uniformly bounded linear maps converging on a genuinely dense operator
range converge on every vector. -/
theorem tendsto_zero_of_dense_range {ι : Type*} {l : Filter ι}
    (A : H →L[ℂ] H) (hd : DenseRange A) (F : ι → H →L[ℂ] H)
    (hF : ∀ i, ‖F i‖≤3) (hlim : ∀ w, Tendsto (fun i => F i (A w)) l (𝓝 0)) (v : H) :
    Tendsto (fun i => F i v) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w,hw⟩ := hd.exists_dist_lt v (show 0<ε/6 by positivity)
  have he := Metric.tendsto_nhds.mp (hlim w) (ε/2) (by positivity)
  filter_upwards [he] with i hi
  rw [dist_zero_right] at hi ⊢
  rw [dist_eq_norm] at hw
  have hdecomp : F i v=F i (v-A w)+F i (A w) := by rw [← map_add,sub_add_cancel]
  rw [hdecomp]
  have hb := ((F i).le_opNorm (v-A w)).trans
    (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg (v-A w)))
  exact (norm_add_le _ _).trans_lt (by linarith)

def oneResolventDifference (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  cfc (p := IsSelfAdjoint) (dampedSecondDifference t) A

theorem oneResolventDifference_formula (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    oneResolventDifference A t=(2/t^2 : ℝ) • (dampedOperator A t-A) := by
  unfold oneResolventDifference dampedSecondDifference dampedOperator
  rw [cfc_const_mul (2/t^2) (fun s => dampedCosine t s-s) A
      ((dampedCosine_continuous t).sub continuous_id).continuousOn,
    cfc_sub (dampedCosine t) (fun s : ℝ => s) A
      (dampedCosine_continuous t).continuousOn continuous_id.continuousOn,cfc_id' ℝ A hA]

theorem oneResolventDifference_norm_le (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (t : ℝ) : ‖oneResolventDifference A t‖≤1 := by
  apply norm_cfc_le zero_le_one
  intro s hs
  have hb := positiveContraction_spectrum_bound A hp hn hs
  exact (dampedSecondDifference_bound t hb.1 hb.2).trans (by linarith)

def oneResolventGeneratorError (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  oneResolventDifference A t+(1-A)

theorem oneResolventGeneratorError_norm_le (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (t : ℝ) : ‖oneResolventGeneratorError A t‖≤3 := by
  have h1 := oneResolventDifference_norm_le A hp hn t
  have h2 := norm_sub_le (1 : H →L[ℂ] H) A
  have h3 : ‖(1 : H →L[ℂ] H)‖≤1 := ContinuousLinearMap.norm_id_le
  exact (norm_add_le _ _).trans (by linarith)

theorem oneResolventGeneratorError_mul (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (t : ℝ) :
    oneResolventGeneratorError A t*A=rangeGeneratorError A t := by
  have hg : rangeCosine A t*A=dampedOperator A t := by ext v; exact rangeCosine_range A hA hd t v
  unfold oneResolventGeneratorError rangeGeneratorError
  rw [oneResolventDifference_formula A hA]
  simp only [add_mul,sub_mul,one_mul,smul_mul_assoc,hg]

theorem oneResolventGeneratorError_tendsto (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) (v : H) :
    Tendsto (fun t => oneResolventGeneratorError A t v) (𝓝[≠] 0) (𝓝 0) := by
  apply tendsto_zero_of_dense_range A hd _ (oneResolventGeneratorError_norm_le A hp hn) _ v
  intro w
  have hc : Continuous (fun B : H →L[ℂ] H => B w) := continuous_id.clm_apply continuous_const
  have h := (hc.tendsto 0).comp (rangeGeneratorError_tendsto A hp hn hd)
  have h' : Tendsto (fun t => rangeGeneratorError A t w) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [zero_apply,Function.comp_def] using h
  apply h'.congr'
  filter_upwards with t
  exact congrArg (fun B : H →L[ℂ] H => B w) (oneResolventGeneratorError_mul A hp.isSelfAdjoint hd t).symm

#print axioms oneResolventGeneratorError_tendsto

end QuantitativeMaass.Wave
