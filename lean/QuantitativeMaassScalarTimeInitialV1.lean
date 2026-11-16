module

public import QuantitativeMaassAbelNormalizedTimeMassV1
public import QuantitativeMaassAbelCosineRepresentationV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Approximation at time zero for a continuous curve by the exact
cosh-normalized shrinking time tests. -/
theorem continuous_time_packet_initial {ι : Type*} (l : Filter ι)
    (φ : ι → ℝ → ℂ) (hw : ∀ i,Wave.ShiftedWaveWeight (φ i))
    (hi : ∀ i,Integrable (fun t => (Real.cosh (t/2):ℂ)*φ i t))
    (hm : ∀ i,(∫ t,(Real.cosh (t/2):ℂ)*φ i t)=1)
    (hn : ∀ i,(∫ t,‖φ i t‖*Real.cosh (|t|/2))≤1)
    (R : ι → ℝ) (hs : ∀ i,Function.support (φ i)⊆Icc (-R i) (R i))
    (hR : Tendsto R l (𝓝 0)) (v : ℝ → ℂ) (hv : Continuous v)
    (hiv : ∀ i,Integrable (fun t => φ i t*v t)) :
    Tendsto (fun i => ∫ t,φ i t*v t) l (𝓝 (v 0)) := by
  let e : ℝ → ℂ := fun t => v t-(Real.cosh (t/2):ℂ)*(v 0)
  have hc : Continuous e := hv.sub
    ((Complex.continuous_ofReal.comp (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul continuous_const)
  have he0 : e 0=0 := by simp [e]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδe⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x:=0)) (ε/2) (by positivity)
  have hr := (tendsto_order.mp hR).2 δ hδ
  filter_upwards [hr] with i hri
  have heq : (∫ t,φ i t*v t)-v 0=∫ t,φ i t • e t := by
    have he (t : ℝ) : φ i t • e t=φ i t • v t-
        ((Real.cosh (t/2):ℂ)*φ i t) • v 0 := by
      simp only [e,smul_eq_mul]
      ring
    simp_rw [he]
    simp only [smul_eq_mul]
    rw [integral_sub (hiv i)
      ((hi i).mul_const (v 0)),integral_mul_const,hm i,one_mul]
  have hb : ‖∫ t,φ i t • e t‖≤(ε/2)*(∫ t,‖φ i t‖*Real.cosh (|t|/2)) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le ((hw i).2.const_mul (ε/2))
    filter_upwards with t
    by_cases ht : φ i t=0
    · simp [ht]
    · have hab := abs_le.mpr (hs i ht)
      have hdist : dist t 0<δ := by simpa only [Real.dist_eq,sub_zero] using hab.trans_lt hri
      have he : ‖e t‖≤ε/2 := by simpa only [he0,dist_zero_right] using (hδe hdist).le
      rw [norm_smul]
      have hh := Real.one_le_cosh (|t|/2)
      calc
        _ ≤ ‖φ i t‖*(ε/2) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
        _ ≤ (ε/2)*(‖φ i t‖*Real.cosh (|t|/2)) := by
          have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg (φ i t)) (by positivity : 0≤ε/2))
          nlinarith only [hmul]
  rw [dist_eq_norm,heq]
  exact lt_of_le_of_lt (hb.trans (by nlinarith [hn i])) (by linarith : ε/2<ε)

#print axioms continuous_time_packet_initial

theorem normalizedContinuousCurve_initial {ι : Type*} (l : Filter ι)
    (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    (v : ℝ → ℂ) (hv : Continuous v) :
    Tendsto (fun i => (2:ℂ)*(∫ t in Ioi (0:ℝ),
      coshTimeTest (abelNormalizedTest (R i)) t*v t)) l (𝓝 (v 0)) := by
  let w : ℝ → ℂ := fun t => v |t|
  have hw : Continuous w := hv.comp continuous_abs
  have ht := continuous_time_packet_initial l
    (fun i => coshTimeTest (abelNormalizedTest (R i)))
    (fun i => coshTimeTest_waveWeight _ (abelNormalizedTest_smooth (R i))
      (R i) (hR i).le (abelNormalizedTest_support (R i) (hR i)))
    (fun i => coshWeightedTest_integrable _ (abelNormalizedTest_smooth (R i))
      (R i) (hR i).le (abelNormalizedTest_support (R i) (hR i)))
    (fun i => abelNormalizedTest_time_mass (R i) (hR i))
    (fun i => (abelNormalizedTest_time_norm_mass (R i) (hR i)).le)
    R (fun i => coshTimeTest_support _ (R i) (hR i).le
      (abelNormalizedTest_support (R i) (hR i))) hlim w hw
    (fun i => coshCurve_integrable _ (abelNormalizedTest_smooth (R i))
      (R i) (hR i).le (abelNormalizedTest_support (R i) (hR i)) w hw)
  change Tendsto _ l (𝓝 (v |0|)) at ht
  rw [abs_zero] at ht
  apply ht.congr'
  filter_upwards with i
  have he := integral_even_eq_two_half
    (fun t => coshTimeTest (abelNormalizedTest (R i)) t*w t)
    (coshCurve_integrable _ (abelNormalizedTest_smooth (R i))
      (R i) (hR i).le (abelNormalizedTest_support (R i) (hR i)) w hw)
    (fun t => by simp only [coshTimeTest,Real.cosh_neg,w,abs_neg])
  rw [he]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show w t=v t from congrArg v (abs_of_pos ht)]

#print axioms normalizedContinuousCurve_initial

end QuantitativeMaass
