module

public import SmallLevelIntegratedSeriesV1
public import SmallLevelMellinEnvelopeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Filter Set Metric MeasureTheory FormalMultilinearSeries FinitenessPolynomialSeries
open scoped NNReal ENNReal Topology

def taylorCoeff (k : ℕ) (a : ℕ → ℂ) (β c y : ℝ) (n : ℕ) : ℂ :=
  (cauchyPowerSeries (deformed k a β c y) 0 (1/2)).coeff n

theorem taylorCoeff_continuous (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (β : ℝ) {c : ℝ} (hc : 0<c) (n : ℕ) :
    ContinuousOn (fun y : ℝ => taylorCoeff k a β c y n) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  simp only [Set.domRestrict_def,taylorCoeff,FormalMultilinearSeries.coeff,Pi.one_def,
    cauchyPowerSeries_apply,sub_zero,circleIntegral,smul_eq_mul]
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hquot : Continuous (fun p : (Ioi (0:ℝ))×ℝ => (1:ℂ)/circleMap 0 (1/2) p.2) := by
    fun_prop (disch := intro p; exact half_circle_ne_zero p.2)
  have hinv : Continuous (fun p : (Ioi (0:ℝ))×ℝ => (circleMap 0 (1/2) p.2)⁻¹) := by
    fun_prop (disch := intro p; exact half_circle_ne_zero p.2)
  have hd : Continuous (fun p : (Ioi (0:ℝ))×ℝ => deriv (circleMap 0 (1/2)) p.2) := by
    simp_rw [deriv_circleMap]
    fun_prop
  exact hd.mul ((hquot.pow n).mul (hinv.mul (deformed_circle_continuous k ha β hc)))

theorem taylorCoeff_bound (k : ℕ) (a : ℕ → ℂ) (β c y : ℝ) {D : ℝ}
    (hbound : ∀ u : ℂ, ‖u‖≤1/2 → ‖deformed k a β c y u‖≤D) (n : ℕ) :
    ‖taylorCoeff k a β c y n‖≤D*2^n := by
  apply le_trans _ (cauchy_coefficient_bound hbound n)
  have h := (cauchyPowerSeries (deformed k a β c y) 0 (1/2) n).le_opNorm (fun _ => 1)
  simpa only [taylorCoeff,FormalMultilinearSeries.coeff,Pi.one_def,norm_one,Finset.prod_const,
    Finset.card_fin,one_pow,mul_one] using h

theorem taylorCoeff_hasSum (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (β : ℝ) {c y : ℝ} (hc : 0<c) (hy : 0<y) {u : ℂ} (hu : ‖u‖<1/2) :
    HasSum (fun n => taylorCoeff k a β c y n*u^n) (deformed k a β c y u) := by
  have hd : DifferentiableOn ℂ (deformed k a β c y) (closedBall 0 (1/2)) := by
    intro z hz
    apply (deformed_analytic k ha β hc hy _).differentiableAt.differentiableWithinAt
    simpa only [mem_closedBall,dist_zero_right] using hz
  have hp := hd.hasFPowerSeriesOnBall (R := (1/2:ℝ≥0)) (by norm_num)
  have hu' : u∈Metric.eball (0:ℂ) ((1/2:ℝ≥0):ℝ≥0∞) := by
    rw [Metric.eball_coe]
    simpa only [mem_ball,dist_zero_right,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hu
  have h := hp.hasSum hu'
  simpa only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,
    apply_eq_pow_smul_coeff,smul_eq_mul,zero_add,mul_comm,taylorCoeff] using h

/-- The Mellin integral of the actual deformed Fourier family has the
power series obtained by integrating its Cauchy coefficients. -/
theorem deformed_mellin_series (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∀ β : ℝ, ∀ s : ℂ, (K:ℝ)<s.re →
      HasFPowerSeriesOnBall (fun u => mellin (fun y => deformed k a β c y u) s)
        (ofScalars ℂ (fun n => mellin (fun y => taylorCoeff k a β c y n) s))
        0 ((1/2:ℝ≥0):ℝ≥0∞) := by
  obtain ⟨K,D,E,κ,hD,hE,hκ,hbound⟩ := deformed_mellin_envelope k ha ha0 hc
  refine ⟨K,?_⟩
  intro β s hs
  have hweight : ContinuousOn (fun y : ℝ => (y:ℂ)^(s-1)) (Ioi 0) := by
    intro y hy
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hy))).continuousWithinAt
  have h := integrated_series (volume.restrict (Ioi (0:ℝ)))
    (fun n y => (y:ℂ)^(s-1)*taylorCoeff k a β c y n)
    (fun y u => (y:ℂ)^(s-1)*deformed k a β c y u)
    (fun y => ‖(y:ℂ)^(s-1)‖*mellinEnvelope K D E κ y)
    (mellinEnvelope_integrable K hD hE hκ hs)
    (fun n => (hweight.mul (taylorCoeff_continuous k ha β hc n)).aestronglyMeasurable measurableSet_Ioi)
    (fun n => ?_) (fun u hu => ?_)
  · simpa only [mellin,smul_eq_mul] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [norm_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (taylorCoeff_bound k a β c y (hbound β y hy) n) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simpa only [mul_assoc] using (taylorCoeff_hasSum k ha β hc hy hu).mul_left ((y:ℂ)^(s-1))

#print axioms taylorCoeff_continuous
#print axioms taylorCoeff_bound
#print axioms taylorCoeff_hasSum
#print axioms deformed_mellin_series
end SmallLevelTaylor
