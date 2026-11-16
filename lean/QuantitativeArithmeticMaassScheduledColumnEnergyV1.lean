module

public import QuantitativeArithmeticMaassColumnEnergyExponentialV1
public import QuantitativeArithmeticMaassScheduledCylinderNewtonV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The chosen propagation both resolves the window and is smaller than
strongScale. These are consequences of the window hypothesis. -/
theorem radius_resolves_window (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,radius ε t≤Strong.strongScale t ∧ 1/radius ε t≤ε t := by
  obtain ⟨hp,hresolve⟩ := propagation_limits slowScale ε
    (slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)))
    (hε.mono (fun _ h => h.1)) hproduct
  filter_upwards [radius_eventually_eq ε hε hproduct,
    hp.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hresolve.eventually (eventually_ge_atTop (1:ℝ)),
    slowScale_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with t hr hp he hL
  have hLp : 0<slowScale t := by linarith
  have hRL : radius ε t≤slowScale t := by
    rw [hr]
    exact (div_le_one hLp).mp hp.le
  constructor
  · change _≤(slowScale t)^2
    nlinarith
  · apply (div_le_iff₀ (radius_pos ε t)).mpr
    rw [hr]
    nlinarith only [he]

/-- Constants and exponential propagation costs are absorbed uniformly
on all center balls of radius at most H*strongScale. -/
theorem column_energy_cost_schedule (A B H : ℝ) (hA : 0<A) (_hB : 0<B)
    (_hH : 0≤H) (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,∀ L : ℝ,L≤H*Strong.strongScale t →
      B*Real.exp (A*(radius ε t+L))≤
        Real.exp ((A*(H+1)+1)*Strong.strongScale t) := by
  filter_upwards [radius_resolves_window ε hε hproduct,
    (Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
      (eventually_ge_atTop B)] with t hr hBexp
  intro L hL
  have he : Real.exp (A*(radius ε t+L))≤
      Real.exp (A*(H+1)*Strong.strongScale t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hr.1]
  calc
    _ ≤ Real.exp (Strong.strongScale t)*Real.exp (A*(H+1)*Strong.strongScale t) :=
      mul_le_mul hBexp he (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

/-- The literal source columns on every ball in the scheduled center range
have energy at most t*epsilon times a fixed exponential in strongScale. -/
theorem source_column_energy_schedule (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (o : ℍ) (H : ℝ) (hH : 0≤H) (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ E : ℝ,0<E ∧ ∀ᶠ t in atTop,∀ L : ℝ,0≤L → L≤H*Strong.strongScale t →
      (∫ z in Metric.closedBall o L,‖column K hc he ε t z‖^2)≤
        (t*ε t)*Real.exp (E*Strong.strongScale t) := by
  obtain ⟨A,B,hA,hB,hbound⟩ := windowSourceColumn_exponential_energy K he hc hK hm o
  refine ⟨A*(H+1)+1,by positivity,?_⟩
  filter_upwards [radius_resolves_window ε hε hproduct,
    column_energy_cost_schedule A B H hA hB hH ε hε hproduct,
    hε,eventually_ge_atTop (1:ℝ)] with t hr hcost heps ht
  intro L hL hLH
  have hR : 1≤radius ε t := le_max_left _ _
  have hb := hbound L (radius ε t) t (ε t) hR hL ht heps.1.le heps.2 hr.2
    (supportRadius K hc*radius ε t)
    (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t)
  apply hb.trans
  calc
    _ = (t*ε t)*(B*Real.exp (A*(radius ε t+L))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hcost L hLH)
      (mul_nonneg (by
        have ht0 : 0≤t := by linarith
        positivity) heps.1.le)

/-- Actual residual columns with the same time-window center as the graph
leakage estimate. The factor t^3*epsilon cancels its spectral denominator. -/
def residualColumn (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) : ℍ→Lp ℂ 2 (quotientMeasure 0) :=
  cylinderTimeColumn (spectralResidualSchwartz t (time K hc ε t))
    (spectralResidualSchwartz_compact t (time K hc ε t) (time_compact K hc ε t))
    (spectralResidualSchwartz_even t (time K hc ε t) (time_even K hc he ε t))
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (spectralTimeResidual_support t (time K hc ε t) _ (time_support K hc ε t))

theorem residual_column_energy_schedule (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (o : ℍ) (H : ℝ) (hH : 0≤H) (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ E : ℝ,0<E ∧ ∀ᶠ t in atTop,∀ L : ℝ,0≤L → L≤H*Strong.strongScale t →
      (∫ z in Metric.closedBall o L,‖residualColumn K hc he ε t z‖^2)≤
        (t^3*ε t)*Real.exp (E*Strong.strongScale t) := by
  obtain ⟨A,B,hA,hB,hbound⟩ := windowResidualColumn_exponential_energy K he hc hK hm o
  refine ⟨A*(H+1)+1,by positivity,?_⟩
  filter_upwards [column_energy_cost_schedule A B H hA hB hH ε hε hproduct,
    hε,eventually_ge_atTop (1:ℝ)] with t hcost heps ht
  intro L hL hLH
  have hR : 1≤radius ε t := le_max_left _ _
  have hb := hbound L (radius ε t) t (ε t) hR hL ht heps.1.le heps.2
    (supportRadius K hc*radius ε t)
    (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t)
  apply hb.trans
  calc
    _ = (t^3*ε t)*(B*Real.exp (A*(radius ε t+L))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hcost L hLH)
      (mul_nonneg (by
        have ht0 : 0≤t := by linarith
        positivity) heps.1.le)

#print axioms radius_resolves_window
#print axioms column_energy_cost_schedule
#print axioms source_column_energy_schedule
#print axioms residual_column_energy_schedule
end QuantitativeMaass.Scheduled
