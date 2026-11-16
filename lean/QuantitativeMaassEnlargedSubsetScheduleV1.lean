module

public import QuantitativeMaassEnlargedSubsetEnergyV1
public import QuantitativeMaassMajorantRectangleMassV1
public import QuantitativeArithmeticMaassScheduledCutoffGeometryV1
public import QuantitativeMaassCompactHeightScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- A geometric area estimate suffices for small energy on a moving subset;
the off-diagonal error is uniform on the enclosing strong-scale ball. -/
theorem enlarged_subset_energy_weighted_limit (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (S : ℝ→Set ℍ) (H W : ℝ) (hH : 0≤H)
    (hsize : ∀ᶠ t in atTop,S t⊆Metric.closedBall I (H*Strong.strongScale t))
    (harea : Tendsto (fun t => Real.exp (W*Strong.strongScale t)*volume.real (S t)) atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z in S t,‖enlargedWindowColumn K hc he ε t z‖^2)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,B,D,hA,hB,hD,hbound⟩ := enlargedWindowSourceColumn_subset_energy K he hc hK hm I
  have hrem := Strong.compact_height_geometric_cost ε A (A*H+W) B
    (hε.mono (fun _ h => h.1)) hp
  have hlim := (harea.const_mul D).add hrem
  simp only [mul_zero,zero_add] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_pos ht heps.1).le
  · filter_upwards [hε,eventually_ge_atTop (3:ℝ),hsize,
      radius_resolves_window ε hε hp,radius_eventually_eq ε hε hp,
      QuantitativeNinaMaass.originalWindowMajorant_parameters ε hε hp] with t heps ht hs hr hrad hparam
    have ht0 : 0<t := by linarith
    have hb := hbound (H*Strong.strongScale t) (radius ε t) t (ε t) (smoothingWidth (slowScale t) (ε t)) (le_max_left _ _)
      (mul_nonneg hH (sq_nonneg _)) ht heps.1.le heps.2 hr.2 hparam.1.le hparam.2.1
      (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      ((symmetricWindowTimeTest_uniform_support K hc).choose_spec.2 (radius ε t) (radius_pos ε t)
        (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))) (S t) hs
    have he2 : (ε t)^2≤1 := by nlinarith
    calc
      _≤Real.exp (W*Strong.strongScale t)*(volume.real (S t)*(D*t*ε t)+
        B*(Real.sqrt t*1)*Real.exp (A*(radius ε t+H*Strong.strongScale t)))/(t*ε t) := by
        apply div_le_div_of_nonneg_right _ (mul_pos ht0 heps.1).le
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply hb.trans
        gcongr
      _=D*(Real.exp (W*Strong.strongScale t)*volume.real (S t))+
        B*Real.sqrt t*Real.exp (A*propagation (slowScale t) (ε t)+
          (A*H+W)*Real.log (Strong.compactCuspHeight t))/(t*ε t) := by
        rw [Strong.log_compactCuspHeight,hrad]
        rw [show A*propagation (slowScale t) (ε t)+(A*H+W)*Strong.strongScale t=
          W*Strong.strongScale t+A*(propagation (slowScale t) (ε t)+H*Strong.strongScale t) by ring,
          Real.exp_add]
        field_simp [ht0.ne',heps.1.ne']

#print axioms enlarged_subset_energy_weighted_limit
end QuantitativeMaass.Scheduled
