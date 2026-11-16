module

public import QuantitativeArithmeticMaassSubsetColumnEnergyV1
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
theorem source_subset_energy_weighted_limit (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (S : ℝ→Set ℍ) (H W : ℝ) (hH : 0≤H)
    (hsize : ∀ᶠ t in atTop,S t⊆Metric.closedBall I (H*Strong.strongScale t))
    (harea : Tendsto (fun t => Real.exp (W*Strong.strongScale t)*volume.real (S t)) atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z in S t,‖column K hc he ε t z‖^2)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,B,D,hA,hB,hD,hbound⟩ := windowSourceColumn_subset_energy K he hc hK hm I
  have hrem := Strong.compact_height_geometric_cost ε A (A*H+W) B
    (hε.mono (fun _ h => h.1)) hp
  have hlim := (harea.const_mul D).add hrem
  simp only [mul_zero,zero_add] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_pos ht heps.1).le
  · filter_upwards [hε,eventually_ge_atTop (1:ℝ),hsize,
      radius_resolves_window ε hε hp,radius_eventually_eq ε hε hp] with t heps ht hs hr hrad
    have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
    have hb := hbound (H*Strong.strongScale t) (radius ε t) t (ε t) (le_max_left _ _)
      (mul_nonneg hH (sq_nonneg _)) ht heps.1.le heps.2 hr.2
      (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (time_support K hc ε t) (S t) hs
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

/-- The actual boundary collar of the chosen smooth cutoff. -/
def cutoffCollar (δ D t : ℝ) : Set ℍ :=
  cutoffRectangle δ t \ upperRectangle (Real.exp (-(D*Strong.strongScale t)))
    (1-Real.exp (-(D*Strong.strongScale t)))
    (δ+Real.exp (-(D*Strong.strongScale t)))
    (Real.exp (Strong.strongScale t/2)-Real.exp (-(D*Strong.strongScale t)))

theorem cutoffCollar_area {δ : ℝ} (hδ : 0<δ) (D : ℝ) (hD : 0≤D) :
    ∀ᶠ t in atTop,volume.real (cutoffCollar δ D t)≤
      (4/δ^2)*Real.exp ((1-D)*Strong.strongScale t) := by
  have hheight := (Real.tendsto_exp_atTop.comp
    (Strong.strongScale_tendsto.atTop_div_const (by norm_num : (0:ℝ)<2))).eventually
    (eventually_ge_atTop (δ+1))
  filter_upwards [hheight] with t ht
  change δ+1≤Real.exp (Strong.strongScale t/2) at ht
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  have hh : Real.exp (-(D*Strong.strongScale t))≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hD hs))
  have hb : Real.exp (Strong.strongScale t/2)≤Real.exp (Strong.strongScale t) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 : 1≤Real.exp (Strong.strongScale t) := Real.one_le_exp hs
  have ha := upperRectangle_collar_area 0 1 δ (Real.exp (Strong.strongScale t/2))
    (Real.exp (-(D*Strong.strongScale t))) (by norm_num) hδ (Real.exp_pos _) (by linarith)
  simp only [zero_add,sub_zero] at ha
  change volume.real (cutoffCollar δ D t)≤_ at ha
  calc
    _≤2*Real.exp (-(D*Strong.strongScale t))*(Real.exp (Strong.strongScale t/2)-δ+1)/δ^2 := ha
    _≤2*Real.exp (-(D*Strong.strongScale t))*(2*Real.exp (Strong.strongScale t))/δ^2 := by
      gcongr
      linarith
    _=_ := by
      rw [show (1-D)*Strong.strongScale t=-(D*Strong.strongScale t)+Strong.strongScale t by ring,
        Real.exp_add]
      ring

theorem cutoffCollar_area_weighted_limit {δ : ℝ} (hδ : 0<δ) (D W : ℝ)
    (hD : 0≤D) (hDW : W+2≤D) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*volume.real (cutoffCollar δ D t))
      atTop (𝓝 0) := by
  have hlim := (Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp Strong.strongScale_tendsto)).const_mul (4/δ^2)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hlim
  filter_upwards [cutoffCollar_area hδ D hD] with t ht
  calc
    _≤Real.exp (W*Strong.strongScale t)*((4/δ^2)*Real.exp ((1-D)*Strong.strongScale t)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _=(4/δ^2)*Real.exp ((W+1-D)*Strong.strongScale t) := by
      rw [show (W+1-D)*Strong.strongScale t=W*Strong.strongScale t+(1-D)*Strong.strongScale t by ring,
        Real.exp_add]
      ring
    _≤_ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      change (W+1-D)*Strong.strongScale t≤ -Strong.strongScale t
      have hs : 0≤Strong.strongScale t := sq_nonneg _
      nlinarith

/-- The actual scheduled collar has arbitrarily small normalized packet
energy, after any prescribed fixed strong-scale exponential weight. -/
theorem cutoffCollar_energy_weighted_limit (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (D W : ℝ) (hD : 0≤D) (hDW : W+2≤D) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z in cutoffCollar δ D t,‖column K hc he ε t z‖^2)/(t*ε t)) atTop (𝓝 0) := by
  apply source_subset_energy_weighted_limit K hc he hK hm ε hε hp
    (cutoffCollar δ D) 4 W (by norm_num) _ (cutoffCollar_area_weighted_limit hδ D W hD hDW)
  filter_upwards [propagated_rectangle_size hδ 0 (by norm_num) ε hε hp] with t ht
  simp only [zero_mul,neg_zero,Real.exp_zero,mul_one] at ht
  have hball := rectangle_subset_ball_of_size δ (Real.exp (Strong.strongScale t))
    (4*Strong.strongScale t) hδ ht
  intro z hz
  apply hball
  refine ⟨hz.1.1,hz.1.2.1,hz.1.2.2.trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  linarith

#print axioms cutoffCollar_energy_weighted_limit

#print axioms source_subset_energy_weighted_limit
#print axioms cutoffCollar_area
#print axioms cutoffCollar_area_weighted_limit
end QuantitativeMaass.Scheduled
