module

public import QuantitativeArithmeticMaassScheduledCollarEnergyV1
public import QuantitativeArithmeticMaassUniformStripOverlapV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The lower edge needed to invert the cap on a propagated region. -/
def movingLowerEdge (δ C : ℝ) (ε : ℝ→ℝ) (t : ℝ) : ℝ :=
  δ*Real.exp (-(C*radius ε t))

theorem movingLowerEdge_pos {δ : ℝ} (hδ : 0<δ) (C : ℝ) (ε : ℝ→ℝ) (t : ℝ) :
    0<movingLowerEdge δ C ε t := mul_pos hδ (Real.exp_pos _)

theorem movingLowerEdge_le {δ C : ℝ} (hδ : 0<δ) (hC : 0≤C)
    (ε : ℝ→ℝ) (t : ℝ) : movingLowerEdge δ C ε t≤δ := by
  have hh := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg hC (radius_pos ε t).le))
  simpa only [movingLowerEdge,mul_one] using mul_le_mul_of_nonneg_left hh hδ.le

/-- Boundary collars still have negligible area when the lower edge moves
exponentially with the propagation radius. -/
theorem movingCutoffCollar_area {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (D : ℝ) (hD : 0≤D) :
    ∀ᶠ t in atTop,volume.real (cutoffCollar (movingLowerEdge δ C ε t) D t)≤
      (4/δ^2)*Real.exp ((2-D)*Strong.strongScale t) := by
  have hheight := (Real.tendsto_exp_atTop.comp
    (Strong.strongScale_tendsto.atTop_div_const (by norm_num : (0:ℝ)<2))).eventually
    (eventually_ge_atTop (δ+1))
  filter_upwards [hheight,radius_mul_le_half_strong C hC ε hε hp] with t ht hr
  change δ+1≤Real.exp (Strong.strongScale t/2) at ht
  let a := movingLowerEdge δ C ε t
  have ha : 0<a := movingLowerEdge_pos hδ C ε t
  have had : a≤δ := movingLowerEdge_le hδ hC ε t
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  have hh : Real.exp (-(D*Strong.strongScale t))≤1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg hD hs))
  have hb : Real.exp (Strong.strongScale t/2)≤Real.exp (Strong.strongScale t) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 : 1≤Real.exp (Strong.strongScale t) := Real.one_le_exp hs
  have harea := upperRectangle_collar_area 0 1 a (Real.exp (Strong.strongScale t/2))
    (Real.exp (-(D*Strong.strongScale t))) (by norm_num) ha (Real.exp_pos _) (by linarith)
  simp only [zero_add,sub_zero] at harea
  change volume.real (cutoffCollar a D t)≤_ at harea
  calc
    _≤2*Real.exp (-(D*Strong.strongScale t))*(Real.exp (Strong.strongScale t/2)-a+1)/a^2 := harea
    _≤2*Real.exp (-(D*Strong.strongScale t))*(2*Real.exp (Strong.strongScale t))/a^2 := by
      gcongr
      linarith
    _=(4/δ^2)*Real.exp ((1-D)*Strong.strongScale t+2*(C*radius ε t)) := by
      dsimp only [a,movingLowerEdge]
      rw [Real.exp_add,show (1-D)*Strong.strongScale t=
        -(D*Strong.strongScale t)+Strong.strongScale t by ring,Real.exp_add,
        Real.exp_neg,show 2*(C*radius ε t)=C*radius ε t+C*radius ε t by ring,Real.exp_add]
      simp only [Real.exp_neg]
      field_simp
      ring
    _≤_ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (by nlinarith)

theorem movingCutoffCollar_area_weighted_limit {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (D W : ℝ) (hD : 0≤D) (hDW : W+3≤D) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      volume.real (cutoffCollar (movingLowerEdge δ C ε t) D t)) atTop (𝓝 0) := by
  have hlim := (Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp Strong.strongScale_tendsto)).const_mul (4/δ^2)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hlim
  filter_upwards [movingCutoffCollar_area hδ C hC ε hε hp D hD] with t ht
  calc
    _≤Real.exp (W*Strong.strongScale t)*((4/δ^2)*Real.exp ((2-D)*Strong.strongScale t)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _=(4/δ^2)*Real.exp ((W+2-D)*Strong.strongScale t) := by
      rw [show (W+2-D)*Strong.strongScale t=W*Strong.strongScale t+(2-D)*Strong.strongScale t by ring,
        Real.exp_add]
      ring
    _≤_ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      change (W+2-D)*Strong.strongScale t≤ -Strong.strongScale t
      have hs : 0≤Strong.strongScale t := sq_nonneg _
      nlinarith

/-- The actual moving collar has arbitrarily small normalized source
energy, not merely small area. -/
theorem movingCutoffCollar_energy_weighted_limit (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (D W : ℝ) (hD : 0≤D) (hDW : W+3≤D) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z in cutoffCollar (movingLowerEdge δ C ε t) D t,‖column K hc he ε t z‖^2)/(t*ε t))
        atTop (𝓝 0) := by
  apply source_subset_energy_weighted_limit K hc he hK hm ε hε hp
    (fun t => cutoffCollar (movingLowerEdge δ C ε t) D t) 4 W (by norm_num) _
    (movingCutoffCollar_area_weighted_limit hδ C hC ε hε hp D W hD hDW)
  filter_upwards [propagated_rectangle_size hδ C hC ε hε hp] with t ht
  have hball := rectangle_subset_ball_of_size (movingLowerEdge δ C ε t)
    (Real.exp (Strong.strongScale t)) (4*Strong.strongScale t)
    (movingLowerEdge_pos hδ C ε t) ht
  intro z hz
  apply hball
  refine ⟨hz.1.1,hz.1.2.1,hz.1.2.2.trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  linarith

#print axioms movingCutoffCollar_area
#print axioms movingCutoffCollar_area_weighted_limit
#print axioms movingCutoffCollar_energy_weighted_limit
end QuantitativeMaass.Scheduled
