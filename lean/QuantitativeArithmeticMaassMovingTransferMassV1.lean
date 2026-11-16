module

public import QuantitativeArithmeticMaassMovingCollarEnergyV1
public import QuantitativeArithmeticMaassSharpTransferMassV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

theorem movingLowerEdge_inv_bound {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,(movingLowerEdge δ C ε t)⁻¹≤Real.exp (4*Strong.strongScale t) := by
  filter_upwards [propagated_rectangle_size hδ C hC ε hε hp] with t ht
  change (2+(Real.exp (Strong.strongScale t))^2)/movingLowerEdge δ C ε t≤_ at ht
  apply le_trans _ ht
  rw [←one_div]
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (Real.exp (Strong.strongScale t))])
    (movingLowerEdge_pos hδ C ε t).le

def movingMultiplicity (δ C : ℝ) (ε : ℝ→ℝ) (t : ℝ) : ℕ :=
  (2*⌈3/movingLowerEdge δ C ε t⌉₊+1)^4+3

/-- Only the lower height enters this multiplicity estimate. -/
theorem movingMultiplicity_bound {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,(movingMultiplicity δ C ε t:ℝ)≤Real.exp (17*Strong.strongScale t) := by
  filter_upwards [movingLowerEdge_inv_bound hδ C hC ε hε hp,
    (Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
      (eventually_ge_atTop ((9:ℝ)^4+3))] with t hi he
  change (9:ℝ)^4+3≤Real.exp (Strong.strongScale t) at he
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  have h1 : 1≤Real.exp (4*Strong.strongScale t) := Real.one_le_exp (by positivity)
  have hceil := Nat.ceil_lt_add_one
    (show 0≤3/movingLowerEdge δ C ε t by exact div_nonneg (by norm_num) (movingLowerEdge_pos hδ C ε t).le)
  have hi3 : 3/movingLowerEdge δ C ε t≤3*Real.exp (4*Strong.strongScale t) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hi (by norm_num)
  have hh : 2*(⌈3/movingLowerEdge δ C ε t⌉₊:ℝ)+1≤9*Real.exp (4*Strong.strongScale t) := by linarith
  have he4 : 1≤(Real.exp (4*Strong.strongScale t))^4 := one_le_pow₀ h1
  calc
    _=(2*(⌈3/movingLowerEdge δ C ε t⌉₊:ℝ)+1)^4+3 := by norm_num [movingMultiplicity]
    _≤(9*Real.exp (4*Strong.strongScale t))^4+3 := by
      exact add_le_add (pow_le_pow_left₀ (by positivity) hh 4) le_rfl
    _≤((9:ℝ)^4+3)*(Real.exp (4*Strong.strongScale t))^4 := by
      rw [mul_pow]
      nlinarith
    _≤Real.exp (Strong.strongScale t)*(Real.exp (4*Strong.strongScale t))^4 :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _=_ := by
      rw [←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      norm_num
      ring

/-- Actual global smooth-transfer mass with the moving lower edge. This
bound is uniform in the level and in the collar width. -/
theorem movingCutoffTransfer_energy (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ t in atTop,∀ (N : ℕ) (D : ℝ),
      (∫ z,‖cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
        (cylinderAutomorphic (column K hc he ε t z))‖^2 ∂quotientMeasure 0)≤
          Real.exp (22*Strong.strongScale t)*(t*ε t) := by
  obtain ⟨B,hB,hbound⟩ := sharp_rectangle_source_mass_uniform K hc he hK hm (1/2)
  filter_upwards [hbound ε hε hp,movingMultiplicity_bound hδ C hC ε hε hp,
    movingLowerEdge_inv_bound hδ C hC ε hε hp,
    (Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually (eventually_ge_atTop B),
    hε,eventually_gt_atTop (0:ℝ)] with t ht hmultip hi hBsmall heps htpos
  intro N D
  let a := movingLowerEdge δ C ε t
  have ha : 0<a := movingLowerEdge_pos hδ C ε t
  let S := cutoffRectangle a t
  let hS := upperRectangle_compact 0 1 a (Real.exp (Strong.strongScale t/2)) ha
  let u := cutoffSeed a D t ha
  let m := movingMultiplicity δ C ε t
  have hv : ∀ᵐ z ∂volume.restrict S,‖upperFunction u.toFun z‖≤1 :=
    Eventually.of_forall (cutoffSeed_bound a D t ha)
  have hmass := transferred_column_energy N (evenCoshLift (time K hc ε t))
    (evenCoshLift_smoothOn _ ((time K hc ε t).smooth ⊤) (time_even K hc he ε t) (time_compact K hc ε t))
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (evenCoshLift_support_of_time_support _ _ (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (time_support K hc ε t)) S hS a (Real.exp (Strong.strongScale t/2)) ha
    (fun _ hz => hz.2) m (by
      intro z Γ hΓ
      apply terminal_strip_overlap_bound N a ha z Γ
      intro g hg
      exact ⟨(hΓ g hg).1.1,(hΓ g hg).1.2,(hΓ g hg).2.1⟩)
    (upperFunction u.toFun) (upperFunction_continuous u.smooth).aestronglyMeasurable hv
  rw [boundedCrossQuotientLocalization_smooth N 0 S hS u (fun z _ => cutoffSeed_bound a D t ha z)] at hmass
  have hrect := ht a (Real.exp (Strong.strongScale t/2)) ha (Real.exp_pos _).le
    (le_of_eq (congrArg Real.exp (by ring)))
  change (∫ z in S,‖column K hc he ε t z‖^2)≤a⁻¹*B*(t*ε t) at hrect
  change (∫ z,‖cutoffTransfer N a D t ha (cylinderAutomorphic (column K hc he ε t z))‖^2
    ∂quotientMeasure 0)≤(m:ℝ)*(∫ z in S,‖column K hc he ε t z‖^2) at hmass
  apply hmass.trans
  calc
    _≤(m:ℝ)*(a⁻¹*B*(t*ε t)) := mul_le_mul_of_nonneg_left hrect (Nat.cast_nonneg _)
    _≤Real.exp (17*Strong.strongScale t)*(Real.exp (4*Strong.strongScale t)*
        Real.exp (Strong.strongScale t)*(t*ε t)) := by
      apply mul_le_mul hmultip _
        (mul_nonneg (mul_nonneg (inv_nonneg.mpr ha.le) hB.le) (mul_pos htpos heps.1).le) (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_right _ (mul_pos htpos heps.1).le
      exact mul_le_mul hi hBsmall hB.le (Real.exp_pos _).le
    _=_ := by
      rw [show (22:ℝ)*Strong.strongScale t=
        17*Strong.strongScale t+(4*Strong.strongScale t+Strong.strongScale t) by ring,
        Real.exp_add,Real.exp_add]
      ring

#print axioms movingLowerEdge_inv_bound
#print axioms movingMultiplicity_bound
#print axioms movingCutoffTransfer_energy
end QuantitativeMaass.Scheduled
