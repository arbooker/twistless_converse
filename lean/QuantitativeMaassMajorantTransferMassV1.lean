module

public import QuantitativeMaassMajorantRectangleMassV1
public import QuantitativeArithmeticMaassMovingTransferMassV1
public import QuantitativeArithmeticMaassSharpTransferMassV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- Actual global smooth-transfer mass with the moving lower edge. This
bound is uniform in the level and in the collar width. -/
theorem originalMajorant_cutoffTransfer_energy (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ t in atTop,∀ (N : ℕ) (D : ℝ),
      (∫ z,‖cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
        (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))‖^2 ∂quotientMeasure 0)≤
          Real.exp (22*Strong.strongScale t)*(t*ε t) := by
  obtain ⟨B,hB,hbound⟩ := originalMajorant_rectangle_mass_uniform K hc he hK hm (1/2)
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
  have hmass := transferred_column_energy N (evenCoshLift (QuantitativeNinaMaass.originalWindowMajorant K hc ε t))
    (evenCoshLift_smoothOn _ ((QuantitativeNinaMaass.originalWindowMajorant K hc ε t).smooth ⊤) (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t) (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t))
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (evenCoshLift_support_of_time_support _ _ (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (originalMajorant_support K hc ε t)) S hS a (Real.exp (Strong.strongScale t/2)) ha
    (fun _ hz => hz.2) m (by
      intro z Γ hΓ
      apply terminal_strip_overlap_bound N a ha z Γ
      intro g hg
      exact ⟨(hΓ g hg).1.1,(hΓ g hg).1.2,(hΓ g hg).2.1⟩)
    (upperFunction u.toFun) (upperFunction_continuous u.smooth).aestronglyMeasurable hv
  rw [boundedCrossQuotientLocalization_smooth N 0 S hS u (fun z _ => cutoffSeed_bound a D t ha z)] at hmass
  have hrect := ht a (Real.exp (Strong.strongScale t/2)) ha (Real.exp_pos _).le
    (le_of_eq (congrArg Real.exp (by ring)))
  change (∫ z in S,‖originalMajorantColumn K hc he ε t z‖^2)≤a⁻¹*B*(t*ε t) at hrect
  change (∫ z,‖cutoffTransfer N a D t ha (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))‖^2
    ∂quotientMeasure 0)≤(m:ℝ)*(∫ z in S,‖originalMajorantColumn K hc he ε t z‖^2) at hmass
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

#print axioms originalMajorant_cutoffTransfer_energy
end QuantitativeMaass.Scheduled
