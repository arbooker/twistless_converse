module

public import QuantitativeMaassMajorantSubsetScheduleV1
public import QuantitativeArithmeticMaassMovingCollarEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The actual moving collar has arbitrarily small normalized source
energy, not merely small area. -/
theorem originalMajorantCutoffCollar_energy_weighted_limit (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (D W : ℝ) (hD : 0≤D) (hDW : W+3≤D) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z in cutoffCollar (movingLowerEdge δ C ε t) D t,‖originalMajorantColumn K hc he ε t z‖^2)/(t*ε t))
        atTop (𝓝 0) := by
  apply originalMajorant_subset_energy_weighted_limit K hc he hK hm ε hε hp
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

#print axioms originalMajorantCutoffCollar_energy_weighted_limit
end QuantitativeMaass.Scheduled
