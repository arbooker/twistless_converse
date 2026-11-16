module

public import QuantitativeMaassMajorantResidualEnergyV1
public import QuantitativeArithmeticMaassMovingFluxBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- Both literal majorant energies on the full propagation enlargement,
with every geometric cost absorbed in a fixed strong-scale exponential. -/
theorem originalMajorant_moving_propagation_energy (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ E : ℝ,0<E ∧ ∀ᶠ t in atTop,
      let R := supportRadius K hc*radius ε t
      let Ω := upperRectangle 0 1 (movingLowerEdge δ C ε t*Real.exp (-R))
        (Real.exp (Strong.strongScale t/2)*Real.exp R)
      (∫ z in Ω,‖originalMajorantColumn K hc he ε t z‖^2)≤
        (t*ε t)*Real.exp (E*Strong.strongScale t) ∧
      (∫ z in Ω,‖originalMajorantResidualColumn K hc he ε t z‖^2)≤
        (t^3*ε t)*Real.exp (E*Strong.strongScale t) := by
  obtain ⟨B,hB,hsrc⟩ := originalMajorant_rectangle_mass_uniform K hc he hK hm 1
  obtain ⟨E,hE,hres⟩ := originalMajorant_residual_energy_schedule K hc he hK hm I 4
    (by norm_num) ε hε hp
  have hCU : 0≤C+supportRadius K hc := add_nonneg hC (supportRadius_pos K hc).le
  refine ⟨max 5 E,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  filter_upwards [hsrc ε hε hp,hres,
    propagated_rectangle_size hδ (C+supportRadius K hc) hCU ε hε hp,
    movingLowerEdge_inv_bound hδ (C+supportRadius K hc) hCU ε hε hp,
    radius_mul_le_half_strong (supportRadius K hc) (supportRadius_pos K hc).le ε hε hp,
    (Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually (eventually_ge_atTop B),
    hε,eventually_ge_atTop (1:ℝ)] with t hsrc hres hsize hinv hr hBexp heps ht
  let R := supportRadius K hc*radius ε t
  let a := movingLowerEdge δ C ε t*Real.exp (-R)
  let b := Real.exp (Strong.strongScale t/2)*Real.exp R
  have ha : 0<a := mul_pos (movingLowerEdge_pos hδ C ε t) (Real.exp_pos _)
  have hb : 0≤b := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  have ht0 : 0≤t := by linarith
  have hlo : a=movingLowerEdge δ (C+supportRadius K hc) ε t := by
    dsimp only [a,R,movingLowerEdge]
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  have hbexp : b≤Real.exp (Strong.strongScale t) := by
    dsimp only [b]
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hball : upperRectangle 0 1 a b⊆Metric.closedBall I (4*Strong.strongScale t) := by
    apply rectangle_subset_ball_of_size a b _ ha
    rw [hlo]
    apply le_trans _ hsize
    exact div_le_div_of_nonneg_right
      (add_le_add le_rfl (pow_le_pow_left₀ hb hbexp 2))
      (movingLowerEdge_pos hδ (C+supportRadius K hc) ε t).le
  have hinv' : a⁻¹≤Real.exp (4*Strong.strongScale t) := by simpa only [hlo] using hinv
  constructor
  · have hm := hsrc a b ha hb (by simpa only [one_mul] using hbexp)
    apply hm.trans
    calc
      _≤Real.exp (4*Strong.strongScale t)*Real.exp (Strong.strongScale t)*(t*ε t) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg ht0 heps.1.le)
        exact mul_le_mul hinv' hBexp hB.le (Real.exp_pos _).le
      _=(t*ε t)*Real.exp (5*Strong.strongScale t) := by
        rw [←Real.exp_add,show 4*Strong.strongScale t+Strong.strongScale t=5*Strong.strongScale t by ring]
        ring
      _≤_ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left 5 E) hs))
        (mul_nonneg ht0 heps.1.le)
  · let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
    have hmono := cylinderTimeColumn_energy_mono (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t))
      (spectralResidualSchwartz_even t f (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t))
      R (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (spectralTimeResidual_support t f R (originalMajorant_support K hc ε t)) _ I _ hball
    apply (hmono.trans (hres _ (by positivity) le_rfl)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right 5 E) hs))
      (mul_nonneg (pow_nonneg ht0 _) heps.1.le)

#print axioms originalMajorant_moving_propagation_energy
end QuantitativeMaass.Scheduled
