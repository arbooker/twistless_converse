module

public import QuantitativeArithmeticMaassMovingTransferMassV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

theorem movingCutoff_overlap (N : ℕ) {δ : ℝ} (hδ : 0<δ) (C : ℝ)
    (ε : ℝ→ℝ) (t : ℝ) (z : ℍ) (S : Finset (gamma N))
    (hS : ∀ g∈S,g•z∈cutoffRectangle (movingLowerEdge δ C ε t) t) :
    S.card≤movingMultiplicity δ C ε t := by
  apply terminal_strip_overlap_bound N _ (movingLowerEdge_pos hδ C ε t) z S
  intro g hg
  exact ⟨(hS g hg).1.1,(hS g hg).1.2,(hS g hg).2.1⟩

theorem movingCutoffTransfer_norm_sq (N : ℕ) {δ : ℝ} (hδ : 0<δ) (C D : ℝ)
    (ε : ℝ→ℝ) (t : ℝ) :
    ‖cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)‖^2≤
      (movingMultiplicity δ C ε t:ℝ)^2 := by
  let a := movingLowerEdge δ C ε t
  have ha := movingLowerEdge_pos hδ C ε t
  have hn := crossQuotientLocalization_norm_le_of_overlap N 0 (cutoffRectangle a t)
    (upperRectangle_compact 0 1 a _ ha) (cutoffSeed a D t ha)
    (movingMultiplicity δ C ε t) (movingMultiplicity δ C ε t)
    (movingCutoff_overlap N hδ C ε t) (movingCutoff_overlap 0 hδ C ε t) 1 (by norm_num)
    (fun z _ => cutoffSeed_bound a D t ha z)
  rw [mul_one,←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)] at hn
  exact pow_le_pow_left₀ (norm_nonneg (cutoffTransfer N a D t ha)) hn 2

/-- The vertical gradient bound does not deteriorate when the lower edge
moves; only the upper height and the smoothing width enter. -/
theorem movingCutoffSeed_gradient {δ : ℝ} (hδ : 0<δ) (C D : ℝ) (ε : ℝ→ℝ) :
    ∀ᶠ t in atTop,∀ z∈cutoffRectangle (movingLowerEdge δ C ε t) t,
      (upperEnergy (cutoffSeed (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)).toFun
        (cutoffSeed (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)).toFun z).re≤
          (Real.exp ((D+2)*Strong.strongScale t))^2 := by
  obtain ⟨B,hB,hderiv⟩ := smoothTransition_deriv_bounded
  filter_upwards [(Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
    (eventually_ge_atTop (4*B))] with t ht
  intro z hz
  have hg := rectangleSmoothSeed_gradient_quantitative B hB hderiv
    0 1 (movingLowerEdge δ C ε t) (Real.exp (Strong.strongScale t/2))
    (Real.exp (-(D*Strong.strongScale t))) (movingLowerEdge_pos hδ C ε t) (Real.exp_pos _) z hz
  apply hg.trans
  apply pow_le_pow_left₀ (by positivity)
  calc
    4*Real.exp (Strong.strongScale t/2)*B/Real.exp (-(D*Strong.strongScale t)) =
      (4*B)*Real.exp ((D+1/2)*Strong.strongScale t) := by
        rw [show (D+1/2)*Strong.strongScale t=Strong.strongScale t/2+D*Strong.strongScale t by ring,
          Real.exp_add,Real.exp_neg]
        field_simp
    _≤Real.exp (Strong.strongScale t)*Real.exp ((D+1/2)*Strong.strongScale t) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _≤Real.exp ((D+2)*Strong.strongScale t) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hs : 0≤Strong.strongScale t := sq_nonneg _
      nlinarith

theorem movingCutoff_flux_coefficients (N : ℕ) {δ : ℝ} (hδ : 0<δ)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,
      let m := (movingMultiplicity δ C ε t:ℝ)
      let B := Real.exp ((D+2)*Strong.strongScale t)
      ‖cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)‖^2≤
        Real.exp ((2*D+40)*Strong.strongScale t) ∧
      (2*Real.sqrt m*|B| *Real.sqrt m)^2≤Real.exp ((2*D+40)*Strong.strongScale t) ∧
      (Real.sqrt m*1*Real.sqrt m)^2≤Real.exp ((2*D+40)*Strong.strongScale t) := by
  filter_upwards [movingMultiplicity_bound hδ C hC ε hε hp,
    (Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
      (eventually_ge_atTop (4:ℝ))] with t hm h4
  dsimp only
  change 4≤Real.exp (Strong.strongScale t) at h4
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  have hm2 : (movingMultiplicity δ C ε t:ℝ)^2≤Real.exp (34*Strong.strongScale t) := by
    calc
      _≤(Real.exp (17*Strong.strongScale t))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hm 2
      _=_ := by rw [pow_two,←Real.exp_add]; congr 1; ring
  have hsmall : Real.exp (34*Strong.strongScale t)≤Real.exp ((2*D+40)*Strong.strongScale t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hD hs]
  refine ⟨(movingCutoffTransfer_norm_sq N hδ C D ε t).trans (hm2.trans hsmall),?_,?_⟩
  · rw [abs_of_pos (Real.exp_pos _)]
    have hid : (2*Real.sqrt (movingMultiplicity δ C ε t:ℝ)*Real.exp ((D+2)*Strong.strongScale t)*
        Real.sqrt (movingMultiplicity δ C ε t:ℝ))^2=
        4*(movingMultiplicity δ C ε t:ℝ)^2*(Real.exp ((D+2)*Strong.strongScale t))^2 := by
      calc
        _=4*((Real.sqrt (movingMultiplicity δ C ε t:ℝ))^2)^2*
            (Real.exp ((D+2)*Strong.strongScale t))^2 := by ring
        _=_ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hid]
    calc
      _≤Real.exp (Strong.strongScale t)*Real.exp (34*Strong.strongScale t)*
          (Real.exp ((D+2)*Strong.strongScale t))^2 := by gcongr
      _=Real.exp ((2*D+39)*Strong.strongScale t) := by
        rw [pow_two,←Real.exp_add,←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      _≤_ := Real.exp_le_exp.mpr (by nlinarith)
  · rw [mul_one,←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
    exact hm2.trans hsmall

/-- Actual source and residual energies on the propagation enlargement
of a cutoff whose lower edge already depends on the propagation radius. -/
theorem movingCutoff_propagation_energy (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ E : ℝ,0<E ∧ ∀ᶠ t in atTop,
      let R := supportRadius K hc*radius ε t
      let Ω := upperRectangle 0 1 (movingLowerEdge δ C ε t*Real.exp (-R))
        (Real.exp (Strong.strongScale t/2)*Real.exp R)
      (∫ z in Ω,‖column K hc he ε t z‖^2)≤(t*ε t)*Real.exp (E*Strong.strongScale t) ∧
      (∫ z in Ω,‖residualColumn K hc he ε t z‖^2)≤(t^3*ε t)*Real.exp (E*Strong.strongScale t) := by
  apply rectangle_column_energy_schedule K hc he hK hm
    (fun t => movingLowerEdge δ C ε t*Real.exp (-(supportRadius K hc*radius ε t)))
    (fun t => Real.exp (Strong.strongScale t/2)*Real.exp (supportRadius K hc*radius ε t))
    (fun t => mul_pos (movingLowerEdge_pos hδ C ε t) (Real.exp_pos _)) 4 (by norm_num) _ ε hε hp
  filter_upwards [propagated_rectangle_size hδ (C+supportRadius K hc)
    (add_nonneg hC (supportRadius_pos K hc).le) ε hε hp,
    radius_mul_le_half_strong (supportRadius K hc) (supportRadius_pos K hc).le ε hε hp]
    with t hsize hr
  have hlo : movingLowerEdge δ C ε t*Real.exp (-(supportRadius K hc*radius ε t))=
      δ*Real.exp (-((C+supportRadius K hc)*radius ε t)) := by
    dsimp only [movingLowerEdge]
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  rw [hlo]
  have hb : Real.exp (Strong.strongScale t/2)*Real.exp (supportRadius K hc*radius ε t)≤
      Real.exp (Strong.strongScale t) := by
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  apply le_trans _ hsize
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact add_le_add le_rfl (pow_le_pow_left₀ (by positivity) hb 2)

#print axioms movingCutoffTransfer_norm_sq
#print axioms movingCutoffSeed_gradient
#print axioms movingCutoff_flux_coefficients
#print axioms movingCutoff_propagation_energy
end QuantitativeMaass.Scheduled
