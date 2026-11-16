module

public import QuantitativeMaassMajorantTransferMassV1
public import QuantitativeMaassMajorantCollarEnergyV1
public import QuantitativeArithmeticMaassScheduledSmoothingTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- Sharp-to-smooth trace comparison for the literal normalized enlarged
majorant packet. The explicit collar margin is retained for canonical-cap
inversion; the comparison uses the actual majorant energy estimates. -/
theorem originalMajorant_sharp_smooth_cutoff_trace_limit_with_margin (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (N : ℕ) {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C) (W : ℝ)
    (T : ℝ→AutomorphicSpace N→L[ℂ]AutomorphicSpace N)
    (hT : ∀ᶠ t in atTop,‖T t‖≤1) :
    ∃ D : ℝ,0≤D ∧ W+3≤D ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (columnLinearTrace (quotientMeasure 0)
        (fun z => sharpCutoffTransfer N (movingLowerEdge δ C ε t) t (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))) (T t)-
       columnLinearTrace (quotientMeasure 0)
        (fun z => cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))) (T t)) /
          (t*ε t)) atTop (𝓝 0) := by
  let D := W+|W|+43
  have hD : 0≤D := by dsimp only [D]; linarith [neg_abs_le W]
  let V := W+|W|+40
  have henergy := originalMajorant_cutoffTransfer_energy K hc he hK hm ε hε hp hδ C hC
  have hcollar := originalMajorantCutoffCollar_energy_weighted_limit K hc he hK hm ε hε hp hδ C hC D V hD
    (by dsimp only [D,V]; ring_nf; exact le_rfl)
  have hsmall := (Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp Strong.strongScale_tendsto))
  have hlim := hsmall.add (hcollar.const_mul 2)
  simp only [mul_zero,zero_add] at hlim
  have hmargin : W+3≤D := by
    dsimp only [D]
    linarith [abs_nonneg W]
  refine ⟨D,hD,hmargin,?_⟩
  apply squeeze_zero_norm' _ hlim
  filter_upwards [henergy,hT,hε,eventually_gt_atTop (0:ℝ),movingMultiplicity_bound hδ C hC ε hε hp] with t henergy hT heps ht hmoving
  let a := movingLowerEdge δ C ε t
  have ha := movingLowerEdge_pos hδ C ε t
  let m := movingMultiplicity δ C ε t
  let η := Real.exp (-((|W|+23)*Strong.strongScale t))
  have hη : 0<η := Real.exp_pos _
  have hη1 : η≤1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg (by positivity) (sq_nonneg _)))
  let S := cutoffRectangle a t
  let hS := upperRectangle_compact 0 1 a (Real.exp (Strong.strongScale t/2)) ha
  let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
  let R := supportRadius K hc*radius ε t
  have hR : 0≤R := (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
  have hF := evenCoshLift_smoothOn f (f.smooth ⊤) (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t) (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)
  have hs := evenCoshLift_support_of_time_support f R hR (originalMajorant_support K hc ε t)
  let c := fun z => originalMajorantColumn K hc he ε t z
  let Ω := cutoffCollar a D t
  have hΩ : MeasurableSet Ω := hS.measurableSet.diff (upperRectangle_measurable _ _ _ _)
  have hΩS : Ω⊆S := sdiff_subset
  have hchange : ∀ᵐ z ∂volume.restrict S,
      ‖(1:ℂ)-upperFunction (cutoffSeed a D t ha).toFun z‖≤1 ∧
      (z∉Ω → (1:ℂ)=upperFunction (cutoffSeed a D t ha).toFun z) := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    change z∈upperRectangle 0 1 a (Real.exp (Strong.strongScale t/2)) at hz
    have hh := rectangleSmoothSeed_collar 0 1 a (Real.exp (Strong.strongScale t/2))
      (Real.exp (-(D*Strong.strongScale t))) ha (Real.exp_pos _) z
    dsimp only [cutoffSeed,Ω,cutoffCollar,cutoffRectangle]
    dsimp only at hh
    simpa only [zero_add,Set.indicator_of_mem hz] using hh
  have herr := transferred_column_collar_trace_error N (evenCoshLift f) hF R hR hs S hS
    a (Real.exp (Strong.strongScale t/2)) ha (fun _ hz => hz.2) m
    (by
      intro z Γ hΓ
      apply terminal_strip_overlap_bound N a ha z Γ
      intro g hg
      exact ⟨(hΓ g hg).1.1,(hΓ g hg).1.2,(hΓ g hg).2.1⟩)
    (fun _ => (1:ℂ)) (upperFunction (cutoffSeed a D t ha).toFun)
    aestronglyMeasurable_const (upperFunction_continuous (cutoffSeed a D t ha).smooth).aestronglyMeasurable
    1 1 1 (Eventually.of_forall (fun _ => by simp))
    (Eventually.of_forall (cutoffSeed_bound a D t ha)) Ω hΩ hchange (T t) η hη
  rw [boundedCrossQuotientLocalization_smooth N 0 S hS (cutoffSeed a D t ha)
    (fun z _ => cutoffSeed_bound a D t ha z),Measure.restrict_restrict hΩ,
    inter_eq_left.mpr hΩS] at herr
  simp only [one_pow,mul_one] at herr
  have hcolpos : 0≤∫ z in Ω,‖c z‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hmass := henergy N D
  have hbound := herr.trans (mul_le_mul_of_nonneg_right hT (by positivity))
  rw [one_mul] at hbound
  have hb := hbound.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmass hη.le) le_rfl)
  change |columnLinearTrace (quotientMeasure 0)
    (fun z => sharpCutoffTransfer N (movingLowerEdge δ C ε t) t (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))) (T t)-
    columnLinearTrace (quotientMeasure 0)
    (fun z => cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))) (T t)|≤
    η*(Real.exp (22*Strong.strongScale t)*(t*ε t))+(1+η⁻¹)*((m:ℝ)*(∫ z in Ω,‖c z‖^2)) at hb
  have hfirst : Real.exp (W*Strong.strongScale t)*η*Real.exp (22*Strong.strongScale t)≤
      Real.exp (-Strong.strongScale t) := by
    dsimp only [η]
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (le_abs_self W) (sq_nonneg (slowScale t))
    change W*Strong.strongScale t≤|W| *Strong.strongScale t at h
    linarith
  have hsecond : Real.exp (W*Strong.strongScale t)*(1+η⁻¹)*(m:ℝ)≤
      2*Real.exp (V*Strong.strongScale t) := by
    have hi : 1≤η⁻¹ := (one_le_inv₀ hη).mpr hη1
    calc
      _≤Real.exp (W*Strong.strongScale t)*(2*η⁻¹)*Real.exp (17*Strong.strongScale t) := by
        apply mul_le_mul _ hmoving (Nat.cast_nonneg _) (by positivity)
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith
      _=_ := by
        dsimp only [η,V]
        rw [Real.exp_neg,inv_inv,show (W+|W|+40)*Strong.strongScale t=
          W*Strong.strongScale t+((|W|+23)*Strong.strongScale t+17*Strong.strongScale t) by ring,
          Real.exp_add,Real.exp_add]
        ring
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (mul_pos ht heps.1)]
  calc
    _≤Real.exp (W*Strong.strongScale t)*(η*(Real.exp (22*Strong.strongScale t)*(t*ε t))+
      (1+η⁻¹)*((m:ℝ)*(∫ z in Ω,‖c z‖^2)))/(t*ε t) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)
        (mul_pos ht heps.1).le
    _≤(Real.exp (-Strong.strongScale t)*(t*ε t)+
      (2*Real.exp (V*Strong.strongScale t))*(∫ z in Ω,‖c z‖^2))/(t*ε t) := by
      apply div_le_div_of_nonneg_right _ (mul_pos ht heps.1).le
      calc
        _=(Real.exp (W*Strong.strongScale t)*η*Real.exp (22*Strong.strongScale t))*(t*ε t)+
          (Real.exp (W*Strong.strongScale t)*(1+η⁻¹)*(m:ℝ))*(∫ z in Ω,‖c z‖^2) := by ring
        _≤_ := add_le_add (mul_le_mul_of_nonneg_right hfirst (mul_pos ht heps.1).le)
          (mul_le_mul_of_nonneg_right hsecond hcolpos)
    _=(Real.exp ∘ Neg.neg ∘ Strong.strongScale) t+
      2*(Real.exp (V*Strong.strongScale t)*(∫ z in Ω,‖c z‖^2)/(t*ε t)) := by
      simp only [Function.comp_apply]
      field_simp [ht.ne',heps.1.ne']

/-- The sharp-to-smooth comparison without the extra collar-margin output. -/
theorem originalMajorant_sharp_smooth_cutoff_trace_limit (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (N : ℕ) {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C) (W : ℝ)
    (T : ℝ→AutomorphicSpace N→L[ℂ]AutomorphicSpace N)
    (hT : ∀ᶠ t in atTop,‖T t‖≤1) :
    ∃ D : ℝ,0≤D ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (columnLinearTrace (quotientMeasure 0)
        (fun z => sharpCutoffTransfer N (movingLowerEdge δ C ε t) t (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))) (T t)-
       columnLinearTrace (quotientMeasure 0)
        (fun z => cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))) (T t)) /
          (t*ε t)) atTop (𝓝 0) := by
  obtain ⟨D,hD,_,hlim⟩ := originalMajorant_sharp_smooth_cutoff_trace_limit_with_margin
    K hc he hK hm ε hε hp N hδ C hC W T hT
  exact ⟨D,hD,hlim⟩

#print axioms originalMajorant_sharp_smooth_cutoff_trace_limit_with_margin
#print axioms originalMajorant_sharp_smooth_cutoff_trace_limit
end QuantitativeMaass.Scheduled
