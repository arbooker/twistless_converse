module

public import QuantitativeMaassEnlargedWindowBoundsV1
public import QuantitativeMaassMajorantColumnLinearV1
public import QuantitativeArithmeticMaassScheduledSharpMassV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The enlarged packet before its bounded scalar normalization. -/
def enlargedWindowColumn (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (t : ℝ) : ℍ→Lp ℂ 2 (quotientMeasure 0) :=
  let a := t-smoothingWidth (slowScale t) (ε t)
  let b := t+ε t+smoothingWidth (slowScale t) (ε t)
  let f := windowTimeSchwartz K hc (radius ε t) (radius_pos ε t) a b
  cylinderTimeColumn f (symmetricWindowTimeTest_compact K hc _ a b (radius_pos ε t))
    (symmetricWindowTimeTest_even K he _ a b) (supportRadius K hc*radius ε t)
    (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    ((symmetricWindowTimeTest_uniform_support K hc).choose_spec.2
      (radius ε t) (radius_pos ε t) a b)

/-- Enlarging the endpoints preserves the rectangle source-mass bound,
with the lower height as the only diagonal geometric loss. -/
theorem enlarged_rectangle_source_mass_uniform (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (H : ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ ε : ℝ→ℝ,
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,∀ a b : ℝ,0<a → 0≤b → b≤Real.exp (H*Strong.strongScale t) →
        (∫ z in upperRectangle 0 1 a b,‖enlargedWindowColumn K hc he ε t z‖^2)≤a⁻¹*B*(t*ε t) := by
  obtain ⟨C,hC,hdecay⟩ := enlargedWindowSquare_abel_decay K he hc
  obtain ⟨D,hD,hdiag⟩ := enlargedWindowIdentity_bound K he hc hK hm
  let U := supportRadius K hc
  have hU : 0<U := supportRadius_pos K hc
  let E := 24*Real.pi*C
  refine ⟨2*D+1,by positivity,?_⟩
  intro ε hε hp
  have hcost := Strong.compact_height_geometric_cost ε (2*U+2) H E
    (hε.mono (fun _ h => h.1)) hp
  filter_upwards [radius_resolves_window ε hε hp,radius_eventually_eq ε hε hp,
    hcost.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),hε,
    QuantitativeNinaMaass.originalWindowMajorant_parameters ε hε hp,
    eventually_ge_atTop (3:ℝ)] with t hresolve hrad hsmall heps hparam ht
  intro a b ha hb hsize
  have ht0 : 0<t := by linarith
  have hR : 1≤radius ε t := le_max_left _ _
  let u := t-smoothingWidth (slowScale t) (ε t)
  let v := t+ε t+smoothingWidth (slowScale t) (ε t)
  have hu : 0<u := hparam.2.2
  have huv : u≤v := by dsimp only [u,v]; linarith [hparam.1,heps.1]
  have hv : v≤2*t := by dsimp only [v]; linarith [hparam.2.1,heps.2]
  have hwidth : v-u≤2*ε t := by dsimp only [u,v]; linarith [hparam.2.1]
  have hu' : t-ε t≤u := by dsimp only [u]; linarith [hparam.2.1,heps.1]
  let f := windowTimeSchwartz K hc (radius ε t) (radius_pos ε t) u v
  have hfc := symmetricWindowTimeTest_compact K hc (radius ε t) u v (radius_pos ε t)
  have hfe := symmetricWindowTimeTest_even K he (radius ε t) u v
  have hs := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2
    (radius ε t) (radius_pos ε t) u v
  have hsource := cylinderTimeColumn_rectangle_sharp_energy f hfc hfe
    (symmetricWindowTimeTest_real K he (radius ε t) u v)
    (U*radius ε t) (mul_pos hU (radius_pos ε t)).le hs a b ha hb
    (C*Real.sqrt t*(radius ε t)^2*(ε t)^2) (by positivity)
    (fun d hd => hdecay (radius ε t) t (ε t) u v d hR ht heps.1.le heps.2 hu' huv hv hwidth hd)
  have hdiagonal : ‖abelProfile (evenCoshLift (timeConvolution f f)) 1‖≤D*t*ε t :=
    hdiag (radius ε t) t (ε t) u v hR (by linarith) heps.1.le heps.2 hresolve.2 hu huv hv hwidth
  have hmean := rectangle_mean_cost 1 b C U (radius ε t) t (ε t)
    (Strong.strongScale t) H (by norm_num) hb hC.le hU.le (radius_pos ε t).le heps.1.le heps.2 hsize
  have hsmall' : E*Real.sqrt t*Real.exp ((2*U+2)*radius ε t+H*Strong.strongScale t)≤t*ε t := by
    rw [Strong.log_compactCuspHeight,←hrad] at hsmall
    exact ((div_lt_one (mul_pos ht0 heps.1)).mp hsmall).le
  have hdiag' := mul_le_mul_of_nonneg_left hdiagonal (show 0≤2*a⁻¹ by positivity)
  change (∫ z in upperRectangle 0 1 a b,‖enlargedWindowColumn K hc he ε t z‖^2)≤_ at hsource
  dsimp only [E] at hsmall'
  norm_num only [inv_one,mul_one] at hmean
  have hm := mul_le_mul_of_nonneg_right (hmean.trans hsmall') (inv_nonneg.mpr ha.le)
  nlinarith only [hsource,hm,hdiag']

/-- The literal normalized majorant has the same uniform sharp energy
bound; its normalization costs at most four. -/
theorem originalMajorant_rectangle_mass_uniform (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (H : ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ ε : ℝ→ℝ,
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,∀ a b : ℝ,0<a → 0≤b → b≤Real.exp (H*Strong.strongScale t) →
        (∫ z in upperRectangle 0 1 a b,‖originalMajorantColumn K hc he ε t z‖^2)≤a⁻¹*B*(t*ε t) := by
  obtain ⟨B,hB,hbound⟩ := enlarged_rectangle_source_mass_uniform K hc he hK hm H
  refine ⟨4*B,by positivity,?_⟩
  intro ε hε hp
  filter_upwards [hbound ε hε hp] with t ht
  intro a b ha hb hsize
  have hc₁ : Continuous (originalMajorantColumn K hc he ε t) := by
    unfold originalMajorantColumn cylinderTimeColumn
    exact cylinderAbelColumn_continuous _ _ _ _ _
  have hc₂ : Continuous (enlargedWindowColumn K hc he ε t) := by
    unfold enlargedWindowColumn cylinderTimeColumn
    exact cylinderAbelColumn_continuous _ _ _ _ _
  have hi : IntegrableOn (fun z => ‖originalMajorantColumn K hc he ε t z‖^2)
      (upperRectangle 0 1 a b) := (hc₁.norm.pow 2).continuousOn.integrableOn_compact
    (upperRectangle_compact 0 1 a b ha)
  have hj : IntegrableOn (fun z => ‖enlargedWindowColumn K hc he ε t z‖^2)
      (upperRectangle 0 1 a b) := (hc₂.norm.pow 2).continuousOn.integrableOn_compact
    (upperRectangle_compact 0 1 a b ha)
  calc
    _≤∫ z in upperRectangle 0 1 a b,4*‖enlargedWindowColumn K hc he ε t z‖^2 :=
      integral_mono_ae hi (hj.const_mul 4) (Eventually.of_forall
        (fun z => originalMajorantColumn_norm_sq_le K hc he ε t z))
    _=4*(∫ z in upperRectangle 0 1 a b,‖enlargedWindowColumn K hc he ε t z‖^2) := integral_const_mul _ _
    _≤4*(a⁻¹*B*(t*ε t)) := mul_le_mul_of_nonneg_left (ht a b ha hb hsize) (by norm_num)
    _=_ := by ring

#print axioms enlarged_rectangle_source_mass_uniform
#print axioms originalMajorant_rectangle_mass_uniform
end QuantitativeMaass.Scheduled
