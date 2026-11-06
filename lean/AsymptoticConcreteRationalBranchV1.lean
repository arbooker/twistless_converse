module

public import AsymptoticRationalBranchTraceLimitV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticConcreteRationalBranch

open UpperHalfPlane MeasureTheory Filter Set ContinuousLinearMap
open AsymptoticUnweightedKernel AsymptoticStripCoordinates
open scoped Topology

noncomputable def operator (g : AsymptoticRationalGroup.Group) (a : ℍ → ℂ)
    (hm : Measurable a) {C : ℝ} (ha : ∀ z,‖a z‖≤C) (m : ℕ) :
    AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  (AsymptoticL2Multiplier.operator a hm.aestronglyMeasurable (Eventually.of_forall ha)).comp
    (AsymptoticHyperbolicSlash.operator
      (AsymptoticRationalFreeness.realMatrix (AsymptoticSlashGauge.representative g)) (2*m))

theorem operator_coeFn (g : AsymptoticRationalGroup.Group) (a : ℍ → ℂ)
    (hm : Measurable a) {C : ℝ} (ha : ∀ z,‖a z‖≤C) (m : ℕ)
    (f : AsymptoticHyperbolicSlash.Space) :
    operator g a hm ha m f =ᵐ[volume]
      (fun z => a z*AsymptoticSlashGauge.phase g m z*f (g • z)) := by
  have hmul := AsymptoticL2Multiplier.operator_coeFn a hm.aestronglyMeasurable
    (Eventually.of_forall ha) (AsymptoticHyperbolicSlash.operator
      (AsymptoticRationalFreeness.realMatrix (AsymptoticSlashGauge.representative g)) (2*m) f)
  have hslash := AsymptoticHyperbolicSlash.operator_coeFn
    (AsymptoticRationalFreeness.realMatrix (AsymptoticSlashGauge.representative g)) (2*m) f
  filter_upwards [hmul,hslash] with z hz ht
  change AsymptoticL2Multiplier.operator a hm.aestronglyMeasurable
    (Eventually.of_forall ha) _ z=_
  apply hz.trans
  rw [ht,AsymptoticSlashGauge.representative_action]
  change a z*(AsymptoticSlashGauge.phase g m z*f (g • z))=_
  ring

theorem operator_norm_le (g : AsymptoticRationalGroup.Group) (a : ℍ → ℂ)
    (hm : Measurable a) {C : ℝ} (hC : 0≤C) (ha : ∀ z,‖a z‖≤C) (m : ℕ) :
    ‖operator g a hm ha m‖≤C := by
  apply (opNorm_comp_le _ _).trans
  have hb := AsymptoticL2Multiplier.operator_norm_le (μ := volume) a hm.aestronglyMeasurable
    hC (Eventually.of_forall ha)
  have hs := AsymptoticHyperbolicSlash.operator_norm_le
    (AsymptoticRationalFreeness.realMatrix (AsymptoticSlashGauge.representative g)) (2*m)
  simpa only [mul_one] using mul_le_mul hb hs (norm_nonneg _) hC

/-- The literal action on lifted modes follows from the concrete
multiplier and rational pullback; it is not an assumed trace identity. -/
theorem retained_operator_mode (g : AsymptoticRationalGroup.Group) (S : Set ℍ)
    (hS : MeasurableSet S) (hend : ∀ z∈S,g • z∈AsymptoticMassTransport.strip)
    (a : ℍ → ℂ) (hm : Measurable a) {C : ℝ} (hC : 0≤C) (ha : ∀ z,‖a z‖≤C)
    (h n : ℕ) {ε : ℝ} (hε : 0<ε) :
    operator g (S.indicator a) (hm.indicator hS) (indicator_coefficient_bound S a hC ha)
      (h+1) (liftedMode h n hε) =ᵐ[volume] S.indicator
        (fun z => (a z*AsymptoticSlashGauge.phase g (h+1) z)*(g • z).im*
          unitRepresentative (2*h) 0 n ε (cylinder (g • z))) := by
  have hp := (AsymptoticRationalGroup.measurePreserving g).quasiMeasurePreserving.ae
    (liftedMode_coeFn h n hε)
  filter_upwards [operator_coeFn g (S.indicator a) (hm.indicator hS)
    (indicator_coefficient_bound S a hC ha) (h+1) (liftedMode h n hε),hp] with z hz hf
  rw [hz,hf]
  classical
  by_cases hs : z∈S
  · rw [indicator_of_mem hs,indicator_of_mem hs,indicator_of_mem (hend z hs)]
    ring
  · rw [indicator_of_notMem hs,indicator_of_notMem hs,zero_mul,zero_mul]

theorem retained_operator_trace_tendsto {ε Y H C : ℝ}
    (hε : 0<ε) (hY : 0<Y) (hC : 0≤C) (g : AsymptoticRationalGroup.Group)
    (S : Set ℍ) (hS : MeasurableSet S) (hstrip : S⊆AsymptoticMassTransport.strip)
    [IsFiniteMeasure ((volume : Measure ℍ).restrict S)]
    (a : ℍ → ℂ) (hm : Measurable a) (ha : ∀ z,‖a z‖≤C)
    (hend : ∀ z∈S,g • z∈AsymptoticMassTransport.strip)
    (hregion : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      Y≤(g • z).im ∧ Y≤z.im ∧ (g • z).im≤H ∧ z.im≤H) :
    Tendsto (fun h => liftedTrace h hε
      (operator g (S.indicator a) (hm.indicator hS) (indicator_coefficient_bound S a hC ha) (h+1))/(2*h+2:ℕ))
      atTop (𝓝 (AsymptoticRegularTrace.signedTrace volume
        (AsymptoticOrbitBranch.operator g (S.indicator a) hC (indicator_coefficient_bound S a hC ha))/(4*Real.pi))) := by
  apply rational_branch_trace_tendsto hε hY hC g _ S hS hstrip a hm ha _ hregion
    (fun h n => retained_operator_mode g S hS hend a hm hC ha h n hε)
  exact (ae_restrict_mem hS).mono (fun z hz => hend z hz)

#print axioms operator_coeFn
#print axioms operator_norm_le
#print axioms retained_operator_mode
#print axioms retained_operator_trace_tendsto

end AsymptoticConcreteRationalBranch
