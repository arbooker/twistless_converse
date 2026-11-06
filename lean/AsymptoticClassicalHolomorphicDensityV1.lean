module

public import AsymptoticClassicalPeterssonMeasureV1
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane MeasureTheory Filter Set
open AsymptoticMassTransport
open scoped Topology Manifold ENNReal NNReal

/-- Hyperbolic area is positive on every nonempty open subset of ℍ. -/
instance hyperbolic_openPos : Measure.IsOpenPosMeasure (volume : Measure ℍ) := by
  let μ : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let : Measure.IsOpenPosMeasure μ :=
    Measure.IsOpenPosMeasure.comap (volume : Measure ℂ) isOpenEmbedding_coe
  have hm : Measurable (fun z : ℍ =>
      (↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) : ℝ≥0∞)) := by
    have hc : Continuous (fun z : ℍ => (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) :=
      continuous_im.subtype_mk _
    have hn (z : ℍ) : (⟨z.im, z.im_pos.le⟩ : ℝ≥0) ≠ 0 := by
      intro he
      exact z.im_ne_zero (congrArg (fun x : ℝ≥0 => (x : ℝ)) he)
    have hd : Continuous (fun z : ℍ => (1 / NNReal.mk z.im z.im_pos.le : ℝ≥0)) :=
      (continuous_const : Continuous (fun _ : ℍ => (1 : ℝ≥0))).div₀ hc hn
    exact (hd.pow 2).measurable.coe_nnreal_ennreal
  have ha : μ ≪ (volume : Measure ℍ) := by
    rw [volume_def]
    apply withDensity_absolutelyContinuous' hm.aemeasurable
    apply Eventually.of_forall
    intro z
    have hz : (0 : ℝ≥0) < NNReal.mk z.im z.im_pos.le := z.im_pos
    exact ne_of_gt (by positivity)
  constructor
  intro U hU hne hzero
  exact hU.measure_ne_zero μ hne (ha hzero)

/-- A holomorphic function that vanishes almost everywhere for the
 quotient density vanishes identically, by positivity on an open strip. -/
theorem eq_zero_of_ae_quotient (N : ℕ) {f : ℍ → ℂ} (hf : MDiff f)
    (hz : f =ᵐ[quotientMeasure N] 0) : f = 0 := by
  let U : Set ℍ := {z | 0 < z.re ∧ z.re < 1}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re |>.inter
    (isOpen_lt continuous_re continuous_const)
  have ha : f =ᵐ[(volume : Measure ℍ).restrict U] 0 := by
    change ∀ᵐ z ∂(volume : Measure ℍ).restrict U, f z = 0
    rw [ae_restrict_iff' hU.measurableSet]
    filter_upwards [ae_strip_of_ae N hz] with z hz hu
    exact hz ⟨hu.1.le, hu.2⟩
  have he : EqOn f 0 U := Measure.eqOn_open_of_ae_eq ha hU
    hf.continuous.continuousOn continuous_zero.continuousOn
  let z₀ : ℍ := ⟨(1 / 2 : ℂ) + Complex.I, by norm_num⟩
  have hz₀ : z₀ ∈ U := by
    change 0 < ((1 / 2 : ℂ) + Complex.I).re ∧ ((1 / 2 : ℂ) + Complex.I).re < 1
    norm_num
  apply UpperHalfPlane.eq_zero_of_frequently hf (τ := z₀)
  apply Filter.Eventually.frequently
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [hU.mem_nhds hz₀] with z hz
  exact he hz

#print axioms hyperbolic_openPos
#print axioms eq_zero_of_ae_quotient

end AsymptoticClassicalPetersson
