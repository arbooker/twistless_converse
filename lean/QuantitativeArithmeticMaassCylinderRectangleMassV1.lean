module

public import QuantitativeArithmeticMaassUniformStripOverlapV1
public import QuantitativeArithmeticMaassSourceColumnEnergyV1
public import QuantitativeMaassCylinderSharpTraceV1
public import QuantitativeMaassCylinderCenteringErrorV1
public import QuantitativeMaassCylinderRectangleMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology SchwartzMap ContDiff ENNReal FourierTransform
namespace QuantitativeMaass

theorem rectangle_measure_le_terminal (a b : ℝ) (ha : 0<a) :
    volume.restrict (upperRectangle 0 1 a b)≤
      volume.restrict (AsymptoticHyperbolicArea.closedTerminal a) := by
  apply Measure.restrict_mono_ae
  have hs := upperRectangle_ae_strip a b ha
  rw [ae_restrict_iff' (upperRectangle_measurable 0 1 a b)] at hs
  filter_upwards [hs] with z hz hzK
  exact ⟨hz hzK,hzK.2.1⟩

theorem rectangle_area_le_inverse (a b : ℝ) (ha : 0<a) :
    volume.real (upperRectangle 0 1 a b)≤a⁻¹ := by
  have hh := Measure.le_iff.mp (rectangle_measure_le_terminal a b ha) Set.univ MeasurableSet.univ
  simp only [Measure.restrict_apply_univ] at hh
  rw [AsymptoticHyperbolicArea.closed_terminal_area ha] at hh
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [Measure.real,ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)] using h

/-- Sharp positive-mode mass on a compact rectangle, with no dependence
on the upper height. -/
theorem cylinderCenteredTimeColumn_rectangle_energy (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f:ℝ→ℂ)) (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (a b : ℝ) (ha : 0<a) :
    (∫ z in upperRectangle 0 1 a b,‖cylinderCenteredTimeColumn f hc he R hR hs z‖^2)≤
      a⁻¹*‖abelProfile (evenCoshLift (timeConvolution f f)) 1‖ := by
  have hi : IntegrableOn (fun z => ‖cylinderCenteredTimeColumn f hc he R hR hs z‖^2)
      (upperRectangle 0 1 a b) :=
    ((cylinderCenteredTimeColumn_continuous f hc he R hR hs).norm.pow 2).continuousOn.integrableOn_compact
      (upperRectangle_compact 0 1 a b ha)
  have hb := (lintegral_mono' (f:=fun z => ENNReal.ofReal
    (‖cylinderCenteredTimeColumn f hc he R hR hs z‖^2))
    (rectangle_measure_le_terminal a b ha) le_rfl).trans
    (cylinderTimeColumn_centered_sharp_tail f hc he hr R hR hs a ha)
  have hb' := hb.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)))
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)),
    ←ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)] at hb'
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb'

/-- The uncentered rectangle mass has a sharp diagonal term, independent
of upper height, and a separate off-diagonal mean term. Only the smaller
mean term pays for the growing cusp cutoff. -/
theorem cylinderTimeColumn_rectangle_sharp_energy (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f:ℝ→ℂ)) (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b) (C : ℝ) (hC : 0≤C)
    (hdecay : ∀ d : ℝ,0<d →
      ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    (∫ z in upperRectangle 0 1 a b,‖cylinderTimeColumn f hc he R hR hs z‖^2)≤
      2*a⁻¹*‖abelProfile (evenCoshLift (timeConvolution f f)) 1‖+
      2*b*(C*(Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2)))*a⁻¹ := by
  let Ω := upperRectangle 0 1 a b
  let E := C*(Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2))
  let c := cylinderTimeColumn f hc he R hR hs
  let d := cylinderCenteredTimeColumn f hc he R hR hs
  have hΩ : IsCompact Ω := upperRectangle_compact 0 1 a b ha
  have hccont : Continuous c := cylinderAbelColumn_continuous _ _ R hR _
  have hdcont : Continuous d := cylinderCenteredTimeColumn_continuous f hc he R hR hs
  have hE : 0≤E := by dsimp only [E]; positivity
  have hi : IntegrableOn (fun z => ‖c z‖^2) Ω := (hccont.norm.pow 2).continuousOn.integrableOn_compact hΩ
  have hid : IntegrableOn (fun z => ‖d z‖^2) Ω := (hdcont.norm.pow 2).continuousOn.integrableOn_compact hΩ
  have hiconst : IntegrableOn (fun _z : ℍ => 2*b*E) Ω :=
    continuous_const.continuousOn.integrableOn_compact hΩ
  have hpoint : ∀ᵐ z ∂volume.restrict Ω,‖c z‖^2≤2*‖d z‖^2+2*b*E := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
    let m := ∫ x in Icc (0:ℝ) 1,c (x+ᵥz)
    have heq : c z=d z+m := by dsimp only [d,cylinderCenteredTimeColumn,m,c]; abel
    have hn := norm_add_le (d z) m
    rw [←heq] at hn
    have hm : ‖m‖^2≤b*E :=
      (cylinderTimeColumn_mean_energy_bound f hc he hr R hR hs C hC hdecay z).trans
        (mul_le_mul_of_nonneg_right hz.2.2 hE)
    nlinarith [sq_nonneg (‖d z‖-‖m‖),norm_nonneg (c z),norm_nonneg (d z),norm_nonneg m]
  have hmain := integral_mono_ae hi ((hid.const_mul 2).add hiconst) hpoint
  simp only [Pi.add_apply] at hmain
  rw [integral_add (hid.const_mul 2) hiconst,integral_const_mul,integral_const] at hmain
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hmain
  have hcenter := cylinderCenteredTimeColumn_rectangle_energy f hc he hr R hR hs a b ha
  have harea := mul_le_mul_of_nonneg_right (rectangle_area_le_inverse a b ha)
    (show 0≤2*b*E by positivity)
  change volume.real Ω*(2*b*E)≤a⁻¹*(2*b*E) at harea
  change (∫ z in Ω,‖d z‖^2)≤_ at hcenter
  change (∫ z in Ω,‖c z‖^2)≤_
  dsimp only [E] at hmain harea
  dsimp only [Measure.real] at harea
  nlinarith only [hmain,harea,hcenter]

#print axioms rectangle_measure_le_terminal
#print axioms rectangle_area_le_inverse
#print axioms cylinderCenteredTimeColumn_rectangle_energy
#print axioms cylinderTimeColumn_rectangle_sharp_energy
end QuantitativeMaass
