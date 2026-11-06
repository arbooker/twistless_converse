module

public import AsymptoticConcreteRationalBranchV1
public import AsymptoticComplexMultiplierAdjointV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticConcreteRationalBranch

open UpperHalfPlane MeasureTheory Filter Set ContinuousLinearMap
open AsymptoticHyperbolicSlash (Space)

theorem product_coefficient_measurable (g : AsymptoticRationalGroup.Group)
    (a b : ℍ → ℂ) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun z => a z*b (g • z)) :=
  ha.mul (hb.comp (AsymptoticRationalBranches.action_continuous g).measurable)

/-- Holomorphic branches have the same reversed label product and
coefficient multiplication as the regular counting branches. -/
theorem operator_comp (g j : AsymptoticRationalGroup.Group) (a b : ℍ → ℂ)
    (ham : Measurable a) (hbm : Measurable b) {C D : ℝ}
    (hC : 0≤C) (ha : ∀ z,‖a z‖≤C) (hb : ∀ z,‖b z‖≤D) (m : ℕ) :
    (operator g a ham ha m).comp (operator j b hbm hb m)=
      operator (j*g) (fun z => a z*b (g • z)) (product_coefficient_measurable g a b ham hbm)
        (AsymptoticOrbitBranch.product_coefficient_bound g a b hC ha hb) m := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hp := (AsymptoticRationalGroup.measurePreserving g).quasiMeasurePreserving.ae
    (operator_coeFn j b hbm hb m f)
  filter_upwards [operator_coeFn g a ham ha m (operator j b hbm hb m f),hp,
    operator_coeFn (j*g) (fun z => a z*b (g • z)) (product_coefficient_measurable g a b ham hbm)
      (AsymptoticOrbitBranch.product_coefficient_bound g a b hC ha hb) m f] with z h₁ h₂ h₃
  change operator g a ham ha m (operator j b hbm hb m f) z=_
  rw [h₁,h₂,h₃,AsymptoticSlashGauge.phase_mul,mul_smul]
  ring

theorem operator_identity (m : ℕ) :
    operator 1 (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m=1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_coeFn 1 (fun _ : ℍ => (1:ℂ)) measurable_const
    (fun _ => le_refl ‖(1:ℂ)‖) m f] with z hz
  change operator 1 (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m f z=f z
  simpa only [AsymptoticSlashGauge.phase_one,one_mul,one_smul] using hz

theorem operator_one_label (a : ℍ → ℂ) (hm : Measurable a) {C : ℝ}
    (ha : ∀ z,‖a z‖≤C) (m : ℕ) :
    operator 1 a hm ha m=AsymptoticL2Multiplier.operator a hm.aestronglyMeasurable (Eventually.of_forall ha) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_coeFn 1 a hm ha m f,
    AsymptoticL2Multiplier.operator_coeFn a hm.aestronglyMeasurable (Eventually.of_forall ha) f] with z hz ht
  rw [hz,ht,AsymptoticSlashGauge.phase_one,one_smul,mul_one]

theorem operator_unit_coefficient (g : AsymptoticRationalGroup.Group) (m : ℕ) :
    operator g (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m=
      AsymptoticHyperbolicSlash.operator
        (AsymptoticRationalFreeness.realMatrix (AsymptoticSlashGauge.representative g)) (2*m) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_coeFn g (fun _ : ℍ => (1:ℂ)) measurable_const
    (fun _ => le_refl ‖(1:ℂ)‖) m f,
    AsymptoticHyperbolicSlash.operator_coeFn
      (AsymptoticRationalFreeness.realMatrix (AsymptoticSlashGauge.representative g)) (2*m) f] with z hz ht
  rw [hz,ht,AsymptoticSlashGauge.representative_action,one_mul]
  rfl

#print axioms operator_comp
#print axioms operator_identity
#print axioms operator_one_label
#print axioms operator_unit_coefficient

end AsymptoticConcreteRationalBranch
