module

public import AsymptoticConcreteBranchAlgebraV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticConcreteRationalBranch

open UpperHalfPlane MeasureTheory Filter ContinuousLinearMap
open AsymptoticHyperbolicSlash (Space)
open scoped ComplexConjugate

theorem operator_congr (g : AsymptoticRationalGroup.Group) (a b : ℍ → ℂ)
    (ham : Measurable a) (hbm : Measurable b) {C D : ℝ}
    (ha : ∀ z,‖a z‖≤C) (hb : ∀ z,‖b z‖≤D) (m : ℕ) (he : ∀ z,a z=b z) :
    operator g a ham ha m=operator g b hbm hb m := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_coeFn g a ham ha m f,operator_coeFn g b hbm hb m f] with z hz ht
  rw [hz,ht,he z]

theorem operator_unit_inverse (g : AsymptoticRationalGroup.Group) (m : ℕ) :
    (operator g (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m).comp
      (operator g⁻¹ (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m)=1 := by
  rw [operator_comp _ _ _ _ _ _ (norm_nonneg _) _ _,inv_mul_cancel]
  exact (operator_congr 1 _ (fun _ : ℍ => (1:ℂ)) _ measurable_const _
    (fun _ => le_refl ‖(1:ℂ)‖) m (fun _ => one_mul _)).trans (operator_identity m)

theorem operator_unit_adjoint (g : AsymptoticRationalGroup.Group) (m : ℕ) :
    (operator g (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m).adjoint=
      operator g⁻¹ (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m := by
  let U := operator g (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m
  let V := operator g⁻¹ (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m
  have hn : ∀ f : Space,‖U f‖=‖f‖ := by
    intro f
    dsimp only [U]
    rw [operator_unit_coefficient]
    exact AsymptoticHyperbolicSlash.operator_norm_map _ _ f
  have hu : U.adjoint.comp U=1 := (norm_map_iff_adjoint_comp_self U).mp hn
  have hv : U.comp V=1 := operator_unit_inverse g m
  change U.adjoint=V
  calc
    U.adjoint=U.adjoint.comp 1 := (comp_id U.adjoint).symm
    _ = U.adjoint.comp (U.comp V) := by rw [hv]
    _ = (U.adjoint.comp U).comp V := by rw [comp_assoc]
    _ = V := by rw [hu]; exact id_comp V

theorem adjoint_coefficient_measurable (g : AsymptoticRationalGroup.Group)
    (a : ℍ → ℂ) (hm : Measurable a) : Measurable (fun z => conj (a (g⁻¹ • z))) :=
  Complex.continuous_conj.measurable.comp
    (hm.comp (AsymptoticRationalBranches.action_continuous g⁻¹).measurable)

/-- Taking adjoints produces exactly the same inverse label and
conjugate pullback coefficient in both realizations. -/
theorem operator_adjoint (g : AsymptoticRationalGroup.Group) (a : ℍ → ℂ)
    (hm : Measurable a) {C : ℝ} (ha : ∀ z,‖a z‖≤C) (m : ℕ) :
    (operator g a hm ha m).adjoint=
      operator g⁻¹ (fun z => conj (a (g⁻¹ • z))) (adjoint_coefficient_measurable g a hm)
        (AsymptoticOrbitBranch.adjoint_coefficient_bound g a ha) m := by
  let U := operator g (fun _ : ℍ => (1:ℂ)) measurable_const (fun _ => le_refl ‖(1:ℂ)‖) m
  let M := AsymptoticL2Multiplier.operator (μ := volume) a hm.aestronglyMeasurable (Eventually.of_forall ha)
  have he : operator g a hm ha m=M.comp U := by
    dsimp only [M,U]
    rw [operator_unit_coefficient]
    rfl
  have hmconj : Measurable (fun z => conj (a z)) := Complex.continuous_conj.measurable.comp hm
  have hconj : ∀ z,‖conj (a z)‖≤C := fun z => by simpa only [RCLike.norm_conj] using ha z
  have hMa : M.adjoint=operator 1 (fun z => conj (a z)) hmconj hconj m := by
    rw [operator_one_label]
    exact AsymptoticL2Multiplier.operator_conj_adjoint a hm.aestronglyMeasurable (Eventually.of_forall ha)
  rw [he,adjoint_comp,hMa]
  dsimp only [U]
  rw [operator_unit_adjoint,operator_comp _ _ _ _ _ _ (norm_nonneg _) _ _,one_mul]
  apply operator_congr
  intro z
  exact one_mul _

#print axioms operator_congr
#print axioms operator_unit_inverse
#print axioms operator_unit_adjoint
#print axioms operator_adjoint

end AsymptoticConcreteRationalBranch
