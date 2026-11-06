module

public import AsymptoticConcreteBranchAdjointV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open scoped ComplexConjugate lp

/-- A single common rational branch datum for both realizations. Bounds
and coefficients are independent of weight and orbit root. -/
structure Branch where
  label : AsymptoticRationalGroup.Group
  coefficient : ℍ → ℂ
  measurable : Measurable coefficient
  bound : ℝ
  bound_nonneg : 0≤bound
  norm_le : ∀ z,‖coefficient z‖≤bound

noncomputable def holomorphic (b : Branch) (m : ℕ) :
    AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  AsymptoticConcreteRationalBranch.operator b.label b.coefficient b.measurable b.norm_le m

noncomputable abbrev RegularSpace := ℓ²(AsymptoticRationalGroup.Group,ℂ)

noncomputable def regular (b : Branch) (z : ℍ) :
    RegularSpace →L[ℂ] RegularSpace :=
  AsymptoticOrbitBranch.operator b.label b.coefficient b.bound_nonneg b.norm_le z

noncomputable def compose (b c : Branch) : Branch where
  label := c.label*b.label
  coefficient z := b.coefficient z*c.coefficient (b.label • z)
  measurable := AsymptoticConcreteRationalBranch.product_coefficient_measurable
    b.label b.coefficient c.coefficient b.measurable c.measurable
  bound := b.bound*c.bound
  bound_nonneg := mul_nonneg b.bound_nonneg c.bound_nonneg
  norm_le := AsymptoticOrbitBranch.product_coefficient_bound b.label b.coefficient c.coefficient
    b.bound_nonneg b.norm_le c.norm_le

noncomputable def adjoint (b : Branch) : Branch where
  label := b.label⁻¹
  coefficient z := conj (b.coefficient (b.label⁻¹ • z))
  measurable := AsymptoticConcreteRationalBranch.adjoint_coefficient_measurable b.label b.coefficient b.measurable
  bound := b.bound
  bound_nonneg := b.bound_nonneg
  norm_le := AsymptoticOrbitBranch.adjoint_coefficient_bound b.label b.coefficient b.norm_le

noncomputable def identity : Branch where
  label := 1
  coefficient _ := 1
  measurable := measurable_const
  bound := ‖(1:ℂ)‖
  bound_nonneg := norm_nonneg _
  norm_le _ := le_refl _

noncomputable def scale (a : ℂ) (b : Branch) : Branch where
  label := b.label
  coefficient z := a*b.coefficient z
  measurable := measurable_const.mul b.measurable
  bound := ‖a‖*b.bound
  bound_nonneg := mul_nonneg (norm_nonneg _) b.bound_nonneg
  norm_le z := by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (b.norm_le z) (norm_nonneg _)

theorem holomorphic_compose (b c : Branch) (m : ℕ) :
    holomorphic (compose b c) m=(holomorphic b m).comp (holomorphic c m) :=
  (AsymptoticConcreteRationalBranch.operator_comp b.label c.label b.coefficient c.coefficient
    b.measurable c.measurable b.bound_nonneg b.norm_le c.norm_le m).symm

theorem regular_compose (b c : Branch) (z : ℍ) :
    regular (compose b c) z=(regular b z).comp (regular c z) :=
  (AsymptoticOrbitBranch.operator_comp b.label c.label b.coefficient c.coefficient
    b.bound_nonneg c.bound_nonneg b.norm_le c.norm_le z).symm

theorem holomorphic_adjoint (b : Branch) (m : ℕ) :
    holomorphic (adjoint b) m=(holomorphic b m).adjoint :=
  (AsymptoticConcreteRationalBranch.operator_adjoint b.label b.coefficient b.measurable b.norm_le m).symm

theorem regular_adjoint (b : Branch) (z : ℍ) :
    regular (adjoint b) z=(regular b z).adjoint :=
  (AsymptoticOrbitBranch.operator_adjoint b.label b.coefficient b.bound_nonneg b.norm_le z).symm

theorem holomorphic_identity (m : ℕ) : holomorphic identity m=1 :=
  AsymptoticConcreteRationalBranch.operator_identity m

theorem regular_identity (z : ℍ) : regular identity z=1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext g
  change regular identity z f g=f g
  simp only [regular,identity,AsymptoticOrbitBranch.operator_apply,one_mul]

theorem holomorphic_scale (a : ℂ) (b : Branch) (m : ℕ) :
    holomorphic (scale a b) m=a • holomorphic b m := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [AsymptoticConcreteRationalBranch.operator_coeFn _ _ _ (scale a b).norm_le m f,
    AsymptoticConcreteRationalBranch.operator_coeFn _ _ _ b.norm_le m f,
    Lp.coeFn_smul a (holomorphic b m f)] with z hs hb hm
  change holomorphic (scale a b) m f z=(a • holomorphic b m f) z
  rw [hm]
  change holomorphic (scale a b) m f z=a*holomorphic b m f z
  change AsymptoticConcreteRationalBranch.operator _ _ _ (scale a b).norm_le m f z=_
  rw [hs]
  change (a*b.coefficient z)*AsymptoticSlashGauge.phase b.label m z*f (b.label • z)=
    a*AsymptoticConcreteRationalBranch.operator _ _ _ b.norm_le m f z
  rw [hb]
  ring

theorem regular_scale (a : ℂ) (b : Branch) (z : ℍ) :
    regular (scale a b) z=a • regular b z := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext g
  simp only [regular,scale,AsymptoticOrbitBranch.operator_apply,smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  ring

theorem holomorphic_norm_le (b : Branch) (m : ℕ) : ‖holomorphic b m‖≤b.bound :=
  AsymptoticConcreteRationalBranch.operator_norm_le b.label b.coefficient b.measurable b.bound_nonneg b.norm_le m

theorem regular_norm_le (b : Branch) (z : ℍ) : ‖regular b z‖≤b.bound :=
  AsymptoticOrbitBranch.operator_norm_le b.label b.coefficient b.bound_nonneg b.norm_le z

#print axioms holomorphic_compose
#print axioms regular_compose
#print axioms holomorphic_adjoint
#print axioms regular_adjoint
#print axioms holomorphic_identity
#print axioms regular_identity
#print axioms holomorphic_scale
#print axioms regular_scale
#print axioms holomorphic_norm_le
#print axioms regular_norm_le

end AsymptoticFiniteBranch
