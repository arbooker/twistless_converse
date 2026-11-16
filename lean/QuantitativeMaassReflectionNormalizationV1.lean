module

public import QuantitativeMaassReflectionLimitV1
public import AsymptoticOrbitDensityIndependenceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology MatrixGroups ENNReal

namespace QuantitativeMaass

/-- Conjugation by the genuine reflection, on integral determinant-one matrices. -/
def reflectedIntegralMatrix (A : SL(2,ℤ)) : SL(2,ℤ) :=
  ⟨!![A 0 0,-A 0 1;-A 1 0,A 1 1],by
    have h := A.property
    rw [Matrix.det_fin_two] at h ⊢
    simpa using h⟩

theorem reflectedIntegralMatrix_mem (N : ℕ) (A : SL(2,ℤ))
    (hA : A∈CongruenceSubgroup.Gamma0 N) :
    reflectedIntegralMatrix A∈CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
  change ((-A 1 0 : ℤ) : ZMod N)=0
  simpa only [Int.cast_neg,neg_eq_zero] using hA

theorem reflection_involutive (z : ℍ) : J•(J•z)=z := by
  rw [← mul_smul,← pow_two,J_sq,one_smul]

/-- The sign change on the off-diagonal entries implements J A J literally. -/
theorem reflectedIntegralMatrix_action (A : SL(2,ℤ)) (z : ℍ) :
    reflectedIntegralMatrix A•z=J•(A•(J•z)) := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply,coe_J_smul,coe_specialLinearGroup_apply,coe_J_smul]
  simp [reflectedIntegralMatrix]
  ring

/-- Reflection of the actual projective congruence element. -/
def reflectedCongruence (N : ℕ) (γ : gamma N) : gamma N :=
  ⟨integralLabel (reflectedIntegralMatrix (representative γ)),
    Subgroup.mem_map.mpr ⟨reflectedIntegralMatrix (representative γ),
      reflectedIntegralMatrix_mem N _ (representative_mem γ),rfl⟩⟩

theorem reflectedCongruence_action (N : ℕ) (γ : gamma N) (z : ℍ) :
    reflectedCongruence N γ•z=J•(γ•(J•z)) := by
  change integralLabel (reflectedIntegralMatrix (representative γ))•z=_
  rw [integralLabel_action,reflectedIntegralMatrix_action,← integralLabel_action,representative_label]
  rfl

theorem congruence_eq_of_action (N : ℕ) (γ δ : gamma N)
    (h : ∀ z : ℍ,γ•z=δ•z) : γ=δ := by
  apply Subtype.ext
  apply inv_mul_eq_one.mp
  apply QuantitativeHolomorphic.rational_label_eq_one_of_fixed
  intro z
  change (γ.val⁻¹*δ.val)•z=z
  rw [mul_smul]
  change γ.val⁻¹•(δ•z)=z
  rw [← h z]
  exact inv_smul_smul γ.val z

theorem reflectedCongruence_involutive (N : ℕ) : Function.Involutive (reflectedCongruence N) := by
  intro γ
  apply congruence_eq_of_action N
  intro z
  rw [reflectedCongruence_action,reflectedCongruence_action,reflection_involutive,reflection_involutive]

/-- Reflection permutes the projective congruence subgroup without duplicating
its two scalar integral representatives. -/
def reflectedCongruenceEquiv (N : ℕ) : gamma N ≃ gamma N :=
  (reflectedCongruence_involutive N).toPerm

/-- Reflection transports the actual quotient density to another normalized
orbit density. Pointwise invariance of the chosen density is not assumed. -/
theorem reflected_density_normalized (N : ℕ) (z : ℍ) :
    (∑' γ : gamma N,density N (J•(γ•z)))=1 := by
  have he := (reflectedCongruenceEquiv N).tsum_eq (fun γ : gamma N => density N (γ•(J•z)))
  have hx (γ : gamma N) : (reflectedCongruenceEquiv N γ)•(J•z)=J•(γ•z) := by
    change reflectedCongruence N γ•(J•z)=_
    rw [reflectedCongruence_action,reflection_involutive]
  simp_rw [hx] at he
  exact he.trans (density_orbit_sum N (J•z))

/-- Reflection preserves quotient integrals of invariant nonnegative measurable
functions, even though the chosen quotient density need not be reflection invariant. -/
theorem reflection_lintegral (N : ℕ) (f : ℍ → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ γ : gamma N,∀ z,f (γ•z)=f z) :
    (∫⁻ z,f (J•z) ∂quotientMeasure N)=∫⁻ z,f z ∂quotientMeasure N := by
  have hJ : MeasurePreserving (fun z : ℍ => J•z) volume volume := measurePreserving_smul J volume
  let σ : ℍ → ℝ≥0∞ := fun z => density N (J•z)
  have hσ : Measurable σ := (density_measurable N).comp hJ.measurable
  have hm := hJ.lintegral_comp (hf.mul hσ)
  have he : (∫⁻ z,f (J•z)*density N z)=∫⁻ z,f z*σ z := by
    simpa only [Function.comp_apply,Pi.mul_apply,σ,reflection_involutive] using hm
  have hi := AsymptoticOrbitDensity.lintegral_invariant_eq volume
    (fun γ : gamma N => AsymptoticRationalGroup.measurePreserving γ.val)
    (density N) σ (density_measurable N) hσ (density_orbit_sum N)
    (reflected_density_normalized N) f hf hinv
  calc
    _ = ∫⁻ z,f (J•z)*density N z := by
      simpa only [quotientMeasure,Function.comp_apply,Pi.mul_apply,mul_comm] using
        lintegral_withDensity_eq_lintegral_mul volume (density_measurable N) (hf.comp hJ.measurable)
    _ = ∫⁻ z,f z*σ z := he
    _ = ∫⁻ z,f z ∂volume.withDensity σ := by
      rw [lintegral_withDensity_eq_lintegral_mul volume hσ hf]
      simp only [Pi.mul_apply,mul_comm]
    _ = _ := hi.symm

#print axioms reflectedIntegralMatrix_mem
#print axioms reflection_involutive
#print axioms reflectedIntegralMatrix_action
#print axioms reflectedCongruence_action
#print axioms congruence_eq_of_action
#print axioms reflectedCongruence_involutive
#print axioms reflected_density_normalized
#print axioms reflection_lintegral

end QuantitativeMaass
