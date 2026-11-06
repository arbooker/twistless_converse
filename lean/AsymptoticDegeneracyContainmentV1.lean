module

public import AsymptoticDegeneracyGroupV1
public import AsymptoticIntegralMatricesV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceLabels

open Matrix AsymptoticIntegralSubgroup AsymptoticRationalGroup
open scoped MatrixGroups

theorem rationalGL_integral (p : ℕ) [Fact p.Prime] (A : SL(2,ℤ)) : rationalGL A∈integralGL p := by
  apply integer_matrix_integral p (rationalGL A) A.val (fun _ _ => rfl)
  change padicNorm p (A.val.map (fun z : ℤ => (z:ℚ))).det=1
  rw [← Int.cast_det,A.property,Int.cast_one,padicNorm.one]

theorem integralLabel_integral (p : ℕ) [Fact p.Prime] (A : SL(2,ℤ)) : integralLabel A∈integralGroup p :=
  ofMatrix_mem p (rationalGL A) (rationalGL_positive A) (rationalGL_integral p A)

theorem dilation_translation (p : ℕ) (hp : 0<p) (r : ℚ) :
    (dilationLabel p hp)⁻¹*translationLabel r*dilationLabel p hp=translationLabel (r/p) := by
  have hp' : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
  apply (mul_left_cancel (a:=dilationLabel p hp))
  simp only [← mul_assoc,mul_inv_cancel,one_mul]
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (AsymptoticMobiusFold.translation r)*rationalMap (dilationGL p hp)=
    rationalMap (dilationGL p hp)*rationalMap (AsymptoticMobiusFold.translation (r/p))
  rw [← map_mul,← map_mul]
  congr 1
  apply Units.ext
  change (AsymptoticMobiusFold.translation r).val*(dilationGL p hp).val=
    (dilationGL p hp).val*(AsymptoticMobiusFold.translation (r/p)).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationGL,AsymptoticMobiusFold.translation,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]
  field_simp

#print axioms rationalGL_integral
#print axioms integralLabel_integral
#print axioms dilation_translation

end AsymptoticCongruenceLabels

namespace AsymptoticCongruenceStrip

open AsymptoticCongruenceLabels AsymptoticIntegralSubgroup

theorem gamma_le_integralGroup (N p : ℕ) [Fact p.Prime] : gamma N ≤ integralGroup p := by
  rintro g ⟨A,_,rfl⟩
  exact integralLabel_integral p A

theorem fractional_translation_not_mem (N p : ℕ) [Fact p.Prime] :
    translationLabel (1/(p:ℚ))∉gamma N := by
  intro h
  have hi := gamma_le_integralGroup N p h
  exact translationLabel_fraction_not_mem p 1
    (by exact_mod_cast (Fact.out : p.Prime).not_dvd_one) (by simpa only [Int.cast_one] using hi)

theorem fractional_translation_mem_degeneracy (M p : ℕ) (hp : 0<p) :
    translationLabel (1/(p:ℚ))∈degeneracyGroup M p hp := by
  refine ⟨translationLabel (1:ℚ),?_,?_⟩
  · change translationLabel (1:ℚ)∈gamma M
    simpa only [Int.cast_one] using translation_mem M (1:ℤ)
  change (dilationLabel p hp)⁻¹*translationLabel 1*((dilationLabel p hp)⁻¹)⁻¹=translationLabel (1/(p:ℚ))
  rw [inv_inv,dilation_translation]

theorem degeneracyGroup_mono {M L p : ℕ} (hp : 0<p) (hLM : L∣M) :
    degeneracyGroup M p hp≤degeneracyGroup L p hp :=
  Subgroup.map_mono (gamma_le_of_dvd hLM)

theorem degeneracyGroup_relIndex (M L p : ℕ) (hp : 0<p) :
    (degeneracyGroup M p hp).relIndex (degeneracyGroup L p hp)=(gamma M).relIndex (gamma L) :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (dilationLabel p hp)⁻¹).injective

#print axioms gamma_le_integralGroup
#print axioms fractional_translation_not_mem
#print axioms fractional_translation_mem_degeneracy
#print axioms degeneracyGroup_mono
#print axioms degeneracyGroup_relIndex

end AsymptoticCongruenceStrip
