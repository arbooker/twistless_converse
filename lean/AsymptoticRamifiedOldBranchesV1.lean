module

public import AsymptoticFrickeCosetsV1
public import AsymptoticDecodedRamifiedKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceLabels

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticFreshMatrices AsymptoticFreshCRT AsymptoticReconstructionBranch
open AsymptoticIntegralSubgroup

/-- Fricke converts the lower-level transvections into translations
with denominator q, in the actual projective label group. -/
theorem fricke_lower_div (M q : ℕ) (hM : 0<M) (hq : 0<q) (j : ℤ) :
    frickeLabel (q*M) (Nat.mul_pos hq hM)*integralLabel (lowerSL M j)=
      translationLabel (-(j:ℚ)/q)*frickeLabel (q*M) (Nat.mul_pos hq hM) := by
  have hq' : (q:ℚ)≠0 := by exact_mod_cast hq.ne'
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branch ((q*M:ℕ):ℚ) 0 0 _)*rationalMap (rationalGL (lowerSL M j))=
    rationalMap (AsymptoticMobiusFold.translation (-(j:ℚ)/q))*rationalMap (branch ((q*M:ℕ):ℚ) 0 0 _)
  rw [← map_mul,← map_mul]
  congr 1
  apply Units.ext
  change (branch ((q*M:ℕ):ℚ) 0 0 _).val*(lower M j).map (fun z : ℤ => (z:ℚ))=
    (AsymptoticMobiusFold.translation (-(j:ℚ)/q)).val*(branch ((q*M:ℕ):ℚ) 0 0 _).val
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [branch,lower,AsymptoticMobiusFold.translation,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]
  field_simp

#print axioms fricke_lower_div

end AsymptoticCongruenceLabels

namespace AsymptoticRamifiedCosets

open AsymptoticCongruenceLabels AsymptoticFreshMatrices AsymptoticIntegralSubgroup

theorem frickeRepresentative_inv (M q : ℕ) (hM : 0<M) (hq : 0<q) (j : Fin q) :
    (frickeRepresentative M q hM hq j).val⁻¹=translationLabel ((j.val:ℚ)/q) := by
  have he : (frickeRepresentative M q hM hq j).val⁻¹=
      frickeLabel (q*M) (Nat.mul_pos hq hM)*integralLabel (lowerSL M (-(j.val:ℤ)))*
        (frickeLabel (q*M) (Nat.mul_pos hq hM))⁻¹ := by
    simp only [frickeRepresentative,mul_inv_rev,inv_inv,← map_inv,lowerSL_inv,mul_assoc]
  rw [he,fricke_lower_div M q hM hq,mul_inv_cancel_right]
  simp

#print axioms frickeRepresentative_inv

end AsymptoticRamifiedCosets

namespace AsymptoticOrbitDecode

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticFreshMatrices AsymptoticCongruenceLabels AsymptoticIntegralSubgroup

theorem ramifiedLabel_mul_dilation (p : ℕ) (hp : 0<p) (a : Fin p) :
    ramifiedLabel p hp a*dilationLabel p hp=translationLabel ((a.val:ℚ)/p) := by
  have hp' : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
  have he : AsymptoticRamifiedBranch.branch (p:ℚ) (a.val:ℚ) hp'*dilationGL p hp=
      AsymptoticMobiusFold.translation ((a.val:ℚ)/p)*
        GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p:ℚ) hp') := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AsymptoticRamifiedBranch.branch,dilationGL,AsymptoticMobiusFold.translation,
        GeneralLinearGroup.scalar,Matrix.scalar,Matrix.natCast_apply,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two]
    field_simp
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (AsymptoticRamifiedBranch.branch (p:ℚ) (a.val:ℚ) hp')*
    rationalMap (dilationGL p hp)=rationalMap (AsymptoticMobiusFold.translation ((a.val:ℚ)/p))
  rw [← map_mul,he,map_mul,rationalMap_scalar,mul_one]

#print axioms ramifiedLabel_mul_dilation

end AsymptoticOrbitDecode
