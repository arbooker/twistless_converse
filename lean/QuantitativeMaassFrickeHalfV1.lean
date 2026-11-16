module

public import QuantitativeMaassAdmissibleNormalizerCoverV1
public import AsymptoticFrickeNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix UpperHalfPlane AsymptoticCongruenceLabels AsymptoticIntegralSubgroup
open AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticFreshMatrices
open AsymptoticReconstructionBranch AsymptoticFreshCRT
open scoped MatrixGroups

namespace QuantitativeMaass

/-- The lower normalizer used in the dyadic cusp reduction is a word in
Fricke and the inverse half-translation. -/
theorem fricke_lower_half (L : ℕ) (hL : 0<L) :
    frickeLabel (4*L) (by positivity)*integralLabel (lowerSL (2*L) 1)=
      translationLabel (-1/2)*frickeLabel (4*L) (by positivity) := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branch ((4*L:ℕ):ℚ) 0 0 _)*rationalMap (rationalGL (lowerSL (2*L) 1))=
    rationalMap (AsymptoticMobiusFold.translation (-1/2))*rationalMap (branch ((4*L:ℕ):ℚ) 0 0 _)
  rw [←map_mul,←map_mul]
  congr 1
  apply Units.ext
  change (branch ((4*L:ℕ):ℚ) 0 0 _).val*(lower (2*L) 1).map (fun z : ℤ => (z:ℚ))=
    (AsymptoticMobiusFold.translation (-1/2)).val*(branch ((4*L:ℕ):ℚ) 0 0 _).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower,branch,AsymptoticMobiusFold.translation,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem lowerHalf_mem_of_fricke_half (L : ℕ) (hL : 0<L)
    (S : Subgroup AsymptoticRationalGroup.Group)
    (hW : frickeLabel (4*L) (by positivity)∈S)
    (hT : translationLabel (1/2)∈S) : integralLabel (lowerSL (2*L) 1)∈S := by
  have ht : translationLabel (-1/2)∈S := by
    simpa only [translationLabel_inv,neg_div] using S.inv_mem hT
  have he := fricke_lower_half L hL
  have hh := congrArg (fun g => (frickeLabel (4*L) (by positivity))⁻¹*g) he
  simp only [←mul_assoc,inv_mul_cancel,one_mul] at hh
  rw [hh]
  exact S.mul_mem (S.mul_mem (S.inv_mem hW) ht) hW

/-- Absolute-value invariance under rational isometries is closed under
composition and inversion, so generator equations propagate to words. -/
def modulusStabilizer (f : ℍ → ℂ) : Subgroup AsymptoticRationalGroup.Group where
  carrier := {g | ∀ z,‖f (g • z)‖=‖f z‖}
  one_mem' := by intro z; rw [one_smul]
  mul_mem' := by intro g h hg hh z; rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg z
    have h := hg (g⁻¹ • z)
    rw [smul_inv_smul] at h
    exact h.symm

#print axioms fricke_lower_half
#print axioms lowerHalf_mem_of_fricke_half
#print axioms modulusStabilizer

end QuantitativeMaass
