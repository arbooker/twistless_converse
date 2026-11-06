module

public import AsymptoticFreshCanonicalReductionV1
public import AsymptoticPrimeMixingV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceLabels

open Matrix AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticFreshMatrices AsymptoticFreshCRT AsymptoticIntegralSubgroup
open AsymptoticReconstructionBranch
open scoped MatrixGroups

def rationalGL : SL(2,ℤ) →* GL (Fin 2) ℚ :=
  SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (Int.castRingHom ℚ))

theorem rationalGL_apply (γ : SL(2,ℤ)) (i j : Fin 2) :
    (rationalGL γ).val i j=(γ.val i j:ℚ) := rfl

theorem rationalGL_positive (γ : SL(2,ℤ)) : 0<(realMatrix (rationalGL γ)).det.val := by
  change 0<((γ.val).map (fun z : ℤ => (z:ℝ))).det
  rw [← Int.cast_det,γ.property]
  norm_num

/-- The integral congruence group in the same positive rational
projective group used by the regular orbit operators. -/
noncomputable def integralLabel : SL(2,ℤ) →* AsymptoticRationalGroup.Group where
  toFun γ := ofMatrix (rationalGL γ) (rationalGL_positive γ)
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact (map_one (rationalMap.comp rationalGL))
  map_mul' γ δ := by
    apply Subtype.ext
    apply Subtype.ext
    exact (map_mul (rationalMap.comp rationalGL) γ δ)

def upperSL (u : ℤ) : SL(2,ℤ) := ⟨upper u,by simp [upper]⟩
def lowerSL (N : ℕ) (u : ℤ) : SL(2,ℤ) := ⟨lower N u,by simp [lower]⟩

theorem upper_label (u : ℤ) : integralLabel (upperSL u)=translationLabel (u:ℚ) := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (rationalGL (upperSL u))=rationalMap (AsymptoticMobiusFold.translation (u:ℚ))
  congr 1
  apply Units.ext
  change (upper u).map (fun z : ℤ => (z:ℚ))=(AsymptoticMobiusFold.translation (u:ℚ)).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper,AsymptoticMobiusFold.translation,
      GeneralLinearGroup.mkOfDetNeZero]

theorem canonical_label (N q : ℕ) (a b c : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    integralLabel (canonical N q a b c h)=canonicalLabel N q a b c h := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (rationalGL (canonical N q a b c h))=rationalMap (canonicalGL N q a b c h)
  congr 1
  apply Units.ext
  rfl

/-- Conjugation by Fricke turns an integral translation into the
lower transvection used in the canonical matrix reduction. -/
theorem fricke_lower (N : ℕ) (hN : 0<N) (u : ℤ) :
    frickeLabel N hN*integralLabel (lowerSL N u)=translationLabel (-(u:ℚ))*frickeLabel N hN := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branch (N:ℚ) 0 0 _)*rationalMap (rationalGL (lowerSL N u))=
    rationalMap (AsymptoticMobiusFold.translation (-(u:ℚ)))*rationalMap (branch (N:ℚ) 0 0 _)
  rw [← map_mul,← map_mul]
  congr 1
  apply Units.ext
  change (branch (N:ℚ) 0 0 _).val * (lower N u).map (fun z : ℤ => (z:ℚ))=
    (AsymptoticMobiusFold.translation (-(u:ℚ))).val * (branch (N:ℚ) 0 0 _).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower,branch,AsymptoticMobiusFold.translation,
      GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem reduction_labels (N q : ℕ) (γ : SL(2,ℤ)) (a b c t u v : ℤ)
    (h : (q:ℤ)*c=(N:ℤ)*a*b+1)
    (he : lower N v * upper t * γ.val * upper u=canonicalEntries N q a b c) :
    integralLabel (lowerSL N v)*translationLabel (t:ℚ)*integralLabel γ*translationLabel (u:ℚ)=
      canonicalLabel N q a b c h := by
  have hh : lowerSL N v * upperSL t * γ * upperSL u=canonical N q a b c h :=
    Subtype.ext he
  have hl := congrArg integralLabel hh
  simpa only [map_mul,upper_label,canonical_label] using hl

#print axioms rationalGL_apply
#print axioms rationalGL_positive
#print axioms upper_label
#print axioms canonical_label
#print axioms fricke_lower
#print axioms reduction_labels

end AsymptoticCongruenceLabels
